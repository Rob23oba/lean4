// Lean compiler output
// Module: Lean.Meta.Tactic.UnifyEq
// Imports: Lean.Meta.Tactic.Injection
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
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__13(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_substCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_mkAdd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MVarId_clear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f_substEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_isConstructorApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isHEq(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkArrow(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_toExpr(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_18; lean_object* x_45; 
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
x_18 = x_45;
goto block_44;
block_17:
{
lean_object* x_13; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l_Lean_MVarId_assert(x_1, x_12, x_11, x_10, x_3, x_4, x_5, x_6, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_MVarId_clear(x_14, x_8, x_3, x_4, x_5, x_6, x_15);
lean_dec(x_3);
return x_16;
}
else
{
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
block_44:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
lean_inc(x_18);
x_19 = l_Lean_Expr_fvar___override(x_18);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_mkEqOfHEq(x_19, x_21, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_23);
x_25 = lean_infer_type(x_23, x_3, x_4, x_5, x_6, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = lean_whnf(x_26, x_3, x_4, x_5, x_6, x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_dec(x_2);
x_8 = x_18;
x_9 = x_30;
x_10 = x_23;
x_11 = x_29;
x_12 = x_31;
goto block_17;
}
else
{
uint8_t x_32; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
else
{
uint8_t x_36; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_25);
if (x_36 == 0)
{
return x_25;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_25, 0);
x_38 = lean_ctor_get(x_25, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_25);
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
lean_dec(x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_22);
if (x_40 == 0)
{
return x_22;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_22, 0);
x_42 = lean_ctor_get(x_22, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_22);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_evalNat(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_isOffset_x3f(x_1, x_2, x_3, x_4, x_5, x_9);
return x_10;
}
else
{
uint8_t x_11; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_7);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = !lean_is_exclusive(x_8);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_mkNatLit(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
lean_ctor_set(x_8, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_unsigned_to_nat(0u);
x_20 = l_Lean_mkNatLit(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 x_25 = x_8;
} else {
 lean_dec_ref(x_8);
 x_25 = lean_box(0);
}
x_26 = lean_unsigned_to_nat(0u);
x_27 = l_Lean_mkNatLit(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_24);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_23);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f_substEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(1);
x_15 = lean_box(x_8);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_substCore___boxed), 11, 6);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_2);
lean_closure_set(x_16, 2, x_15);
lean_closure_set(x_16, 3, x_3);
lean_closure_set(x_16, 4, x_14);
lean_closure_set(x_16, 5, x_14);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_17 = l_Lean_observing_x3f___at___Lean_Meta_substVar_x3f_spec__0(lean_box(0), x_16, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_20 = l_Lean_Meta_isExprDefEq(x_6, x_7, x_9, x_10, x_11, x_12, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Expr_fvar___override(x_2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_25 = lean_apply_7(x_4, x_1, x_24, x_9, x_10, x_11, x_12, x_23);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_39; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_mk_string_unchecked("dependent elimination failed, failed to solve equation", 54, 54);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_39 = lean_ctor_get(x_5, 3);
lean_inc(x_39);
lean_dec(x_5);
x_31 = x_39;
goto block_38;
block_38:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = l_Lean_indentExpr(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("", 0, 0);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_36, x_9, x_10, x_11, x_12, x_28);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_37;
}
}
else
{
uint8_t x_40; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_25);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_25, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_25, 0, x_42);
return x_25;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_dec(x_25);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
x_46 = !lean_is_exclusive(x_25);
if (x_46 == 0)
{
return x_25;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_25, 0);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_25);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_5);
lean_dec(x_4);
x_50 = lean_ctor_get(x_20, 1);
lean_inc(x_50);
lean_dec(x_20);
x_51 = l_Lean_MVarId_clear(x_1, x_2, x_9, x_10, x_11, x_12, x_50);
lean_dec(x_9);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_3);
lean_ctor_set(x_55, 2, x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_57 = lean_ctor_get(x_51, 0);
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_51);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_3);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_58);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_3);
x_63 = !lean_is_exclusive(x_51);
if (x_63 == 0)
{
return x_51;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_51);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_20);
if (x_67 == 0)
{
return x_20;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_20, 0);
x_69 = lean_ctor_get(x_20, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_20);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_18);
if (x_71 == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_17);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_18, 0);
x_74 = lean_ctor_get(x_17, 0);
lean_dec(x_74);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_73, 1);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_75);
lean_ctor_set(x_78, 2, x_77);
lean_ctor_set(x_18, 0, x_78);
return x_17;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_18, 0);
x_80 = lean_ctor_get(x_17, 1);
lean_inc(x_80);
lean_dec(x_17);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_83 = lean_unsigned_to_nat(0u);
x_84 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_81);
lean_ctor_set(x_84, 2, x_83);
lean_ctor_set(x_18, 0, x_84);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_18);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_ctor_get(x_18, 0);
lean_inc(x_86);
lean_dec(x_18);
x_87 = lean_ctor_get(x_17, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_88 = x_17;
} else {
 lean_dec_ref(x_17);
 x_88 = lean_box(0);
}
x_89 = lean_ctor_get(x_86, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_dec(x_86);
x_91 = lean_unsigned_to_nat(0u);
x_92 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_91);
x_93 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_93, 0, x_92);
if (lean_is_scalar(x_88)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_88;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_87);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_17);
if (x_95 == 0)
{
return x_17;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_17, 0);
x_97 = lean_ctor_get(x_17, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_17);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f_substEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lean_Meta_unifyEq_x3f_substEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f_injection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_82; lean_object* x_140; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_140 = lean_apply_7(x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_7);
x_143 = l_Lean_Meta_isConstructorApp(x_7, x_9, x_10, x_11, x_12, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; uint8_t x_145; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
x_82 = x_143;
goto block_139;
}
else
{
lean_object* x_146; lean_object* x_147; 
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
x_147 = l_Lean_Meta_isConstructorApp(x_8, x_9, x_10, x_11, x_12, x_146);
x_82 = x_147;
goto block_139;
}
}
else
{
x_82 = x_143;
goto block_139;
}
}
else
{
uint8_t x_148; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_140);
if (x_148 == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_140, 0);
lean_dec(x_149);
x_150 = !lean_is_exclusive(x_141);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_141, 0);
x_152 = lean_unsigned_to_nat(1u);
x_153 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_3);
lean_ctor_set(x_153, 2, x_152);
lean_ctor_set(x_141, 0, x_153);
return x_140;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_154 = lean_ctor_get(x_141, 0);
lean_inc(x_154);
lean_dec(x_141);
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_3);
lean_ctor_set(x_156, 2, x_155);
x_157 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_140, 0, x_157);
return x_140;
}
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_158 = lean_ctor_get(x_140, 1);
lean_inc(x_158);
lean_dec(x_140);
x_159 = lean_ctor_get(x_141, 0);
lean_inc(x_159);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 x_160 = x_141;
} else {
 lean_dec_ref(x_141);
 x_160 = lean_box(0);
}
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_3);
lean_ctor_set(x_162, 2, x_161);
if (lean_is_scalar(x_160)) {
 x_163 = lean_alloc_ctor(1, 1, 0);
} else {
 x_163 = x_160;
}
lean_ctor_set(x_163, 0, x_162);
x_164 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_158);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_140);
if (x_165 == 0)
{
return x_140;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_140, 0);
x_167 = lean_ctor_get(x_140, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_140);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
block_41:
{
lean_object* x_18; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_18 = l_Lean_MVarId_assert(x_1, x_17, x_16, x_14, x_9, x_10, x_11, x_12, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_MVarId_clear(x_19, x_2, x_9, x_10, x_11, x_12, x_20);
lean_dec(x_9);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_3);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_21, 0);
x_28 = lean_ctor_get(x_21, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_21);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_3);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_3);
x_33 = !lean_is_exclusive(x_21);
if (x_33 == 0)
{
return x_21;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_21, 0);
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_21);
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
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_18);
if (x_37 == 0)
{
return x_18;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_18, 0);
x_39 = lean_ctor_get(x_18, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_18);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
block_54:
{
lean_object* x_45; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_45 = l_Lean_Meta_mkEq(x_42, x_43, x_9, x_10, x_11, x_12, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_2);
x_48 = l_Lean_Expr_fvar___override(x_2);
x_49 = lean_ctor_get(x_5, 2);
lean_inc(x_49);
lean_dec(x_5);
x_14 = x_48;
x_15 = x_47;
x_16 = x_46;
x_17 = x_49;
goto block_41;
}
else
{
uint8_t x_50; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_45);
if (x_50 == 0)
{
return x_45;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_45, 0);
x_52 = lean_ctor_get(x_45, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_45);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
block_64:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = l_Lean_indentExpr(x_57);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_55);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_mk_string_unchecked("", 0, 0);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_62, x_9, x_10, x_11, x_12, x_56);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_63;
}
block_81:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_70 = l_Lean_indentExpr(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_67);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_mk_string_unchecked("\nat case ", 9, 9);
x_73 = l_Lean_stringToMessageData(x_72);
lean_dec(x_72);
x_74 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
x_75 = l_Lean_MessageData_ofConstName(x_66, x_68);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("", 0, 0);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_79, x_9, x_10, x_11, x_12, x_65);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_80;
}
block_139:
{
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; 
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_7);
x_86 = lean_whnf(x_7, x_9, x_10, x_11, x_12, x_85);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_89 = lean_whnf(x_8, x_9, x_10, x_11, x_12, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_expr_eqv(x_87, x_7);
lean_dec(x_7);
if (x_92 == 0)
{
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_4);
x_42 = x_87;
x_43 = x_90;
x_44 = x_91;
goto block_54;
}
else
{
uint8_t x_93; 
x_93 = lean_expr_eqv(x_90, x_8);
lean_dec(x_8);
if (x_93 == 0)
{
lean_dec(x_83);
lean_dec(x_4);
x_42 = x_87;
x_43 = x_90;
x_44 = x_91;
goto block_54;
}
else
{
lean_dec(x_90);
lean_dec(x_87);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_83);
x_94 = lean_mk_string_unchecked("dependent elimination failed, failed to solve equation", 54, 54);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_ctor_get(x_5, 3);
lean_inc(x_96);
lean_dec(x_5);
x_55 = x_95;
x_56 = x_91;
x_57 = x_96;
goto block_64;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_97 = lean_ctor_get(x_4, 0);
lean_inc(x_97);
lean_dec(x_4);
x_98 = lean_mk_string_unchecked("dependent elimination failed, failed to solve equation", 54, 54);
x_99 = l_Lean_stringToMessageData(x_98);
lean_dec(x_98);
x_100 = lean_ctor_get(x_5, 3);
lean_inc(x_100);
lean_dec(x_5);
x_101 = lean_unbox(x_83);
lean_dec(x_83);
x_65 = x_91;
x_66 = x_97;
x_67 = x_99;
x_68 = x_101;
x_69 = x_100;
goto block_81;
}
}
}
}
else
{
uint8_t x_102; 
lean_dec(x_87);
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_102 = !lean_is_exclusive(x_89);
if (x_102 == 0)
{
return x_89;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_89, 0);
x_104 = lean_ctor_get(x_89, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_89);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_83);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_86);
if (x_106 == 0)
{
return x_86;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_86, 0);
x_108 = lean_ctor_get(x_86, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_86);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_110 = lean_ctor_get(x_82, 1);
lean_inc(x_110);
lean_dec(x_82);
x_111 = l_Lean_Meta_injectionCore(x_1, x_2, x_9, x_10, x_11, x_12, x_110);
lean_dec(x_9);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
lean_dec(x_3);
x_113 = !lean_is_exclusive(x_111);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_ctor_get(x_111, 0);
lean_dec(x_114);
x_115 = lean_box(0);
lean_ctor_set(x_111, 0, x_115);
return x_111;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_111, 1);
lean_inc(x_116);
lean_dec(x_111);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_116);
return x_118;
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_111);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_120 = lean_ctor_get(x_111, 0);
lean_dec(x_120);
x_121 = lean_ctor_get(x_112, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_112, 1);
lean_inc(x_122);
lean_dec(x_112);
x_123 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_3);
lean_ctor_set(x_123, 2, x_122);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_111, 0, x_124);
return x_111;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_125 = lean_ctor_get(x_111, 1);
lean_inc(x_125);
lean_dec(x_111);
x_126 = lean_ctor_get(x_112, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_112, 1);
lean_inc(x_127);
lean_dec(x_112);
x_128 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_3);
lean_ctor_set(x_128, 2, x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
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
uint8_t x_131; 
lean_dec(x_3);
x_131 = !lean_is_exclusive(x_111);
if (x_131 == 0)
{
return x_111;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_111, 0);
x_133 = lean_ctor_get(x_111, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_111);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_135 = !lean_is_exclusive(x_82);
if (x_135 == 0)
{
return x_82;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_82, 0);
x_137 = lean_ctor_get(x_82, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_82);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_118; uint8_t x_119; 
x_118 = lean_st_ref_get(x_9, x_10);
x_119 = !lean_is_exclusive(x_118);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_120 = lean_ctor_get(x_118, 0);
x_121 = lean_ctor_get(x_118, 1);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_mk_string_unchecked("Nat", 3, 3);
x_124 = lean_mk_string_unchecked("elimOffset", 10, 10);
x_125 = l_Lean_Name_mkStr2(x_123, x_124);
x_126 = l_Lean_Environment_contains(x_122, x_125, x_1);
if (x_126 == 0)
{
lean_object* x_127; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_127 = lean_box(0);
lean_ctor_set(x_118, 0, x_127);
return x_118;
}
else
{
lean_object* x_128; 
lean_free_object(x_118);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_128 = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(x_4, x_6, x_7, x_8, x_9, x_121);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_130 = !lean_is_exclusive(x_128);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 0);
lean_dec(x_131);
x_132 = lean_box(0);
lean_ctor_set(x_128, 0, x_132);
return x_128;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_128, 1);
lean_inc(x_133);
lean_dec(x_128);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_133);
return x_135;
}
}
else
{
lean_object* x_136; uint8_t x_137; 
x_136 = lean_ctor_get(x_129, 0);
lean_inc(x_136);
lean_dec(x_129);
x_137 = !lean_is_exclusive(x_128);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_128, 1);
x_139 = lean_ctor_get(x_128, 0);
lean_dec(x_139);
x_140 = lean_ctor_get(x_136, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_142 = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(x_5, x_6, x_7, x_8, x_9, x_138);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_145 = x_142;
} else {
 lean_dec_ref(x_142);
 x_145 = lean_box(0);
}
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_149; 
lean_dec(x_145);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_149 = lean_box(0);
lean_ctor_set(x_128, 1, x_144);
lean_ctor_set(x_128, 0, x_149);
return x_128;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_free_object(x_128);
x_150 = lean_ctor_get(x_143, 0);
lean_inc(x_150);
lean_dec(x_143);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_unsigned_to_nat(0u);
x_154 = lean_nat_dec_eq(x_141, x_153);
if (x_154 == 0)
{
uint8_t x_155; 
x_155 = lean_nat_dec_eq(x_152, x_153);
if (x_155 == 0)
{
uint8_t x_156; 
lean_dec(x_145);
x_156 = lean_nat_dec_lt(x_141, x_152);
if (x_156 == 0)
{
uint8_t x_157; 
x_157 = lean_nat_dec_eq(x_141, x_152);
if (x_157 == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_nat_sub(x_141, x_152);
lean_dec(x_141);
x_159 = l_Lean_mkNatLit(x_158);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_160 = l_Lean_Meta_mkAdd(x_140, x_159, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_31 = x_161;
x_32 = x_151;
x_33 = x_152;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_162;
goto block_117;
}
else
{
uint8_t x_163; 
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_163 = !lean_is_exclusive(x_160);
if (x_163 == 0)
{
return x_160;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_160, 0);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_160);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_dec(x_152);
x_31 = x_140;
x_32 = x_151;
x_33 = x_141;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_144;
goto block_117;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = lean_nat_sub(x_152, x_141);
lean_dec(x_152);
x_168 = l_Lean_mkNatLit(x_167);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_169 = l_Lean_Meta_mkAdd(x_151, x_168, x_6, x_7, x_8, x_9, x_144);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
lean_dec(x_169);
x_31 = x_140;
x_32 = x_170;
x_33 = x_141;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_171;
goto block_117;
}
else
{
uint8_t x_172; 
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_172 = !lean_is_exclusive(x_169);
if (x_172 == 0)
{
return x_169;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_169, 0);
x_174 = lean_ctor_get(x_169, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_169);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
}
else
{
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
goto block_148;
}
}
else
{
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_141);
lean_dec(x_140);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
goto block_148;
}
}
block_148:
{
lean_object* x_146; lean_object* x_147; 
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
else
{
uint8_t x_176; 
lean_dec(x_141);
lean_dec(x_140);
lean_free_object(x_128);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_176 = !lean_is_exclusive(x_142);
if (x_176 == 0)
{
return x_142;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_177 = lean_ctor_get(x_142, 0);
x_178 = lean_ctor_get(x_142, 1);
lean_inc(x_178);
lean_inc(x_177);
lean_dec(x_142);
x_179 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_179, 0, x_177);
lean_ctor_set(x_179, 1, x_178);
return x_179;
}
}
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_180 = lean_ctor_get(x_128, 1);
lean_inc(x_180);
lean_dec(x_128);
x_181 = lean_ctor_get(x_136, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_136, 1);
lean_inc(x_182);
lean_dec(x_136);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_183 = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(x_5, x_6, x_7, x_8, x_9, x_180);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_190; lean_object* x_191; 
lean_dec(x_186);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_190 = lean_box(0);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_185);
return x_191;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
x_192 = lean_ctor_get(x_184, 0);
lean_inc(x_192);
lean_dec(x_184);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_unsigned_to_nat(0u);
x_196 = lean_nat_dec_eq(x_182, x_195);
if (x_196 == 0)
{
uint8_t x_197; 
x_197 = lean_nat_dec_eq(x_194, x_195);
if (x_197 == 0)
{
uint8_t x_198; 
lean_dec(x_186);
x_198 = lean_nat_dec_lt(x_182, x_194);
if (x_198 == 0)
{
uint8_t x_199; 
x_199 = lean_nat_dec_eq(x_182, x_194);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_200 = lean_nat_sub(x_182, x_194);
lean_dec(x_182);
x_201 = l_Lean_mkNatLit(x_200);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_202 = l_Lean_Meta_mkAdd(x_181, x_201, x_6, x_7, x_8, x_9, x_185);
if (lean_obj_tag(x_202) == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
x_31 = x_203;
x_32 = x_193;
x_33 = x_194;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_204;
goto block_117;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_202, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_202, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_202)) {
 lean_ctor_release(x_202, 0);
 lean_ctor_release(x_202, 1);
 x_207 = x_202;
} else {
 lean_dec_ref(x_202);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_dec(x_194);
x_31 = x_181;
x_32 = x_193;
x_33 = x_182;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_185;
goto block_117;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_nat_sub(x_194, x_182);
lean_dec(x_194);
x_210 = l_Lean_mkNatLit(x_209);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_211 = l_Lean_Meta_mkAdd(x_193, x_210, x_6, x_7, x_8, x_9, x_185);
if (lean_obj_tag(x_211) == 0)
{
lean_object* x_212; lean_object* x_213; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
x_213 = lean_ctor_get(x_211, 1);
lean_inc(x_213);
lean_dec(x_211);
x_31 = x_181;
x_32 = x_212;
x_33 = x_182;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_213;
goto block_117;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_214 = lean_ctor_get(x_211, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_211, 1);
lean_inc(x_215);
if (lean_is_exclusive(x_211)) {
 lean_ctor_release(x_211, 0);
 lean_ctor_release(x_211, 1);
 x_216 = x_211;
} else {
 lean_dec_ref(x_211);
 x_216 = lean_box(0);
}
if (lean_is_scalar(x_216)) {
 x_217 = lean_alloc_ctor(1, 2, 0);
} else {
 x_217 = x_216;
}
lean_ctor_set(x_217, 0, x_214);
lean_ctor_set(x_217, 1, x_215);
return x_217;
}
}
}
else
{
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
goto block_189;
}
}
else
{
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
goto block_189;
}
}
block_189:
{
lean_object* x_187; lean_object* x_188; 
x_187 = lean_box(0);
if (lean_is_scalar(x_186)) {
 x_188 = lean_alloc_ctor(0, 2, 0);
} else {
 x_188 = x_186;
}
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_185);
return x_188;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_218 = lean_ctor_get(x_183, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_183, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_220 = x_183;
} else {
 lean_dec_ref(x_183);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
}
}
else
{
uint8_t x_222; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_222 = !lean_is_exclusive(x_128);
if (x_222 == 0)
{
return x_128;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_128, 0);
x_224 = lean_ctor_get(x_128, 1);
lean_inc(x_224);
lean_inc(x_223);
lean_dec(x_128);
x_225 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_225, 0, x_223);
lean_ctor_set(x_225, 1, x_224);
return x_225;
}
}
}
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; uint8_t x_232; 
x_226 = lean_ctor_get(x_118, 0);
x_227 = lean_ctor_get(x_118, 1);
lean_inc(x_227);
lean_inc(x_226);
lean_dec(x_118);
x_228 = lean_ctor_get(x_226, 0);
lean_inc(x_228);
lean_dec(x_226);
x_229 = lean_mk_string_unchecked("Nat", 3, 3);
x_230 = lean_mk_string_unchecked("elimOffset", 10, 10);
x_231 = l_Lean_Name_mkStr2(x_229, x_230);
x_232 = l_Lean_Environment_contains(x_228, x_231, x_1);
if (x_232 == 0)
{
lean_object* x_233; lean_object* x_234; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_233 = lean_box(0);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_227);
return x_234;
}
else
{
lean_object* x_235; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_235 = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(x_4, x_6, x_7, x_8, x_9, x_227);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
if (lean_obj_tag(x_236) == 0)
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_238 = x_235;
} else {
 lean_dec_ref(x_235);
 x_238 = lean_box(0);
}
x_239 = lean_box(0);
if (lean_is_scalar(x_238)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_238;
}
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_237);
return x_240;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_236, 0);
lean_inc(x_241);
lean_dec(x_236);
x_242 = lean_ctor_get(x_235, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_243 = x_235;
} else {
 lean_dec_ref(x_235);
 x_243 = lean_box(0);
}
x_244 = lean_ctor_get(x_241, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_241, 1);
lean_inc(x_245);
lean_dec(x_241);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_246 = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_toOffset_x3f(x_5, x_6, x_7, x_8, x_9, x_242);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_249 = x_246;
} else {
 lean_dec_ref(x_246);
 x_249 = lean_box(0);
}
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_253; lean_object* x_254; 
lean_dec(x_249);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_253 = lean_box(0);
if (lean_is_scalar(x_243)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_243;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_248);
return x_254;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; 
lean_dec(x_243);
x_255 = lean_ctor_get(x_247, 0);
lean_inc(x_255);
lean_dec(x_247);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
x_258 = lean_unsigned_to_nat(0u);
x_259 = lean_nat_dec_eq(x_245, x_258);
if (x_259 == 0)
{
uint8_t x_260; 
x_260 = lean_nat_dec_eq(x_257, x_258);
if (x_260 == 0)
{
uint8_t x_261; 
lean_dec(x_249);
x_261 = lean_nat_dec_lt(x_245, x_257);
if (x_261 == 0)
{
uint8_t x_262; 
x_262 = lean_nat_dec_eq(x_245, x_257);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_nat_sub(x_245, x_257);
lean_dec(x_245);
x_264 = l_Lean_mkNatLit(x_263);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_265 = l_Lean_Meta_mkAdd(x_244, x_264, x_6, x_7, x_8, x_9, x_248);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; 
x_266 = lean_ctor_get(x_265, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_265, 1);
lean_inc(x_267);
lean_dec(x_265);
x_31 = x_266;
x_32 = x_256;
x_33 = x_257;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_267;
goto block_117;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_268 = lean_ctor_get(x_265, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_265, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_265)) {
 lean_ctor_release(x_265, 0);
 lean_ctor_release(x_265, 1);
 x_270 = x_265;
} else {
 lean_dec_ref(x_265);
 x_270 = lean_box(0);
}
if (lean_is_scalar(x_270)) {
 x_271 = lean_alloc_ctor(1, 2, 0);
} else {
 x_271 = x_270;
}
lean_ctor_set(x_271, 0, x_268);
lean_ctor_set(x_271, 1, x_269);
return x_271;
}
}
else
{
lean_dec(x_257);
x_31 = x_244;
x_32 = x_256;
x_33 = x_245;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_248;
goto block_117;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_nat_sub(x_257, x_245);
lean_dec(x_257);
x_273 = l_Lean_mkNatLit(x_272);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_274 = l_Lean_Meta_mkAdd(x_256, x_273, x_6, x_7, x_8, x_9, x_248);
if (lean_obj_tag(x_274) == 0)
{
lean_object* x_275; lean_object* x_276; 
x_275 = lean_ctor_get(x_274, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_274, 1);
lean_inc(x_276);
lean_dec(x_274);
x_31 = x_244;
x_32 = x_275;
x_33 = x_245;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_276;
goto block_117;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_277 = lean_ctor_get(x_274, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_274, 1);
lean_inc(x_278);
if (lean_is_exclusive(x_274)) {
 lean_ctor_release(x_274, 0);
 lean_ctor_release(x_274, 1);
 x_279 = x_274;
} else {
 lean_dec_ref(x_274);
 x_279 = lean_box(0);
}
if (lean_is_scalar(x_279)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_279;
}
lean_ctor_set(x_280, 0, x_277);
lean_ctor_set(x_280, 1, x_278);
return x_280;
}
}
}
else
{
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
goto block_252;
}
}
else
{
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
goto block_252;
}
}
block_252:
{
lean_object* x_250; lean_object* x_251; 
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
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
lean_dec(x_245);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_281 = lean_ctor_get(x_246, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_246, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_283 = x_246;
} else {
 lean_dec_ref(x_246);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_285 = lean_ctor_get(x_235, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_235, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_287 = x_235;
} else {
 lean_dec_ref(x_235);
 x_287 = lean_box(0);
}
if (lean_is_scalar(x_287)) {
 x_288 = lean_alloc_ctor(1, 2, 0);
} else {
 x_288 = x_287;
}
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
block_30:
{
lean_object* x_18; 
x_18 = l_Lean_MVarId_tryClear(x_16, x_17, x_11, x_15, x_13, x_12, x_14);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_18);
if (x_26 == 0)
{
return x_18;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_18, 0);
x_28 = lean_ctor_get(x_18, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_18);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
block_117:
{
lean_object* x_39; 
lean_inc(x_2);
x_39 = l_Lean_MVarId_getType(x_2, x_34, x_35, x_36, x_37, x_38);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_40);
x_42 = l_Lean_Meta_getLevel(x_40, x_34, x_35, x_36, x_37, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_32);
lean_inc(x_31);
x_45 = l_Lean_Meta_mkEq(x_31, x_32, x_34, x_35, x_36, x_37, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_40);
x_48 = l_Lean_mkArrow(x_46, x_40, x_36, x_37, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_2);
x_51 = l_Lean_MVarId_getTag(x_2, x_34, x_35, x_36, x_37, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_34);
x_54 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_49, x_52, x_34, x_35, x_36, x_37, x_53);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = lean_ctor_get(x_54, 1);
x_58 = lean_mk_string_unchecked("Nat", 3, 3);
x_59 = lean_mk_string_unchecked("elimOffset", 10, 10);
x_60 = l_Lean_Name_mkStr2(x_58, x_59);
x_61 = lean_box(0);
lean_ctor_set_tag(x_54, 1);
lean_ctor_set(x_54, 1, x_61);
lean_ctor_set(x_54, 0, x_43);
x_62 = l_Lean_Expr_const___override(x_60, x_54);
x_63 = l_Lean_mkNatLit(x_33);
lean_inc(x_3);
x_64 = l_Lean_LocalDecl_toExpr(x_3);
x_65 = lean_unsigned_to_nat(6u);
x_66 = lean_mk_empty_array_with_capacity(x_65);
x_67 = lean_array_push(x_66, x_40);
x_68 = lean_array_push(x_67, x_31);
x_69 = lean_array_push(x_68, x_32);
x_70 = lean_array_push(x_69, x_63);
x_71 = lean_array_push(x_70, x_64);
lean_inc(x_56);
x_72 = lean_array_push(x_71, x_56);
x_73 = l_Lean_mkAppN(x_62, x_72);
lean_dec(x_72);
x_74 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_2, x_73, x_35, x_57);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_76 = l_Lean_Expr_mvarId_x21(x_56);
lean_dec(x_56);
x_77 = lean_ctor_get(x_3, 1);
lean_inc(x_77);
lean_dec(x_3);
x_11 = x_34;
x_12 = x_37;
x_13 = x_36;
x_14 = x_75;
x_15 = x_35;
x_16 = x_76;
x_17 = x_77;
goto block_30;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_78 = lean_ctor_get(x_54, 0);
x_79 = lean_ctor_get(x_54, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_54);
x_80 = lean_mk_string_unchecked("Nat", 3, 3);
x_81 = lean_mk_string_unchecked("elimOffset", 10, 10);
x_82 = l_Lean_Name_mkStr2(x_80, x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_43);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_Expr_const___override(x_82, x_84);
x_86 = l_Lean_mkNatLit(x_33);
lean_inc(x_3);
x_87 = l_Lean_LocalDecl_toExpr(x_3);
x_88 = lean_unsigned_to_nat(6u);
x_89 = lean_mk_empty_array_with_capacity(x_88);
x_90 = lean_array_push(x_89, x_40);
x_91 = lean_array_push(x_90, x_31);
x_92 = lean_array_push(x_91, x_32);
x_93 = lean_array_push(x_92, x_86);
x_94 = lean_array_push(x_93, x_87);
lean_inc(x_78);
x_95 = lean_array_push(x_94, x_78);
x_96 = l_Lean_mkAppN(x_85, x_95);
lean_dec(x_95);
x_97 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_2, x_96, x_35, x_79);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = l_Lean_Expr_mvarId_x21(x_78);
lean_dec(x_78);
x_100 = lean_ctor_get(x_3, 1);
lean_inc(x_100);
lean_dec(x_3);
x_11 = x_34;
x_12 = x_37;
x_13 = x_36;
x_14 = x_98;
x_15 = x_35;
x_16 = x_99;
x_17 = x_100;
goto block_30;
}
}
else
{
uint8_t x_101; 
lean_dec(x_49);
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
x_101 = !lean_is_exclusive(x_51);
if (x_101 == 0)
{
return x_51;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_51, 0);
x_103 = lean_ctor_get(x_51, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_51);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
uint8_t x_105; 
lean_dec(x_43);
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
x_105 = !lean_is_exclusive(x_45);
if (x_105 == 0)
{
return x_45;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_45, 0);
x_107 = lean_ctor_get(x_45, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_45);
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
lean_dec(x_40);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
x_109 = !lean_is_exclusive(x_42);
if (x_109 == 0)
{
return x_42;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_42, 0);
x_111 = lean_ctor_get(x_42, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_42);
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
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_3);
lean_dec(x_2);
x_113 = !lean_is_exclusive(x_39);
if (x_113 == 0)
{
return x_39;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_39, 0);
x_115 = lean_ctor_get(x_39, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_39);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
x_14 = l_Lean_Meta_isExprDefEq(x_7, x_8, x_9, x_10, x_11, x_12, x_13);
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
x_18 = l_Lean_Meta_unifyEq_x3f_injection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = l_Lean_MVarId_clear(x_1, x_2, x_9, x_10, x_11, x_12, x_19);
lean_dec(x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_3);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_24);
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
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_3);
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
}
else
{
uint8_t x_36; 
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
x_36 = !lean_is_exclusive(x_14);
if (x_36 == 0)
{
return x_14;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_14, 0);
x_38 = lean_ctor_get(x_14, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_14);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_bvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_mvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_sort___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_const___override(x_1, x_2);
x_15 = lean_apply_7(x_3, x_14, x_4, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_app___override(x_1, x_2);
x_15 = lean_apply_7(x_3, x_14, x_4, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_lam___override(x_1, x_2, x_3, x_4);
x_17 = lean_apply_7(x_5, x_16, x_6, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; 
x_16 = l_Lean_Expr_forallE___override(x_1, x_2, x_3, x_4);
x_17 = lean_apply_7(x_5, x_16, x_6, x_11, x_12, x_13, x_14, x_15);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
x_18 = lean_apply_7(x_6, x_17, x_7, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_lit___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_mdata___override(x_1, x_2);
x_15 = lean_apply_7(x_3, x_14, x_4, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_16 = lean_apply_7(x_4, x_15, x_5, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__13(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_FVarId_getDecl___redArg(x_1, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_29; lean_object* x_311; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_311 = lean_ctor_get(x_12, 3);
lean_inc(x_311);
x_29 = x_311;
goto block_310;
block_21:
{
uint8_t x_19; lean_object* x_20; 
x_19 = lean_nat_dec_lt(x_17, x_18);
lean_dec(x_18);
lean_dec(x_17);
x_20 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_15, x_16, x_19, x_6, x_7, x_8, x_9, x_14);
return x_20;
}
block_28:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_23, 0);
lean_inc(x_27);
lean_dec(x_23);
x_14 = x_22;
x_15 = x_24;
x_16 = x_25;
x_17 = x_26;
x_18 = x_27;
goto block_21;
}
block_310:
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isHEq(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_mk_string_unchecked("Eq", 2, 2);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_unsigned_to_nat(3u);
x_34 = l_Lean_Expr_isAppOfArity(x_29, x_32, x_33);
lean_dec(x_32);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_mk_string_unchecked("equality expected", 17, 17);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = l_Lean_indentExpr(x_29);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked("", 0, 0);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_41, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_43 = l_Lean_Expr_appFn_x21(x_29);
x_44 = l_Lean_Expr_appArg_x21(x_43);
lean_dec(x_43);
lean_inc(x_44);
x_45 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_44, x_7, x_13);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = l_Lean_Expr_appArg_x21(x_29);
lean_dec(x_29);
lean_inc(x_48);
x_49 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_48, x_7, x_47);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_box(x_34);
lean_inc(x_12);
lean_inc(x_2);
x_53 = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__0___boxed), 10, 3);
lean_closure_set(x_53, 0, x_52);
lean_closure_set(x_53, 1, x_2);
lean_closure_set(x_53, 2, x_12);
lean_inc(x_53);
lean_inc(x_12);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_54 = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__1), 13, 6);
lean_closure_set(x_54, 0, x_2);
lean_closure_set(x_54, 1, x_1);
lean_closure_set(x_54, 2, x_3);
lean_closure_set(x_54, 3, x_5);
lean_closure_set(x_54, 4, x_12);
lean_closure_set(x_54, 5, x_53);
switch (lean_obj_tag(x_46)) {
case 0:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_55; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_55 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_55;
}
case 6:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_56 = lean_ctor_get(x_46, 0);
lean_inc(x_56);
lean_dec(x_46);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_50, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_61 = l_Lean_Meta_unifyEq_x3f___lam__2(x_56, x_54, x_50, x_57, x_58, x_59, x_60, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
return x_61;
}
case 7:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_62 = lean_ctor_get(x_46, 0);
lean_inc(x_62);
lean_dec(x_46);
x_63 = lean_ctor_get(x_50, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_50, 2);
lean_inc(x_65);
x_66 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_67 = l_Lean_Meta_unifyEq_x3f___lam__2(x_62, x_54, x_50, x_63, x_64, x_65, x_66, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
return x_67;
}
default: 
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_68 = lean_ctor_get(x_46, 0);
lean_inc(x_68);
lean_dec(x_46);
x_69 = l_Lean_Expr_bvar___override(x_68);
x_70 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_69, x_50, x_6, x_7, x_8, x_9, x_51);
return x_70;
}
}
}
case 1:
{
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_5);
if (lean_obj_tag(x_50) == 1)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_46, 0);
lean_inc(x_71);
lean_dec(x_46);
x_72 = lean_ctor_get(x_50, 0);
lean_inc(x_72);
lean_dec(x_50);
lean_inc(x_6);
x_73 = l_Lean_FVarId_getDecl___redArg(x_71, x_6, x_8, x_9, x_51);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
lean_inc(x_6);
x_76 = l_Lean_FVarId_getDecl___redArg(x_72, x_6, x_8, x_9, x_75);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
lean_dec(x_74);
x_22 = x_78;
x_23 = x_77;
x_24 = x_44;
x_25 = x_48;
x_26 = x_79;
goto block_28;
}
else
{
uint8_t x_80; 
lean_dec(x_74);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_80 = !lean_is_exclusive(x_76);
if (x_80 == 0)
{
return x_76;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_76, 0);
x_82 = lean_ctor_get(x_76, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_76);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
else
{
uint8_t x_84; 
lean_dec(x_72);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_73);
if (x_84 == 0)
{
return x_73;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_73, 0);
x_86 = lean_ctor_get(x_73, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_73);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; 
lean_dec(x_50);
lean_dec(x_46);
x_88 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_30, x_6, x_7, x_8, x_9, x_51);
return x_88;
}
}
case 2:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_89; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_89 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_89;
}
case 6:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_46, 0);
lean_inc(x_90);
lean_dec(x_46);
x_91 = lean_ctor_get(x_50, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_50, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_50, 2);
lean_inc(x_93);
x_94 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_95 = l_Lean_Meta_unifyEq_x3f___lam__3(x_90, x_54, x_50, x_91, x_92, x_93, x_94, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
return x_95;
}
case 7:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_96 = lean_ctor_get(x_46, 0);
lean_inc(x_96);
lean_dec(x_46);
x_97 = lean_ctor_get(x_50, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_50, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_50, 2);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_101 = l_Lean_Meta_unifyEq_x3f___lam__3(x_96, x_54, x_50, x_97, x_98, x_99, x_100, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
return x_101;
}
default: 
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_102 = lean_ctor_get(x_46, 0);
lean_inc(x_102);
lean_dec(x_46);
x_103 = l_Lean_Expr_mvar___override(x_102);
x_104 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_103, x_50, x_6, x_7, x_8, x_9, x_51);
return x_104;
}
}
}
case 3:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_105; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_105 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_105;
}
case 6:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_106 = lean_ctor_get(x_46, 0);
lean_inc(x_106);
lean_dec(x_46);
x_107 = lean_ctor_get(x_50, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_50, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_50, 2);
lean_inc(x_109);
x_110 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_111 = l_Lean_Meta_unifyEq_x3f___lam__4(x_106, x_54, x_50, x_107, x_108, x_109, x_110, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
return x_111;
}
case 7:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_112 = lean_ctor_get(x_46, 0);
lean_inc(x_112);
lean_dec(x_46);
x_113 = lean_ctor_get(x_50, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_50, 1);
lean_inc(x_114);
x_115 = lean_ctor_get(x_50, 2);
lean_inc(x_115);
x_116 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_117 = l_Lean_Meta_unifyEq_x3f___lam__4(x_112, x_54, x_50, x_113, x_114, x_115, x_116, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
return x_117;
}
default: 
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_118 = lean_ctor_get(x_46, 0);
lean_inc(x_118);
lean_dec(x_46);
x_119 = l_Lean_Expr_sort___override(x_118);
x_120 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_119, x_50, x_6, x_7, x_8, x_9, x_51);
return x_120;
}
}
}
case 4:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_121; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_121 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_121;
}
case 6:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; lean_object* x_128; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = lean_ctor_get(x_46, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_46, 1);
lean_inc(x_123);
lean_dec(x_46);
x_124 = lean_ctor_get(x_50, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_50, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_50, 2);
lean_inc(x_126);
x_127 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_128 = l_Lean_Meta_unifyEq_x3f___lam__5(x_122, x_123, x_54, x_50, x_124, x_125, x_126, x_127, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
return x_128;
}
case 7:
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; lean_object* x_135; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = lean_ctor_get(x_46, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_46, 1);
lean_inc(x_130);
lean_dec(x_46);
x_131 = lean_ctor_get(x_50, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_50, 1);
lean_inc(x_132);
x_133 = lean_ctor_get(x_50, 2);
lean_inc(x_133);
x_134 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_135 = l_Lean_Meta_unifyEq_x3f___lam__5(x_129, x_130, x_54, x_50, x_131, x_132, x_133, x_134, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
return x_135;
}
default: 
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_136 = lean_ctor_get(x_46, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_46, 1);
lean_inc(x_137);
lean_dec(x_46);
x_138 = l_Lean_Expr_const___override(x_136, x_137);
x_139 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_138, x_50, x_6, x_7, x_8, x_9, x_51);
return x_139;
}
}
}
case 5:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_140; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_140 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_140;
}
case 6:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_141 = lean_ctor_get(x_46, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_46, 1);
lean_inc(x_142);
lean_dec(x_46);
x_143 = lean_ctor_get(x_50, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_50, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_50, 2);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_147 = l_Lean_Meta_unifyEq_x3f___lam__6(x_141, x_142, x_54, x_50, x_143, x_144, x_145, x_146, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_145);
lean_dec(x_144);
lean_dec(x_143);
return x_147;
}
case 7:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; lean_object* x_154; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = lean_ctor_get(x_46, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_46, 1);
lean_inc(x_149);
lean_dec(x_46);
x_150 = lean_ctor_get(x_50, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_50, 1);
lean_inc(x_151);
x_152 = lean_ctor_get(x_50, 2);
lean_inc(x_152);
x_153 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_154 = l_Lean_Meta_unifyEq_x3f___lam__6(x_148, x_149, x_54, x_50, x_150, x_151, x_152, x_153, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_150);
return x_154;
}
default: 
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_155 = lean_ctor_get(x_46, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_46, 1);
lean_inc(x_156);
lean_dec(x_46);
x_157 = l_Lean_Expr_app___override(x_155, x_156);
x_158 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_157, x_50, x_6, x_7, x_8, x_9, x_51);
return x_158;
}
}
}
case 6:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_159; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_159 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_159;
}
case 6:
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_160 = lean_ctor_get(x_46, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_46, 1);
lean_inc(x_161);
x_162 = lean_ctor_get(x_46, 2);
lean_inc(x_162);
x_163 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_164 = lean_ctor_get(x_50, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_50, 1);
lean_inc(x_165);
x_166 = lean_ctor_get(x_50, 2);
lean_inc(x_166);
x_167 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_168 = l_Lean_Meta_unifyEq_x3f___lam__7(x_160, x_161, x_162, x_163, x_54, x_50, x_164, x_165, x_166, x_167, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
return x_168;
}
case 7:
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; uint8_t x_176; lean_object* x_177; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_169 = lean_ctor_get(x_46, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_46, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_46, 2);
lean_inc(x_171);
x_172 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_173 = lean_ctor_get(x_50, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_50, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_50, 2);
lean_inc(x_175);
x_176 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_177 = l_Lean_Meta_unifyEq_x3f___lam__7(x_169, x_170, x_171, x_172, x_54, x_50, x_173, x_174, x_175, x_176, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_175);
lean_dec(x_174);
lean_dec(x_173);
return x_177;
}
default: 
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_178 = lean_ctor_get(x_46, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_46, 1);
lean_inc(x_179);
x_180 = lean_ctor_get(x_46, 2);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_182 = l_Lean_Expr_lam___override(x_178, x_179, x_180, x_181);
x_183 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_182, x_50, x_6, x_7, x_8, x_9, x_51);
return x_183;
}
}
}
case 7:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_184; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_184 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_184;
}
case 6:
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; lean_object* x_193; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_185 = lean_ctor_get(x_46, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_46, 1);
lean_inc(x_186);
x_187 = lean_ctor_get(x_46, 2);
lean_inc(x_187);
x_188 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_189 = lean_ctor_get(x_50, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_50, 1);
lean_inc(x_190);
x_191 = lean_ctor_get(x_50, 2);
lean_inc(x_191);
x_192 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_193 = l_Lean_Meta_unifyEq_x3f___lam__8(x_185, x_186, x_187, x_188, x_54, x_50, x_189, x_190, x_191, x_192, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_191);
lean_dec(x_190);
lean_dec(x_189);
return x_193;
}
case 7:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_194 = lean_ctor_get(x_46, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_46, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_46, 2);
lean_inc(x_196);
x_197 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_198 = lean_ctor_get(x_50, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_50, 1);
lean_inc(x_199);
x_200 = lean_ctor_get(x_50, 2);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_202 = l_Lean_Meta_unifyEq_x3f___lam__8(x_194, x_195, x_196, x_197, x_54, x_50, x_198, x_199, x_200, x_201, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_200);
lean_dec(x_199);
lean_dec(x_198);
return x_202;
}
default: 
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_203 = lean_ctor_get(x_46, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_46, 1);
lean_inc(x_204);
x_205 = lean_ctor_get(x_46, 2);
lean_inc(x_205);
x_206 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_207 = l_Lean_Expr_forallE___override(x_203, x_204, x_205, x_206);
x_208 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_207, x_50, x_6, x_7, x_8, x_9, x_51);
return x_208;
}
}
}
case 8:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_209; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_209 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_209;
}
case 6:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; lean_object* x_219; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_ctor_get(x_46, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_46, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_46, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_46, 3);
lean_inc(x_213);
x_214 = lean_ctor_get_uint8(x_46, sizeof(void*)*4 + 8);
lean_dec(x_46);
x_215 = lean_ctor_get(x_50, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_50, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_50, 2);
lean_inc(x_217);
x_218 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_219 = l_Lean_Meta_unifyEq_x3f___lam__9(x_210, x_211, x_212, x_213, x_214, x_54, x_50, x_215, x_216, x_217, x_218, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_215);
return x_219;
}
case 7:
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; lean_object* x_229; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_220 = lean_ctor_get(x_46, 0);
lean_inc(x_220);
x_221 = lean_ctor_get(x_46, 1);
lean_inc(x_221);
x_222 = lean_ctor_get(x_46, 2);
lean_inc(x_222);
x_223 = lean_ctor_get(x_46, 3);
lean_inc(x_223);
x_224 = lean_ctor_get_uint8(x_46, sizeof(void*)*4 + 8);
lean_dec(x_46);
x_225 = lean_ctor_get(x_50, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_50, 1);
lean_inc(x_226);
x_227 = lean_ctor_get(x_50, 2);
lean_inc(x_227);
x_228 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_229 = l_Lean_Meta_unifyEq_x3f___lam__9(x_220, x_221, x_222, x_223, x_224, x_54, x_50, x_225, x_226, x_227, x_228, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
return x_229;
}
default: 
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; uint8_t x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_230 = lean_ctor_get(x_46, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_46, 1);
lean_inc(x_231);
x_232 = lean_ctor_get(x_46, 2);
lean_inc(x_232);
x_233 = lean_ctor_get(x_46, 3);
lean_inc(x_233);
x_234 = lean_ctor_get_uint8(x_46, sizeof(void*)*4 + 8);
lean_dec(x_46);
x_235 = l_Lean_Expr_letE___override(x_230, x_231, x_232, x_233, x_234);
x_236 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_235, x_50, x_6, x_7, x_8, x_9, x_51);
return x_236;
}
}
}
case 9:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_237; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_237 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_237;
}
case 6:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_46, 0);
lean_inc(x_238);
lean_dec(x_46);
x_239 = lean_ctor_get(x_50, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_50, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_50, 2);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_243 = l_Lean_Meta_unifyEq_x3f___lam__10(x_238, x_54, x_50, x_239, x_240, x_241, x_242, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_241);
lean_dec(x_240);
lean_dec(x_239);
return x_243;
}
case 7:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_244 = lean_ctor_get(x_46, 0);
lean_inc(x_244);
lean_dec(x_46);
x_245 = lean_ctor_get(x_50, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_50, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_50, 2);
lean_inc(x_247);
x_248 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_249 = l_Lean_Meta_unifyEq_x3f___lam__10(x_244, x_54, x_50, x_245, x_246, x_247, x_248, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_247);
lean_dec(x_246);
lean_dec(x_245);
return x_249;
}
default: 
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_250 = lean_ctor_get(x_46, 0);
lean_inc(x_250);
lean_dec(x_46);
x_251 = l_Lean_Expr_lit___override(x_250);
x_252 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_251, x_50, x_6, x_7, x_8, x_9, x_51);
return x_252;
}
}
}
case 10:
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_253; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_253 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_253;
}
case 6:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; uint8_t x_259; lean_object* x_260; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_ctor_get(x_46, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_46, 1);
lean_inc(x_255);
lean_dec(x_46);
x_256 = lean_ctor_get(x_50, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_50, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_50, 2);
lean_inc(x_258);
x_259 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_260 = l_Lean_Meta_unifyEq_x3f___lam__11(x_254, x_255, x_54, x_50, x_256, x_257, x_258, x_259, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_258);
lean_dec(x_257);
lean_dec(x_256);
return x_260;
}
case 7:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; lean_object* x_267; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_261 = lean_ctor_get(x_46, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_46, 1);
lean_inc(x_262);
lean_dec(x_46);
x_263 = lean_ctor_get(x_50, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_50, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_50, 2);
lean_inc(x_265);
x_266 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_267 = l_Lean_Meta_unifyEq_x3f___lam__11(x_261, x_262, x_54, x_50, x_263, x_264, x_265, x_266, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_265);
lean_dec(x_264);
lean_dec(x_263);
return x_267;
}
default: 
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_268 = lean_ctor_get(x_46, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_46, 1);
lean_inc(x_269);
lean_dec(x_46);
x_270 = l_Lean_Expr_mdata___override(x_268, x_269);
x_271 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_270, x_50, x_6, x_7, x_8, x_9, x_51);
return x_271;
}
}
}
default: 
{
switch (lean_obj_tag(x_50)) {
case 1:
{
lean_object* x_272; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_46);
lean_dec(x_5);
x_272 = l_Lean_Meta_unifyEq_x3f_substEq(x_2, x_1, x_3, x_4, x_12, x_44, x_48, x_34, x_6, x_7, x_8, x_9, x_51);
return x_272;
}
case 6:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; uint8_t x_279; lean_object* x_280; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_273 = lean_ctor_get(x_46, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_46, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_46, 2);
lean_inc(x_275);
lean_dec(x_46);
x_276 = lean_ctor_get(x_50, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_50, 1);
lean_inc(x_277);
x_278 = lean_ctor_get(x_50, 2);
lean_inc(x_278);
x_279 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_280 = l_Lean_Meta_unifyEq_x3f___lam__12(x_273, x_274, x_275, x_54, x_50, x_276, x_277, x_278, x_279, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_278);
lean_dec(x_277);
lean_dec(x_276);
return x_280;
}
case 7:
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; uint8_t x_287; lean_object* x_288; 
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_281 = lean_ctor_get(x_46, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_46, 1);
lean_inc(x_282);
x_283 = lean_ctor_get(x_46, 2);
lean_inc(x_283);
lean_dec(x_46);
x_284 = lean_ctor_get(x_50, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_50, 1);
lean_inc(x_285);
x_286 = lean_ctor_get(x_50, 2);
lean_inc(x_286);
x_287 = lean_ctor_get_uint8(x_50, sizeof(void*)*3 + 8);
x_288 = l_Lean_Meta_unifyEq_x3f___lam__12(x_281, x_282, x_283, x_54, x_50, x_284, x_285, x_286, x_287, x_6, x_7, x_8, x_9, x_51);
lean_dec(x_286);
lean_dec(x_285);
lean_dec(x_284);
return x_288;
}
default: 
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_54);
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_4);
x_289 = lean_ctor_get(x_46, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_46, 1);
lean_inc(x_290);
x_291 = lean_ctor_get(x_46, 2);
lean_inc(x_291);
lean_dec(x_46);
x_292 = l_Lean_Expr_proj___override(x_289, x_290, x_291);
x_293 = l_Lean_Meta_unifyEq_x3f___lam__1(x_2, x_1, x_3, x_5, x_12, x_53, x_292, x_50, x_6, x_7, x_8, x_9, x_51);
return x_293;
}
}
}
}
}
}
else
{
lean_object* x_294; 
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_294 = l___private_Lean_Meta_Tactic_UnifyEq_0__Lean_Meta_heqToEq_x27(x_2, x_12, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_294) == 0)
{
uint8_t x_295; 
x_295 = !lean_is_exclusive(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_294, 0);
x_297 = lean_unsigned_to_nat(1u);
x_298 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_298, 0, x_296);
lean_ctor_set(x_298, 1, x_3);
lean_ctor_set(x_298, 2, x_297);
x_299 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_294, 0, x_299);
return x_294;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
x_300 = lean_ctor_get(x_294, 0);
x_301 = lean_ctor_get(x_294, 1);
lean_inc(x_301);
lean_inc(x_300);
lean_dec(x_294);
x_302 = lean_unsigned_to_nat(1u);
x_303 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_3);
lean_ctor_set(x_303, 2, x_302);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
x_305 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_305, 0, x_304);
lean_ctor_set(x_305, 1, x_301);
return x_305;
}
}
else
{
uint8_t x_306; 
lean_dec(x_3);
x_306 = !lean_is_exclusive(x_294);
if (x_306 == 0)
{
return x_294;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_307 = lean_ctor_get(x_294, 0);
x_308 = lean_ctor_get(x_294, 1);
lean_inc(x_308);
lean_inc(x_307);
lean_dec(x_294);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
return x_309;
}
}
}
}
}
else
{
uint8_t x_312; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_312 = !lean_is_exclusive(x_11);
if (x_312 == 0)
{
return x_11;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_ctor_get(x_11, 0);
x_314 = lean_ctor_get(x_11, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_11);
x_315 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_315, 0, x_313);
lean_ctor_set(x_315, 1, x_314);
return x_315;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_unifyEq_x3f___lam__13), 10, 5);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_1);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_5);
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_unifyEq_x3f___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_unifyEq_x3f___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_unifyEq_x3f___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_unifyEq_x3f___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lean_Meta_unifyEq_x3f___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lean_Meta_unifyEq_x3f___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_10);
lean_dec(x_10);
x_18 = l_Lean_Meta_unifyEq_x3f___lam__7(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_17, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_10);
lean_dec(x_10);
x_18 = l_Lean_Meta_unifyEq_x3f___lam__8(x_1, x_2, x_3, x_16, x_5, x_6, x_7, x_8, x_9, x_17, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_11);
lean_dec(x_11);
x_19 = l_Lean_Meta_unifyEq_x3f___lam__9(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_18, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l_Lean_Meta_unifyEq_x3f___lam__10(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l_Lean_Meta_unifyEq_x3f___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l_Lean_Meta_unifyEq_x3f___lam__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_unifyEq_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_unifyEq_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_UnifyEq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
