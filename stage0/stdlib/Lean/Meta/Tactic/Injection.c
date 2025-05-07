// Lean compiler output
// Module: Lean.Meta.Tactic.Injection
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.Tactic.Clear Lean.Meta.Tactic.Subst Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Intro
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isConstructorApp_x27_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEqHEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isRawNatLit(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* l_Lean_Meta_heqToEq(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_SavedState_restore___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_saveState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_tryClear(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqOfHEq(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_getFVarIds(lean_object*);
lean_object* l_Lean_Meta_intro1Core(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_nat_dec_lt(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = l_Lean_instInhabitedExpr;
x_15 = lean_ctor_get(x_1, 3);
x_16 = lean_nat_add(x_15, x_5);
x_17 = lean_array_get(x_14, x_2, x_16);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = lean_infer_type(x_17, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_21 = l_Lean_Meta_isProp(x_19, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_29; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_29 = lean_unbox(x_22);
lean_dec(x_22);
if (x_29 == 0)
{
x_24 = x_4;
goto block_28;
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_4, x_30);
lean_dec(x_4);
x_24 = x_31;
goto block_28;
}
block_28:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_3, 2);
x_26 = lean_nat_add(x_5, x_25);
lean_dec(x_5);
x_4 = x_24;
x_5 = x_26;
x_10 = x_23;
goto _start;
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
else
{
uint8_t x_36; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_18);
if (x_36 == 0)
{
return x_18;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_18, 0);
x_38 = lean_ctor_get(x_18, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_18);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_ctor_get(x_1, 4);
x_11 = lean_unsigned_to_nat(1u);
lean_inc(x_10);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(x_1, x_2, x_12, x_9, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_getCtorNumPropFields___lam__0___boxed), 8, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_8, 2);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_9, x_7, x_11, x_2, x_3, x_4, x_5, x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_getCtorNumPropFields_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getCtorNumPropFields___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_getCtorNumPropFields___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_431; 
lean_inc(x_2);
lean_inc(x_1);
x_431 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; lean_object* x_433; 
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
lean_dec(x_431);
lean_inc(x_4);
lean_inc(x_3);
x_433 = l_Lean_FVarId_getDecl___redArg(x_3, x_4, x_6, x_7, x_432);
if (lean_obj_tag(x_433) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_480; 
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
lean_dec(x_433);
x_480 = lean_ctor_get(x_434, 3);
lean_inc(x_480);
lean_dec(x_434);
x_436 = x_480;
goto block_479;
block_479:
{
lean_object* x_437; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_437 = lean_whnf(x_436, x_4, x_5, x_6, x_7, x_435);
if (lean_obj_tag(x_437) == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; 
x_438 = lean_ctor_get(x_437, 0);
lean_inc(x_438);
x_439 = lean_ctor_get(x_437, 1);
lean_inc(x_439);
lean_dec(x_437);
lean_inc(x_3);
x_440 = l_Lean_Expr_fvar___override(x_3);
x_441 = lean_mk_string_unchecked("HEq", 3, 3);
x_442 = l_Lean_Name_mkStr1(x_441);
x_443 = lean_unsigned_to_nat(4u);
x_444 = l_Lean_Expr_isAppOfArity(x_438, x_442, x_443);
lean_dec(x_442);
if (x_444 == 0)
{
x_20 = x_438;
x_21 = x_440;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_439;
goto block_430;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
x_445 = l_Lean_Expr_appFn_x21(x_438);
x_446 = l_Lean_Expr_appFn_x21(x_445);
x_447 = l_Lean_Expr_appFn_x21(x_446);
x_448 = l_Lean_Expr_appArg_x21(x_447);
lean_dec(x_447);
x_449 = l_Lean_Expr_appArg_x21(x_445);
lean_dec(x_445);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_450 = l_Lean_Meta_isExprDefEq(x_448, x_449, x_4, x_5, x_6, x_7, x_439);
if (lean_obj_tag(x_450) == 0)
{
lean_object* x_451; uint8_t x_452; 
x_451 = lean_ctor_get(x_450, 0);
lean_inc(x_451);
x_452 = lean_unbox(x_451);
lean_dec(x_451);
if (x_452 == 0)
{
lean_object* x_453; 
lean_dec(x_446);
x_453 = lean_ctor_get(x_450, 1);
lean_inc(x_453);
lean_dec(x_450);
x_20 = x_438;
x_21 = x_440;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_453;
goto block_430;
}
else
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_454 = lean_ctor_get(x_450, 1);
lean_inc(x_454);
lean_dec(x_450);
x_455 = l_Lean_Expr_appArg_x21(x_446);
lean_dec(x_446);
x_456 = l_Lean_Expr_appArg_x21(x_438);
lean_dec(x_438);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_457 = l_Lean_Meta_mkEq(x_455, x_456, x_4, x_5, x_6, x_7, x_454);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_460 = l_Lean_Meta_mkEqOfHEq(x_440, x_444, x_4, x_5, x_6, x_7, x_459);
if (lean_obj_tag(x_460) == 0)
{
lean_object* x_461; lean_object* x_462; 
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_460, 1);
lean_inc(x_462);
lean_dec(x_460);
x_20 = x_458;
x_21 = x_461;
x_22 = x_4;
x_23 = x_5;
x_24 = x_6;
x_25 = x_7;
x_26 = x_462;
goto block_430;
}
else
{
uint8_t x_463; 
lean_dec(x_458);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_463 = !lean_is_exclusive(x_460);
if (x_463 == 0)
{
return x_460;
}
else
{
lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_464 = lean_ctor_get(x_460, 0);
x_465 = lean_ctor_get(x_460, 1);
lean_inc(x_465);
lean_inc(x_464);
lean_dec(x_460);
x_466 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_466, 0, x_464);
lean_ctor_set(x_466, 1, x_465);
return x_466;
}
}
}
else
{
uint8_t x_467; 
lean_dec(x_440);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_467 = !lean_is_exclusive(x_457);
if (x_467 == 0)
{
return x_457;
}
else
{
lean_object* x_468; lean_object* x_469; lean_object* x_470; 
x_468 = lean_ctor_get(x_457, 0);
x_469 = lean_ctor_get(x_457, 1);
lean_inc(x_469);
lean_inc(x_468);
lean_dec(x_457);
x_470 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
return x_470;
}
}
}
}
else
{
uint8_t x_471; 
lean_dec(x_446);
lean_dec(x_440);
lean_dec(x_438);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_471 = !lean_is_exclusive(x_450);
if (x_471 == 0)
{
return x_450;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; 
x_472 = lean_ctor_get(x_450, 0);
x_473 = lean_ctor_get(x_450, 1);
lean_inc(x_473);
lean_inc(x_472);
lean_dec(x_450);
x_474 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_474, 0, x_472);
lean_ctor_set(x_474, 1, x_473);
return x_474;
}
}
}
}
else
{
uint8_t x_475; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_475 = !lean_is_exclusive(x_437);
if (x_475 == 0)
{
return x_437;
}
else
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; 
x_476 = lean_ctor_get(x_437, 0);
x_477 = lean_ctor_get(x_437, 1);
lean_inc(x_477);
lean_inc(x_476);
lean_dec(x_437);
x_478 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_478, 0, x_476);
lean_ctor_set(x_478, 1, x_477);
return x_478;
}
}
}
}
else
{
uint8_t x_481; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_481 = !lean_is_exclusive(x_433);
if (x_481 == 0)
{
return x_433;
}
else
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_482 = lean_ctor_get(x_433, 0);
x_483 = lean_ctor_get(x_433, 1);
lean_inc(x_483);
lean_inc(x_482);
lean_dec(x_433);
x_484 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
return x_484;
}
}
}
else
{
uint8_t x_485; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_485 = !lean_is_exclusive(x_431);
if (x_485 == 0)
{
return x_431;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_431, 0);
x_487 = lean_ctor_get(x_431, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_431);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
block_19:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_14 = lean_mk_string_unchecked("equality of constructor applications expected", 45, 45);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = l_Lean_MessageData_ofFormat(x_15);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_17, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_18;
}
block_430:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_mk_string_unchecked("Eq", 2, 2);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Expr_isAppOfArity(x_20, x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
x_31 = lean_mk_string_unchecked("equality expected", 17, 17);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = l_Lean_MessageData_ofFormat(x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_34, x_22, x_23, x_24, x_25, x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
return x_35;
}
else
{
lean_object* x_36; 
lean_inc(x_1);
x_36 = l_Lean_MVarId_getType(x_1, x_22, x_23, x_24, x_25, x_26);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Expr_appFn_x21(x_20);
x_40 = l_Lean_Expr_appArg_x21(x_39);
lean_dec(x_39);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_41 = l_Lean_Meta_isConstructorApp_x27_x3f(x_40, x_22, x_23, x_24, x_25, x_38);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = l_Lean_Expr_appArg_x21(x_20);
lean_dec(x_20);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
x_45 = l_Lean_Meta_isConstructorApp_x27_x3f(x_44, x_22, x_23, x_24, x_25, x_43);
if (lean_obj_tag(x_45) == 0)
{
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_46; 
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_3);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_9 = x_22;
x_10 = x_23;
x_11 = x_24;
x_12 = x_25;
x_13 = x_46;
goto block_19;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_21);
lean_dec(x_3);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_9 = x_22;
x_10 = x_23;
x_11 = x_24;
x_12 = x_25;
x_13 = x_48;
goto block_19;
}
else
{
lean_object* x_49; uint8_t x_50; 
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
lean_dec(x_45);
x_50 = !lean_is_exclusive(x_42);
if (x_50 == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_47);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; lean_object* x_73; uint8_t x_74; uint64_t x_75; lean_object* x_76; uint64_t x_77; uint64_t x_78; uint64_t x_79; uint8_t x_80; uint64_t x_81; uint64_t x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; 
x_52 = lean_ctor_get(x_42, 0);
x_53 = lean_ctor_get(x_47, 0);
x_54 = lean_box(1);
x_55 = lean_ctor_get(x_22, 0);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_55, 0);
x_57 = lean_ctor_get_uint8(x_55, 1);
x_58 = lean_ctor_get_uint8(x_55, 2);
x_59 = lean_ctor_get_uint8(x_55, 3);
x_60 = lean_ctor_get_uint8(x_55, 4);
x_61 = lean_ctor_get_uint8(x_55, 5);
x_62 = lean_ctor_get_uint8(x_55, 6);
x_63 = lean_ctor_get_uint8(x_55, 7);
x_64 = lean_ctor_get_uint8(x_55, 8);
x_65 = lean_ctor_get_uint8(x_55, 10);
x_66 = lean_ctor_get_uint8(x_55, 11);
x_67 = lean_ctor_get_uint8(x_55, 12);
x_68 = lean_ctor_get_uint8(x_55, 13);
x_69 = lean_ctor_get_uint8(x_55, 14);
x_70 = lean_ctor_get_uint8(x_55, 15);
x_71 = lean_ctor_get_uint8(x_55, 16);
x_72 = lean_ctor_get_uint8(x_55, 17);
lean_dec(x_55);
x_73 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_73, 0, x_56);
lean_ctor_set_uint8(x_73, 1, x_57);
lean_ctor_set_uint8(x_73, 2, x_58);
lean_ctor_set_uint8(x_73, 3, x_59);
lean_ctor_set_uint8(x_73, 4, x_60);
lean_ctor_set_uint8(x_73, 5, x_61);
lean_ctor_set_uint8(x_73, 6, x_62);
lean_ctor_set_uint8(x_73, 7, x_63);
lean_ctor_set_uint8(x_73, 8, x_64);
x_74 = lean_unbox(x_54);
lean_ctor_set_uint8(x_73, 9, x_74);
lean_ctor_set_uint8(x_73, 10, x_65);
lean_ctor_set_uint8(x_73, 11, x_66);
lean_ctor_set_uint8(x_73, 12, x_67);
lean_ctor_set_uint8(x_73, 13, x_68);
lean_ctor_set_uint8(x_73, 14, x_69);
lean_ctor_set_uint8(x_73, 15, x_70);
lean_ctor_set_uint8(x_73, 16, x_71);
lean_ctor_set_uint8(x_73, 17, x_72);
x_75 = lean_ctor_get_uint64(x_22, sizeof(void*)*7);
x_76 = lean_unsigned_to_nat(2u);
x_77 = lean_uint64_of_nat(x_76);
x_78 = lean_uint64_shift_right(x_75, x_77);
x_79 = lean_uint64_shift_left(x_78, x_77);
x_80 = lean_unbox(x_54);
x_81 = l_Lean_Meta_TransparencyMode_toUInt64(x_80);
x_82 = lean_uint64_lor(x_79, x_81);
x_83 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 8);
x_84 = lean_ctor_get(x_22, 1);
lean_inc(x_84);
x_85 = lean_ctor_get(x_22, 2);
lean_inc(x_85);
x_86 = lean_ctor_get(x_22, 3);
lean_inc(x_86);
x_87 = lean_ctor_get(x_22, 4);
lean_inc(x_87);
x_88 = lean_ctor_get(x_22, 5);
lean_inc(x_88);
x_89 = lean_ctor_get(x_22, 6);
lean_inc(x_89);
x_90 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 9);
x_91 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 10);
x_92 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_92, 0, x_73);
lean_ctor_set(x_92, 1, x_84);
lean_ctor_set(x_92, 2, x_85);
lean_ctor_set(x_92, 3, x_86);
lean_ctor_set(x_92, 4, x_87);
lean_ctor_set(x_92, 5, x_88);
lean_ctor_set(x_92, 6, x_89);
lean_ctor_set_uint64(x_92, sizeof(void*)*7, x_82);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 8, x_83);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 9, x_90);
lean_ctor_set_uint8(x_92, sizeof(void*)*7 + 10, x_91);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_93 = l_Lean_Meta_mkNoConfusion(x_37, x_21, x_92, x_23, x_24, x_25, x_49);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_ctor_get(x_52, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_ctor_get(x_53, 0);
lean_inc(x_98);
lean_dec(x_53);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
lean_dec(x_98);
x_100 = lean_name_eq(x_97, x_99);
lean_dec(x_99);
lean_dec(x_97);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
lean_free_object(x_47);
lean_free_object(x_42);
lean_dec(x_52);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_101 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_94, x_23, x_95);
lean_dec(x_23);
x_102 = !lean_is_exclusive(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_101, 0);
lean_dec(x_103);
x_104 = lean_box(0);
lean_ctor_set(x_101, 0, x_104);
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_dec(x_101);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
}
else
{
lean_object* x_108; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_94);
x_108 = lean_infer_type(x_94, x_22, x_23, x_24, x_25, x_95);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_111 = l_Lean_Meta_whnfD(x_109, x_22, x_23, x_24, x_25, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
if (lean_obj_tag(x_112) == 7)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_free_object(x_47);
lean_free_object(x_42);
lean_dec(x_2);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
lean_inc(x_1);
x_115 = l_Lean_MVarId_getTag(x_1, x_22, x_23, x_24, x_25, x_113);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
x_118 = l_Lean_Expr_headBeta(x_114);
lean_inc(x_22);
x_119 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_118, x_116, x_22, x_23, x_24, x_25, x_117);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
lean_inc(x_120);
x_122 = l_Lean_Expr_app___override(x_94, x_120);
x_123 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_122, x_23, x_121);
x_124 = !lean_is_exclusive(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_123, 1);
x_126 = lean_ctor_get(x_123, 0);
lean_dec(x_126);
x_127 = l_Lean_Expr_mvarId_x21(x_120);
lean_dec(x_120);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_128 = l_Lean_MVarId_tryClear(x_127, x_3, x_22, x_23, x_24, x_25, x_125);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_52);
x_131 = l_Lean_Meta_getCtorNumPropFields(x_52, x_22, x_23, x_24, x_25, x_130);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_ctor_get(x_52, 4);
lean_inc(x_134);
lean_dec(x_52);
x_135 = lean_nat_sub(x_134, x_133);
lean_dec(x_133);
lean_dec(x_134);
lean_ctor_set_tag(x_123, 1);
lean_ctor_set(x_123, 1, x_135);
lean_ctor_set(x_123, 0, x_129);
lean_ctor_set(x_131, 0, x_123);
return x_131;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_136 = lean_ctor_get(x_131, 0);
x_137 = lean_ctor_get(x_131, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_131);
x_138 = lean_ctor_get(x_52, 4);
lean_inc(x_138);
lean_dec(x_52);
x_139 = lean_nat_sub(x_138, x_136);
lean_dec(x_136);
lean_dec(x_138);
lean_ctor_set_tag(x_123, 1);
lean_ctor_set(x_123, 1, x_139);
lean_ctor_set(x_123, 0, x_129);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_123);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_129);
lean_free_object(x_123);
lean_dec(x_52);
x_141 = !lean_is_exclusive(x_131);
if (x_141 == 0)
{
return x_131;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_131, 0);
x_143 = lean_ctor_get(x_131, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_131);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_free_object(x_123);
lean_dec(x_52);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_145 = !lean_is_exclusive(x_128);
if (x_145 == 0)
{
return x_128;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_128, 0);
x_147 = lean_ctor_get(x_128, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_128);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_123, 1);
lean_inc(x_149);
lean_dec(x_123);
x_150 = l_Lean_Expr_mvarId_x21(x_120);
lean_dec(x_120);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_151 = l_Lean_MVarId_tryClear(x_150, x_3, x_22, x_23, x_24, x_25, x_149);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
lean_inc(x_52);
x_154 = l_Lean_Meta_getCtorNumPropFields(x_52, x_22, x_23, x_24, x_25, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_155 = lean_ctor_get(x_154, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_154, 1);
lean_inc(x_156);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_157 = x_154;
} else {
 lean_dec_ref(x_154);
 x_157 = lean_box(0);
}
x_158 = lean_ctor_get(x_52, 4);
lean_inc(x_158);
lean_dec(x_52);
x_159 = lean_nat_sub(x_158, x_155);
lean_dec(x_155);
lean_dec(x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_152);
lean_ctor_set(x_160, 1, x_159);
if (lean_is_scalar(x_157)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_157;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_156);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_152);
lean_dec(x_52);
x_162 = lean_ctor_get(x_154, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_154, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_164 = x_154;
} else {
 lean_dec_ref(x_154);
 x_164 = lean_box(0);
}
if (lean_is_scalar(x_164)) {
 x_165 = lean_alloc_ctor(1, 2, 0);
} else {
 x_165 = x_164;
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_163);
return x_165;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_52);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_166 = lean_ctor_get(x_151, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_151, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_151)) {
 lean_ctor_release(x_151, 0);
 lean_ctor_release(x_151, 1);
 x_168 = x_151;
} else {
 lean_dec_ref(x_151);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
}
else
{
uint8_t x_170; 
lean_dec(x_114);
lean_dec(x_94);
lean_dec(x_52);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_170 = !lean_is_exclusive(x_115);
if (x_170 == 0)
{
return x_115;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_115, 0);
x_172 = lean_ctor_get(x_115, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_115);
x_173 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_173, 0, x_171);
lean_ctor_set(x_173, 1, x_172);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_112);
lean_dec(x_94);
lean_dec(x_52);
lean_dec(x_3);
x_174 = lean_ctor_get(x_111, 1);
lean_inc(x_174);
lean_dec(x_111);
x_175 = lean_mk_string_unchecked("ill-formed noConfusion auxiliary construction", 45, 45);
lean_ctor_set_tag(x_42, 3);
lean_ctor_set(x_42, 0, x_175);
x_176 = l_Lean_MessageData_ofFormat(x_42);
lean_ctor_set(x_47, 0, x_176);
x_177 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_47, x_22, x_23, x_24, x_25, x_174);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
return x_177;
}
}
else
{
uint8_t x_178; 
lean_dec(x_94);
lean_free_object(x_47);
lean_free_object(x_42);
lean_dec(x_52);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = !lean_is_exclusive(x_111);
if (x_178 == 0)
{
return x_111;
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_111, 0);
x_180 = lean_ctor_get(x_111, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_111);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_94);
lean_free_object(x_47);
lean_free_object(x_42);
lean_dec(x_52);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_108);
if (x_182 == 0)
{
return x_108;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_108, 0);
x_184 = lean_ctor_get(x_108, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_108);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
}
else
{
uint8_t x_186; 
lean_free_object(x_47);
lean_dec(x_53);
lean_free_object(x_42);
lean_dec(x_52);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_93);
if (x_186 == 0)
{
return x_93;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_93, 0);
x_188 = lean_ctor_get(x_93, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_93);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; uint8_t x_195; uint8_t x_196; uint8_t x_197; uint8_t x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; uint8_t x_203; uint8_t x_204; uint8_t x_205; uint8_t x_206; uint8_t x_207; uint8_t x_208; uint8_t x_209; uint8_t x_210; lean_object* x_211; uint8_t x_212; uint64_t x_213; lean_object* x_214; uint64_t x_215; uint64_t x_216; uint64_t x_217; uint8_t x_218; uint64_t x_219; uint64_t x_220; uint8_t x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; uint8_t x_229; lean_object* x_230; lean_object* x_231; 
x_190 = lean_ctor_get(x_42, 0);
x_191 = lean_ctor_get(x_47, 0);
lean_inc(x_191);
lean_dec(x_47);
x_192 = lean_box(1);
x_193 = lean_ctor_get(x_22, 0);
lean_inc(x_193);
x_194 = lean_ctor_get_uint8(x_193, 0);
x_195 = lean_ctor_get_uint8(x_193, 1);
x_196 = lean_ctor_get_uint8(x_193, 2);
x_197 = lean_ctor_get_uint8(x_193, 3);
x_198 = lean_ctor_get_uint8(x_193, 4);
x_199 = lean_ctor_get_uint8(x_193, 5);
x_200 = lean_ctor_get_uint8(x_193, 6);
x_201 = lean_ctor_get_uint8(x_193, 7);
x_202 = lean_ctor_get_uint8(x_193, 8);
x_203 = lean_ctor_get_uint8(x_193, 10);
x_204 = lean_ctor_get_uint8(x_193, 11);
x_205 = lean_ctor_get_uint8(x_193, 12);
x_206 = lean_ctor_get_uint8(x_193, 13);
x_207 = lean_ctor_get_uint8(x_193, 14);
x_208 = lean_ctor_get_uint8(x_193, 15);
x_209 = lean_ctor_get_uint8(x_193, 16);
x_210 = lean_ctor_get_uint8(x_193, 17);
lean_dec(x_193);
x_211 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_211, 0, x_194);
lean_ctor_set_uint8(x_211, 1, x_195);
lean_ctor_set_uint8(x_211, 2, x_196);
lean_ctor_set_uint8(x_211, 3, x_197);
lean_ctor_set_uint8(x_211, 4, x_198);
lean_ctor_set_uint8(x_211, 5, x_199);
lean_ctor_set_uint8(x_211, 6, x_200);
lean_ctor_set_uint8(x_211, 7, x_201);
lean_ctor_set_uint8(x_211, 8, x_202);
x_212 = lean_unbox(x_192);
lean_ctor_set_uint8(x_211, 9, x_212);
lean_ctor_set_uint8(x_211, 10, x_203);
lean_ctor_set_uint8(x_211, 11, x_204);
lean_ctor_set_uint8(x_211, 12, x_205);
lean_ctor_set_uint8(x_211, 13, x_206);
lean_ctor_set_uint8(x_211, 14, x_207);
lean_ctor_set_uint8(x_211, 15, x_208);
lean_ctor_set_uint8(x_211, 16, x_209);
lean_ctor_set_uint8(x_211, 17, x_210);
x_213 = lean_ctor_get_uint64(x_22, sizeof(void*)*7);
x_214 = lean_unsigned_to_nat(2u);
x_215 = lean_uint64_of_nat(x_214);
x_216 = lean_uint64_shift_right(x_213, x_215);
x_217 = lean_uint64_shift_left(x_216, x_215);
x_218 = lean_unbox(x_192);
x_219 = l_Lean_Meta_TransparencyMode_toUInt64(x_218);
x_220 = lean_uint64_lor(x_217, x_219);
x_221 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 8);
x_222 = lean_ctor_get(x_22, 1);
lean_inc(x_222);
x_223 = lean_ctor_get(x_22, 2);
lean_inc(x_223);
x_224 = lean_ctor_get(x_22, 3);
lean_inc(x_224);
x_225 = lean_ctor_get(x_22, 4);
lean_inc(x_225);
x_226 = lean_ctor_get(x_22, 5);
lean_inc(x_226);
x_227 = lean_ctor_get(x_22, 6);
lean_inc(x_227);
x_228 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 9);
x_229 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 10);
x_230 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_230, 0, x_211);
lean_ctor_set(x_230, 1, x_222);
lean_ctor_set(x_230, 2, x_223);
lean_ctor_set(x_230, 3, x_224);
lean_ctor_set(x_230, 4, x_225);
lean_ctor_set(x_230, 5, x_226);
lean_ctor_set(x_230, 6, x_227);
lean_ctor_set_uint64(x_230, sizeof(void*)*7, x_220);
lean_ctor_set_uint8(x_230, sizeof(void*)*7 + 8, x_221);
lean_ctor_set_uint8(x_230, sizeof(void*)*7 + 9, x_228);
lean_ctor_set_uint8(x_230, sizeof(void*)*7 + 10, x_229);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_231 = l_Lean_Meta_mkNoConfusion(x_37, x_21, x_230, x_23, x_24, x_25, x_49);
if (lean_obj_tag(x_231) == 0)
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_232 = lean_ctor_get(x_231, 0);
lean_inc(x_232);
x_233 = lean_ctor_get(x_231, 1);
lean_inc(x_233);
lean_dec(x_231);
x_234 = lean_ctor_get(x_190, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_234, 0);
lean_inc(x_235);
lean_dec(x_234);
x_236 = lean_ctor_get(x_191, 0);
lean_inc(x_236);
lean_dec(x_191);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
lean_dec(x_236);
x_238 = lean_name_eq(x_235, x_237);
lean_dec(x_237);
lean_dec(x_235);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_free_object(x_42);
lean_dec(x_190);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_239 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_232, x_23, x_233);
lean_dec(x_23);
x_240 = lean_ctor_get(x_239, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_239)) {
 lean_ctor_release(x_239, 0);
 lean_ctor_release(x_239, 1);
 x_241 = x_239;
} else {
 lean_dec_ref(x_239);
 x_241 = lean_box(0);
}
x_242 = lean_box(0);
if (lean_is_scalar(x_241)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_241;
}
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_240);
return x_243;
}
else
{
lean_object* x_244; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_232);
x_244 = lean_infer_type(x_232, x_22, x_23, x_24, x_25, x_233);
if (lean_obj_tag(x_244) == 0)
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_247 = l_Lean_Meta_whnfD(x_245, x_22, x_23, x_24, x_25, x_246);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
if (lean_obj_tag(x_248) == 7)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_free_object(x_42);
lean_dec(x_2);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 1);
lean_inc(x_250);
lean_dec(x_248);
lean_inc(x_1);
x_251 = l_Lean_MVarId_getTag(x_1, x_22, x_23, x_24, x_25, x_249);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_251, 1);
lean_inc(x_253);
lean_dec(x_251);
x_254 = l_Lean_Expr_headBeta(x_250);
lean_inc(x_22);
x_255 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_254, x_252, x_22, x_23, x_24, x_25, x_253);
x_256 = lean_ctor_get(x_255, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_255, 1);
lean_inc(x_257);
lean_dec(x_255);
lean_inc(x_256);
x_258 = l_Lean_Expr_app___override(x_232, x_256);
x_259 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_258, x_23, x_257);
x_260 = lean_ctor_get(x_259, 1);
lean_inc(x_260);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_261 = x_259;
} else {
 lean_dec_ref(x_259);
 x_261 = lean_box(0);
}
x_262 = l_Lean_Expr_mvarId_x21(x_256);
lean_dec(x_256);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_263 = l_Lean_MVarId_tryClear(x_262, x_3, x_22, x_23, x_24, x_25, x_260);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_190);
x_266 = l_Lean_Meta_getCtorNumPropFields(x_190, x_22, x_23, x_24, x_25, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = lean_ctor_get(x_190, 4);
lean_inc(x_270);
lean_dec(x_190);
x_271 = lean_nat_sub(x_270, x_267);
lean_dec(x_267);
lean_dec(x_270);
if (lean_is_scalar(x_261)) {
 x_272 = lean_alloc_ctor(1, 2, 0);
} else {
 x_272 = x_261;
 lean_ctor_set_tag(x_272, 1);
}
lean_ctor_set(x_272, 0, x_264);
lean_ctor_set(x_272, 1, x_271);
if (lean_is_scalar(x_269)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_269;
}
lean_ctor_set(x_273, 0, x_272);
lean_ctor_set(x_273, 1, x_268);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_264);
lean_dec(x_261);
lean_dec(x_190);
x_274 = lean_ctor_get(x_266, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_266, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_276 = x_266;
} else {
 lean_dec_ref(x_266);
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
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_261);
lean_dec(x_190);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_278 = lean_ctor_get(x_263, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_263, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_280 = x_263;
} else {
 lean_dec_ref(x_263);
 x_280 = lean_box(0);
}
if (lean_is_scalar(x_280)) {
 x_281 = lean_alloc_ctor(1, 2, 0);
} else {
 x_281 = x_280;
}
lean_ctor_set(x_281, 0, x_278);
lean_ctor_set(x_281, 1, x_279);
return x_281;
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_250);
lean_dec(x_232);
lean_dec(x_190);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_282 = lean_ctor_get(x_251, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_251, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_284 = x_251;
} else {
 lean_dec_ref(x_251);
 x_284 = lean_box(0);
}
if (lean_is_scalar(x_284)) {
 x_285 = lean_alloc_ctor(1, 2, 0);
} else {
 x_285 = x_284;
}
lean_ctor_set(x_285, 0, x_282);
lean_ctor_set(x_285, 1, x_283);
return x_285;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
lean_dec(x_248);
lean_dec(x_232);
lean_dec(x_190);
lean_dec(x_3);
x_286 = lean_ctor_get(x_247, 1);
lean_inc(x_286);
lean_dec(x_247);
x_287 = lean_mk_string_unchecked("ill-formed noConfusion auxiliary construction", 45, 45);
lean_ctor_set_tag(x_42, 3);
lean_ctor_set(x_42, 0, x_287);
x_288 = l_Lean_MessageData_ofFormat(x_42);
x_289 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_289, 0, x_288);
x_290 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_289, x_22, x_23, x_24, x_25, x_286);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
return x_290;
}
}
else
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_232);
lean_free_object(x_42);
lean_dec(x_190);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_291 = lean_ctor_get(x_247, 0);
lean_inc(x_291);
x_292 = lean_ctor_get(x_247, 1);
lean_inc(x_292);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_293 = x_247;
} else {
 lean_dec_ref(x_247);
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
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_232);
lean_free_object(x_42);
lean_dec(x_190);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_295 = lean_ctor_get(x_244, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_244, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_244)) {
 lean_ctor_release(x_244, 0);
 lean_ctor_release(x_244, 1);
 x_297 = x_244;
} else {
 lean_dec_ref(x_244);
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
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_191);
lean_free_object(x_42);
lean_dec(x_190);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_299 = lean_ctor_get(x_231, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_231, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_231)) {
 lean_ctor_release(x_231, 0);
 lean_ctor_release(x_231, 1);
 x_301 = x_231;
} else {
 lean_dec_ref(x_231);
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
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; uint8_t x_308; uint8_t x_309; uint8_t x_310; uint8_t x_311; uint8_t x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; uint8_t x_316; uint8_t x_317; uint8_t x_318; uint8_t x_319; uint8_t x_320; uint8_t x_321; uint8_t x_322; uint8_t x_323; uint8_t x_324; lean_object* x_325; uint8_t x_326; uint64_t x_327; lean_object* x_328; uint64_t x_329; uint64_t x_330; uint64_t x_331; uint8_t x_332; uint64_t x_333; uint64_t x_334; uint8_t x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; uint8_t x_342; uint8_t x_343; lean_object* x_344; lean_object* x_345; 
x_303 = lean_ctor_get(x_42, 0);
lean_inc(x_303);
lean_dec(x_42);
x_304 = lean_ctor_get(x_47, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_305 = x_47;
} else {
 lean_dec_ref(x_47);
 x_305 = lean_box(0);
}
x_306 = lean_box(1);
x_307 = lean_ctor_get(x_22, 0);
lean_inc(x_307);
x_308 = lean_ctor_get_uint8(x_307, 0);
x_309 = lean_ctor_get_uint8(x_307, 1);
x_310 = lean_ctor_get_uint8(x_307, 2);
x_311 = lean_ctor_get_uint8(x_307, 3);
x_312 = lean_ctor_get_uint8(x_307, 4);
x_313 = lean_ctor_get_uint8(x_307, 5);
x_314 = lean_ctor_get_uint8(x_307, 6);
x_315 = lean_ctor_get_uint8(x_307, 7);
x_316 = lean_ctor_get_uint8(x_307, 8);
x_317 = lean_ctor_get_uint8(x_307, 10);
x_318 = lean_ctor_get_uint8(x_307, 11);
x_319 = lean_ctor_get_uint8(x_307, 12);
x_320 = lean_ctor_get_uint8(x_307, 13);
x_321 = lean_ctor_get_uint8(x_307, 14);
x_322 = lean_ctor_get_uint8(x_307, 15);
x_323 = lean_ctor_get_uint8(x_307, 16);
x_324 = lean_ctor_get_uint8(x_307, 17);
lean_dec(x_307);
x_325 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_325, 0, x_308);
lean_ctor_set_uint8(x_325, 1, x_309);
lean_ctor_set_uint8(x_325, 2, x_310);
lean_ctor_set_uint8(x_325, 3, x_311);
lean_ctor_set_uint8(x_325, 4, x_312);
lean_ctor_set_uint8(x_325, 5, x_313);
lean_ctor_set_uint8(x_325, 6, x_314);
lean_ctor_set_uint8(x_325, 7, x_315);
lean_ctor_set_uint8(x_325, 8, x_316);
x_326 = lean_unbox(x_306);
lean_ctor_set_uint8(x_325, 9, x_326);
lean_ctor_set_uint8(x_325, 10, x_317);
lean_ctor_set_uint8(x_325, 11, x_318);
lean_ctor_set_uint8(x_325, 12, x_319);
lean_ctor_set_uint8(x_325, 13, x_320);
lean_ctor_set_uint8(x_325, 14, x_321);
lean_ctor_set_uint8(x_325, 15, x_322);
lean_ctor_set_uint8(x_325, 16, x_323);
lean_ctor_set_uint8(x_325, 17, x_324);
x_327 = lean_ctor_get_uint64(x_22, sizeof(void*)*7);
x_328 = lean_unsigned_to_nat(2u);
x_329 = lean_uint64_of_nat(x_328);
x_330 = lean_uint64_shift_right(x_327, x_329);
x_331 = lean_uint64_shift_left(x_330, x_329);
x_332 = lean_unbox(x_306);
x_333 = l_Lean_Meta_TransparencyMode_toUInt64(x_332);
x_334 = lean_uint64_lor(x_331, x_333);
x_335 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 8);
x_336 = lean_ctor_get(x_22, 1);
lean_inc(x_336);
x_337 = lean_ctor_get(x_22, 2);
lean_inc(x_337);
x_338 = lean_ctor_get(x_22, 3);
lean_inc(x_338);
x_339 = lean_ctor_get(x_22, 4);
lean_inc(x_339);
x_340 = lean_ctor_get(x_22, 5);
lean_inc(x_340);
x_341 = lean_ctor_get(x_22, 6);
lean_inc(x_341);
x_342 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 9);
x_343 = lean_ctor_get_uint8(x_22, sizeof(void*)*7 + 10);
x_344 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_344, 0, x_325);
lean_ctor_set(x_344, 1, x_336);
lean_ctor_set(x_344, 2, x_337);
lean_ctor_set(x_344, 3, x_338);
lean_ctor_set(x_344, 4, x_339);
lean_ctor_set(x_344, 5, x_340);
lean_ctor_set(x_344, 6, x_341);
lean_ctor_set_uint64(x_344, sizeof(void*)*7, x_334);
lean_ctor_set_uint8(x_344, sizeof(void*)*7 + 8, x_335);
lean_ctor_set_uint8(x_344, sizeof(void*)*7 + 9, x_342);
lean_ctor_set_uint8(x_344, sizeof(void*)*7 + 10, x_343);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_345 = l_Lean_Meta_mkNoConfusion(x_37, x_21, x_344, x_23, x_24, x_25, x_49);
if (lean_obj_tag(x_345) == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; 
x_346 = lean_ctor_get(x_345, 0);
lean_inc(x_346);
x_347 = lean_ctor_get(x_345, 1);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_ctor_get(x_303, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_348, 0);
lean_inc(x_349);
lean_dec(x_348);
x_350 = lean_ctor_get(x_304, 0);
lean_inc(x_350);
lean_dec(x_304);
x_351 = lean_ctor_get(x_350, 0);
lean_inc(x_351);
lean_dec(x_350);
x_352 = lean_name_eq(x_349, x_351);
lean_dec(x_351);
lean_dec(x_349);
if (x_352 == 0)
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; 
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
x_353 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_346, x_23, x_347);
lean_dec(x_23);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
if (lean_is_exclusive(x_353)) {
 lean_ctor_release(x_353, 0);
 lean_ctor_release(x_353, 1);
 x_355 = x_353;
} else {
 lean_dec_ref(x_353);
 x_355 = lean_box(0);
}
x_356 = lean_box(0);
if (lean_is_scalar(x_355)) {
 x_357 = lean_alloc_ctor(0, 2, 0);
} else {
 x_357 = x_355;
}
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_354);
return x_357;
}
else
{
lean_object* x_358; 
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_346);
x_358 = lean_infer_type(x_346, x_22, x_23, x_24, x_25, x_347);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_361 = l_Lean_Meta_whnfD(x_359, x_22, x_23, x_24, x_25, x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
if (lean_obj_tag(x_362) == 7)
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_305);
lean_dec(x_2);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = lean_ctor_get(x_362, 1);
lean_inc(x_364);
lean_dec(x_362);
lean_inc(x_1);
x_365 = l_Lean_MVarId_getTag(x_1, x_22, x_23, x_24, x_25, x_363);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Expr_headBeta(x_364);
lean_inc(x_22);
x_369 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_368, x_366, x_22, x_23, x_24, x_25, x_367);
x_370 = lean_ctor_get(x_369, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_369, 1);
lean_inc(x_371);
lean_dec(x_369);
lean_inc(x_370);
x_372 = l_Lean_Expr_app___override(x_346, x_370);
x_373 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_372, x_23, x_371);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_375 = x_373;
} else {
 lean_dec_ref(x_373);
 x_375 = lean_box(0);
}
x_376 = l_Lean_Expr_mvarId_x21(x_370);
lean_dec(x_370);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
x_377 = l_Lean_MVarId_tryClear(x_376, x_3, x_22, x_23, x_24, x_25, x_374);
if (lean_obj_tag(x_377) == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
lean_dec(x_377);
lean_inc(x_303);
x_380 = l_Lean_Meta_getCtorNumPropFields(x_303, x_22, x_23, x_24, x_25, x_379);
if (lean_obj_tag(x_380) == 0)
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_380, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_383 = x_380;
} else {
 lean_dec_ref(x_380);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_303, 4);
lean_inc(x_384);
lean_dec(x_303);
x_385 = lean_nat_sub(x_384, x_381);
lean_dec(x_381);
lean_dec(x_384);
if (lean_is_scalar(x_375)) {
 x_386 = lean_alloc_ctor(1, 2, 0);
} else {
 x_386 = x_375;
 lean_ctor_set_tag(x_386, 1);
}
lean_ctor_set(x_386, 0, x_378);
lean_ctor_set(x_386, 1, x_385);
if (lean_is_scalar(x_383)) {
 x_387 = lean_alloc_ctor(0, 2, 0);
} else {
 x_387 = x_383;
}
lean_ctor_set(x_387, 0, x_386);
lean_ctor_set(x_387, 1, x_382);
return x_387;
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_378);
lean_dec(x_375);
lean_dec(x_303);
x_388 = lean_ctor_get(x_380, 0);
lean_inc(x_388);
x_389 = lean_ctor_get(x_380, 1);
lean_inc(x_389);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_390 = x_380;
} else {
 lean_dec_ref(x_380);
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
lean_dec(x_375);
lean_dec(x_303);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_392 = lean_ctor_get(x_377, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_377, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_394 = x_377;
} else {
 lean_dec_ref(x_377);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_364);
lean_dec(x_346);
lean_dec(x_303);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_1);
x_396 = lean_ctor_get(x_365, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_365, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_398 = x_365;
} else {
 lean_dec_ref(x_365);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; 
lean_dec(x_362);
lean_dec(x_346);
lean_dec(x_303);
lean_dec(x_3);
x_400 = lean_ctor_get(x_361, 1);
lean_inc(x_400);
lean_dec(x_361);
x_401 = lean_mk_string_unchecked("ill-formed noConfusion auxiliary construction", 45, 45);
x_402 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_402, 0, x_401);
x_403 = l_Lean_MessageData_ofFormat(x_402);
if (lean_is_scalar(x_305)) {
 x_404 = lean_alloc_ctor(1, 1, 0);
} else {
 x_404 = x_305;
}
lean_ctor_set(x_404, 0, x_403);
x_405 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_404, x_22, x_23, x_24, x_25, x_400);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
return x_405;
}
}
else
{
lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_346);
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_406 = lean_ctor_get(x_361, 0);
lean_inc(x_406);
x_407 = lean_ctor_get(x_361, 1);
lean_inc(x_407);
if (lean_is_exclusive(x_361)) {
 lean_ctor_release(x_361, 0);
 lean_ctor_release(x_361, 1);
 x_408 = x_361;
} else {
 lean_dec_ref(x_361);
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
lean_dec(x_346);
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_410 = lean_ctor_get(x_358, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_358, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_412 = x_358;
} else {
 lean_dec_ref(x_358);
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
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
lean_dec(x_305);
lean_dec(x_304);
lean_dec(x_303);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_414 = lean_ctor_get(x_345, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_345, 1);
lean_inc(x_415);
if (lean_is_exclusive(x_345)) {
 lean_ctor_release(x_345, 0);
 lean_ctor_release(x_345, 1);
 x_416 = x_345;
} else {
 lean_dec_ref(x_345);
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
lean_dec(x_42);
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_418 = !lean_is_exclusive(x_45);
if (x_418 == 0)
{
return x_45;
}
else
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_419 = lean_ctor_get(x_45, 0);
x_420 = lean_ctor_get(x_45, 1);
lean_inc(x_420);
lean_inc(x_419);
lean_dec(x_45);
x_421 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_421, 0, x_419);
lean_ctor_set(x_421, 1, x_420);
return x_421;
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_37);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_422 = !lean_is_exclusive(x_41);
if (x_422 == 0)
{
return x_41;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_41, 0);
x_424 = lean_ctor_get(x_41, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_41);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_426 = !lean_is_exclusive(x_36);
if (x_426 == 0)
{
return x_36;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_36, 0);
x_428 = lean_ctor_get(x_36, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_36);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked("injection", 9, 9);
x_9 = l_Lean_Name_mkStr1(x_8);
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_injectionCore___lam__0), 8, 3);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_2);
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_injectionCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_2, x_11);
if (x_12 == 1)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_4);
lean_ctor_set(x_13, 2, x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_2, x_15);
lean_dec(x_2);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_17; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Meta_intro1Core(x_3, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = l_Lean_Meta_heqToEq(x_21, x_20, x_1, x_6, x_7, x_8, x_9, x_19);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_array_push(x_4, x_25);
x_2 = x_16;
x_3 = x_26;
x_4 = x_27;
x_10 = x_24;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
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
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_5, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_5, 1);
lean_inc(x_38);
lean_dec(x_5);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_39 = l_Lean_MVarId_intro(x_3, x_37, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_44 = l_Lean_Meta_heqToEq(x_43, x_42, x_1, x_6, x_7, x_8, x_9, x_41);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_array_push(x_4, x_47);
x_2 = x_16;
x_3 = x_48;
x_4 = x_49;
x_5 = x_38;
x_10 = x_46;
goto _start;
}
else
{
uint8_t x_51; 
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_44);
if (x_51 == 0)
{
return x_44;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_44, 0);
x_53 = lean_ctor_get(x_44, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_44);
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
lean_dec(x_38);
lean_dec(x_16);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_55 = !lean_is_exclusive(x_39);
if (x_55 == 0)
{
return x_39;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_39, 0);
x_57 = lean_ctor_get(x_39, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_39);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Meta_injectionIntro_go(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_10);
x_12 = l_Lean_Meta_injectionIntro_go(x_4, x_2, x_1, x_11, x_3, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injectionIntro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_injectionIntro(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_9 = l_Lean_Meta_injectionCore(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = lean_box(1);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Meta_injectionIntro(x_18, x_19, x_3, x_21, x_4, x_5, x_6, x_7, x_17);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_23 = !lean_is_exclusive(x_9);
if (x_23 == 0)
{
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_9, 0);
x_25 = lean_ctor_get(x_9, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_9);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injection___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_injection(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = l_Lean_Meta_saveState___redArg(x_3, x_4, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
lean_inc(x_5);
lean_inc(x_3);
x_10 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; uint8_t x_20; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
x_20 = l_Lean_Exception_isInterrupt(x_11);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Exception_isRuntime(x_11);
x_13 = x_21;
goto block_19;
}
else
{
x_13 = x_20;
goto block_19;
}
block_19:
{
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
lean_dec(x_10);
x_14 = l_Lean_Meta_SavedState_restore___redArg(x_8, x_3, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_8);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_12 = l_Lean_Meta_injection(x_1, x_2, x_3, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
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
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_13, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_13, 2);
lean_inc(x_23);
lean_dec(x_13);
x_24 = lean_array_to_list(x_22);
x_25 = l_List_appendTR(lean_box(0), x_24, x_4);
x_26 = l_Lean_FVarIdSet_insert(x_5, x_2);
lean_inc(x_21);
x_27 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go), 10, 5);
lean_closure_set(x_27, 0, x_6);
lean_closure_set(x_27, 1, x_25);
lean_closure_set(x_27, 2, x_21);
lean_closure_set(x_27, 3, x_23);
lean_closure_set(x_27, 4, x_26);
x_28 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_21, x_27, x_7, x_8, x_9, x_10, x_20);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_12);
if (x_29 == 0)
{
return x_12;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_12, 0);
x_31 = lean_ctor_get(x_12, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_12);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_1, x_11);
if (x_12 == 1)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("injections", 10, 10);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("recursion depth exceeded", 24, 24);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_throwTacticEx___redArg(x_14, x_3, x_18, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_19;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_32; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_1, x_24);
lean_dec(x_1);
x_26 = lean_nat_add(x_25, x_24);
x_32 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_5, x_22);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; 
lean_inc(x_6);
lean_inc(x_22);
x_33 = l_Lean_FVarId_getType___redArg(x_22, x_6, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_36 = l_Lean_Meta_matchEqHEq_x3f(x_34, x_6, x_7, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
lean_dec(x_25);
lean_dec(x_22);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_1 = x_26;
x_2 = x_23;
x_10 = x_38;
goto _start;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = lean_whnf(x_43, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_48 = lean_whnf(x_44, x_6, x_7, x_8, x_9, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_60; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_5);
lean_inc(x_23);
lean_inc(x_4);
lean_inc(x_3);
x_51 = lean_alloc_closure((void*)(l_Lean_Meta_injections_go___lam__0___boxed), 11, 6);
lean_closure_set(x_51, 0, x_3);
lean_closure_set(x_51, 1, x_22);
lean_closure_set(x_51, 2, x_4);
lean_closure_set(x_51, 3, x_23);
lean_closure_set(x_51, 4, x_5);
lean_closure_set(x_51, 5, x_25);
x_60 = l_Lean_Expr_isRawNatLit(x_46);
lean_dec(x_46);
if (x_60 == 0)
{
lean_dec(x_49);
x_52 = x_60;
goto block_59;
}
else
{
uint8_t x_61; 
x_61 = l_Lean_Expr_isRawNatLit(x_49);
lean_dec(x_49);
x_52 = x_61;
goto block_59;
}
block_59:
{
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_53 = l_Lean_commitIfNoEx___at___Lean_Meta_injections_go_spec__0___redArg(x_51, x_6, x_7, x_8, x_9, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
x_56 = l_Lean_Exception_isInterrupt(x_54);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = l_Lean_Exception_isRuntime(x_54);
lean_dec(x_54);
x_27 = x_55;
x_28 = x_53;
x_29 = x_57;
goto block_31;
}
else
{
lean_dec(x_54);
x_27 = x_55;
x_28 = x_53;
x_29 = x_56;
goto block_31;
}
}
}
else
{
lean_dec(x_51);
x_1 = x_26;
x_2 = x_23;
x_10 = x_50;
goto _start;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_46);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_62 = !lean_is_exclusive(x_48);
if (x_62 == 0)
{
return x_48;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_48, 0);
x_64 = lean_ctor_get(x_48, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_48);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_44);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_66 = !lean_is_exclusive(x_45);
if (x_66 == 0)
{
return x_45;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_45, 0);
x_68 = lean_ctor_get(x_45, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_45);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_70 = !lean_is_exclusive(x_36);
if (x_70 == 0)
{
return x_36;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_36, 0);
x_72 = lean_ctor_get(x_36, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_36);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_33);
if (x_74 == 0)
{
return x_33;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_33, 0);
x_76 = lean_ctor_get(x_33, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_33);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_dec(x_32);
lean_dec(x_25);
lean_dec(x_22);
x_1 = x_26;
x_2 = x_23;
goto _start;
}
block_31:
{
if (x_29 == 0)
{
lean_dec(x_28);
x_1 = x_26;
x_2 = x_23;
x_10 = x_27;
goto _start;
}
else
{
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_injections_go___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_5, 2);
lean_inc(x_10);
x_11 = l_Lean_LocalContext_getFVarIds(x_10);
lean_dec(x_10);
x_12 = lean_array_to_list(x_11);
x_13 = l_Lean_Meta_injections_go(x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
lean_inc(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_injections___lam__0), 9, 4);
lean_closure_set(x_10, 0, x_3);
lean_closure_set(x_10, 1, x_1);
lean_closure_set(x_10, 2, x_2);
lean_closure_set(x_10, 3, x_4);
x_11 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_injections___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_injections(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Clear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Subst(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Intro(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Injection(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Clear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Subst(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Intro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
