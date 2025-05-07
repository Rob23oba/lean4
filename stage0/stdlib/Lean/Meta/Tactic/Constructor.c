// Lean compiler output
// Module: Lean.Meta.Tactic.Constructor
// Imports: Lean.Meta.Check Lean.Meta.Tactic.Util Lean.Meta.Tactic.Apply
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
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MVarId_apply(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_checkApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_5);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
x_15 = lean_box(0);
lean_inc(x_1);
x_16 = l_Lean_Expr_const___override(x_13, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_MVarId_apply(x_2, x_16, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_15);
lean_ctor_set(x_4, 0, x_20);
lean_ctor_set(x_17, 0, x_4);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_15);
lean_ctor_set(x_4, 0, x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_33; 
x_25 = lean_ctor_get(x_17, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_27 = x_17;
} else {
 lean_dec_ref(x_17);
 x_27 = lean_box(0);
}
x_28 = lean_box(0);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_15);
lean_ctor_set(x_4, 0, x_28);
x_33 = l_Lean_Exception_isInterrupt(x_25);
if (x_33 == 0)
{
uint8_t x_34; 
x_34 = l_Lean_Exception_isRuntime(x_25);
x_29 = x_34;
goto block_32;
}
else
{
x_29 = x_33;
goto block_32;
}
block_32:
{
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_25);
{
lean_object* _tmp_3 = x_14;
lean_object* _tmp_4 = x_4;
lean_object* _tmp_9 = x_26;
x_4 = _tmp_3;
x_5 = _tmp_4;
x_10 = _tmp_9;
}
goto _start;
}
else
{
lean_object* x_31; 
lean_dec(x_4);
lean_dec(x_14);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_27)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_27;
}
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_4, 0);
x_36 = lean_ctor_get(x_4, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_4);
x_37 = lean_box(0);
lean_inc(x_1);
x_38 = l_Lean_Expr_const___override(x_35, x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_39 = l_Lean_MVarId_apply(x_2, x_38, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_37);
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
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_55; 
x_46 = lean_ctor_get(x_39, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_48 = x_39;
} else {
 lean_dec_ref(x_39);
 x_48 = lean_box(0);
}
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_37);
x_55 = l_Lean_Exception_isInterrupt(x_46);
if (x_55 == 0)
{
uint8_t x_56; 
x_56 = l_Lean_Exception_isRuntime(x_46);
x_51 = x_56;
goto block_54;
}
else
{
x_51 = x_55;
goto block_54;
}
block_54:
{
if (x_51 == 0)
{
lean_dec(x_48);
lean_dec(x_46);
x_4 = x_36;
x_5 = x_50;
x_10 = x_47;
goto _start;
}
else
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_48)) {
 x_53 = lean_alloc_ctor(1, 2, 0);
} else {
 x_53 = x_48;
}
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_mk_string_unchecked("target is not an inductive datatype", 35, 35);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_throwTacticEx___redArg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_2);
lean_inc(x_1);
x_10 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_12 = l_Lean_MVarId_getType_x27(x_1, x_5, x_6, x_7, x_8, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_Expr_getAppFn(x_13);
lean_dec(x_13);
if (lean_obj_tag(x_15) == 4)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_8, x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
x_25 = l_Lean_Environment_find_x3f(x_22, x_16, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_apply_6(x_3, x_26, x_5, x_6, x_7, x_8, x_21);
return x_27;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_25, 0);
if (lean_obj_tag(x_29) == 5)
{
uint8_t x_30; 
lean_dec(x_3);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_31, 4);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_box(0);
x_34 = lean_box(0);
lean_ctor_set(x_18, 1, x_34);
lean_ctor_set(x_18, 0, x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_35 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_17, x_1, x_4, x_32, x_18, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec(x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_dec(x_35);
x_39 = lean_mk_string_unchecked("no applicable constructor found", 31, 31);
lean_ctor_set_tag(x_29, 3);
lean_ctor_set(x_29, 0, x_39);
x_40 = l_Lean_MessageData_ofFormat(x_29);
lean_ctor_set(x_25, 0, x_40);
x_41 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_25, x_5, x_6, x_7, x_8, x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_41;
}
else
{
uint8_t x_42; 
lean_free_object(x_29);
lean_free_object(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_35);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_35, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_37, 0);
lean_inc(x_44);
lean_dec(x_37);
lean_ctor_set(x_35, 0, x_44);
return x_35;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_35, 1);
lean_inc(x_45);
lean_dec(x_35);
x_46 = lean_ctor_get(x_37, 0);
lean_inc(x_46);
lean_dec(x_37);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_29);
lean_free_object(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_35);
if (x_48 == 0)
{
return x_35;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_35, 0);
x_50 = lean_ctor_get(x_35, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_35);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_52 = lean_ctor_get(x_29, 0);
lean_inc(x_52);
lean_dec(x_29);
x_53 = lean_ctor_get(x_52, 4);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_box(0);
x_55 = lean_box(0);
lean_ctor_set(x_18, 1, x_55);
lean_ctor_set(x_18, 0, x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_56 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_17, x_1, x_4, x_53, x_18, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_56) == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
lean_dec(x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_59 = lean_ctor_get(x_56, 1);
lean_inc(x_59);
lean_dec(x_56);
x_60 = lean_mk_string_unchecked("no applicable constructor found", 31, 31);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_MessageData_ofFormat(x_61);
lean_ctor_set(x_25, 0, x_62);
x_63 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_25, x_5, x_6, x_7, x_8, x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_64 = lean_ctor_get(x_56, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_65 = x_56;
} else {
 lean_dec_ref(x_56);
 x_65 = lean_box(0);
}
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
lean_dec(x_58);
if (lean_is_scalar(x_65)) {
 x_67 = lean_alloc_ctor(0, 2, 0);
} else {
 x_67 = x_65;
}
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_64);
return x_67;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_free_object(x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_68 = lean_ctor_get(x_56, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_56, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_70 = x_56;
} else {
 lean_dec_ref(x_56);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; 
lean_free_object(x_25);
lean_dec(x_29);
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_72 = lean_box(0);
x_73 = lean_apply_6(x_3, x_72, x_5, x_6, x_7, x_8, x_21);
return x_73;
}
}
else
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_25, 0);
lean_inc(x_74);
lean_dec(x_25);
if (lean_obj_tag(x_74) == 5)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_3);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_75, 4);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_box(0);
x_79 = lean_box(0);
lean_ctor_set(x_18, 1, x_79);
lean_ctor_set(x_18, 0, x_78);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_80 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_17, x_1, x_4, x_77, x_18, x_5, x_6, x_7, x_8, x_21);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
x_84 = lean_mk_string_unchecked("no applicable constructor found", 31, 31);
if (lean_is_scalar(x_76)) {
 x_85 = lean_alloc_ctor(3, 1, 0);
} else {
 x_85 = x_76;
 lean_ctor_set_tag(x_85, 3);
}
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Lean_MessageData_ofFormat(x_85);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
x_88 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_87, x_5, x_6, x_7, x_8, x_83);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_89 = lean_ctor_get(x_80, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_90 = x_80;
} else {
 lean_dec_ref(x_80);
 x_90 = lean_box(0);
}
x_91 = lean_ctor_get(x_82, 0);
lean_inc(x_91);
lean_dec(x_82);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_76);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_93 = lean_ctor_get(x_80, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_80, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_80)) {
 lean_ctor_release(x_80, 0);
 lean_ctor_release(x_80, 1);
 x_95 = x_80;
} else {
 lean_dec_ref(x_80);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_74);
lean_free_object(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_97 = lean_box(0);
x_98 = lean_apply_6(x_3, x_97, x_5, x_6, x_7, x_8, x_21);
return x_98;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_99 = lean_ctor_get(x_18, 0);
x_100 = lean_ctor_get(x_18, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_18);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_box(0);
x_103 = lean_unbox(x_102);
x_104 = l_Lean_Environment_find_x3f(x_101, x_16, x_103);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_105 = lean_box(0);
x_106 = lean_apply_6(x_3, x_105, x_5, x_6, x_7, x_8, x_100);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_ctor_get(x_104, 0);
lean_inc(x_107);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 x_108 = x_104;
} else {
 lean_dec_ref(x_104);
 x_108 = lean_box(0);
}
if (lean_obj_tag(x_107) == 5)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_3);
x_109 = lean_ctor_get(x_107, 0);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_109, 4);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_box(0);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_115 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_17, x_1, x_4, x_111, x_114, x_5, x_6, x_7, x_8, x_100);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
lean_dec(x_116);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = lean_mk_string_unchecked("no applicable constructor found", 31, 31);
if (lean_is_scalar(x_110)) {
 x_120 = lean_alloc_ctor(3, 1, 0);
} else {
 x_120 = x_110;
 lean_ctor_set_tag(x_120, 3);
}
lean_ctor_set(x_120, 0, x_119);
x_121 = l_Lean_MessageData_ofFormat(x_120);
if (lean_is_scalar(x_108)) {
 x_122 = lean_alloc_ctor(1, 1, 0);
} else {
 x_122 = x_108;
}
lean_ctor_set(x_122, 0, x_121);
x_123 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_122, x_5, x_6, x_7, x_8, x_118);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_125 = x_115;
} else {
 lean_dec_ref(x_115);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_117, 0);
lean_inc(x_126);
lean_dec(x_117);
if (lean_is_scalar(x_125)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_125;
}
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_124);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_110);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_128 = lean_ctor_get(x_115, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_115, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_130 = x_115;
} else {
 lean_dec_ref(x_115);
 x_130 = lean_box(0);
}
if (lean_is_scalar(x_130)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_130;
}
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_132 = lean_box(0);
x_133 = lean_apply_6(x_3, x_132, x_5, x_6, x_7, x_8, x_100);
return x_133;
}
}
}
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_134 = lean_box(0);
x_135 = lean_apply_6(x_3, x_134, x_5, x_6, x_7, x_8, x_14);
return x_135;
}
}
else
{
uint8_t x_136; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_136 = !lean_is_exclusive(x_12);
if (x_136 == 0)
{
return x_12;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = lean_ctor_get(x_12, 0);
x_138 = lean_ctor_get(x_12, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_12);
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_137);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
}
}
else
{
uint8_t x_140; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_140 = !lean_is_exclusive(x_10);
if (x_140 == 0)
{
return x_10;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_10, 0);
x_142 = lean_ctor_get(x_10, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_10);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("constructor", 11, 11);
x_9 = l_Lean_Name_mkStr1(x_8);
lean_inc(x_1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_constructor___lam__0___boxed), 8, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_constructor___lam__1), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_2);
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___Lean_MVarId_constructor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_constructor___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_constructor___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_constructor(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_mk_string_unchecked("target is not an inductive datatype with one constructor", 56, 56);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Meta_throwTacticEx___redArg(x_1, x_2, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_29; 
lean_inc(x_2);
lean_inc(x_1);
x_29 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_31 = l_Lean_MVarId_getType_x27(x_1, x_5, x_6, x_7, x_8, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = l_Lean_Expr_getAppFn(x_32);
if (lean_obj_tag(x_34) == 4)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_8, x_33);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
x_43 = l_Lean_Environment_find_x3f(x_40, x_35, x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_apply_6(x_3, x_44, x_5, x_6, x_7, x_8, x_39);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_43);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_43, 0);
if (lean_obj_tag(x_47) == 5)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
lean_dec(x_47);
x_49 = lean_ctor_get(x_48, 4);
lean_inc(x_49);
lean_dec(x_48);
if (lean_obj_tag(x_49) == 0)
{
lean_free_object(x_43);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_39;
goto block_28;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_51, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; 
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
if (lean_obj_tag(x_53) == 6)
{
lean_object* x_54; uint8_t x_55; 
lean_dec(x_3);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = !lean_is_exclusive(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_56, 4);
lean_inc(x_57);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_nat_dec_lt(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_53);
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
lean_dec(x_60);
x_62 = l_Lean_Expr_const___override(x_61, x_36);
x_63 = lean_box(0);
x_64 = l_Lean_Expr_sort___override(x_63);
x_65 = l_Lean_Expr_getAppNumArgs(x_32);
lean_inc(x_65);
x_66 = lean_mk_array(x_65, x_64);
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_sub(x_65, x_67);
lean_dec(x_65);
x_69 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_32, x_66, x_68);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_ctor_get(x_56, 3);
lean_inc(x_71);
lean_dec(x_56);
x_72 = l_Array_toSubarray___redArg(x_69, x_70, x_71);
x_73 = l_Array_ofSubarray___redArg(x_72);
lean_dec(x_72);
x_74 = l_Lean_mkAppN(x_62, x_73);
lean_dec(x_73);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_74);
x_75 = lean_infer_type(x_74, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_nat_sub(x_57, x_58);
lean_dec(x_57);
lean_ctor_set(x_43, 0, x_78);
x_79 = lean_box(0);
x_80 = lean_unbox(x_79);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_81 = l_Lean_Meta_forallMetaTelescopeReducing(x_76, x_43, x_80, x_5, x_6, x_7, x_8, x_77);
lean_dec(x_43);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_mkAppN(x_74, x_84);
lean_dec(x_84);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_85);
x_86 = l_Lean_Meta_checkApp(x_85, x_4, x_5, x_6, x_7, x_8, x_83);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; uint8_t x_95; lean_object* x_96; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_88 = l_Lean_Expr_app___override(x_85, x_4);
x_89 = lean_box(0);
x_90 = lean_box(1);
x_91 = lean_alloc_ctor(0, 0, 4);
x_92 = lean_unbox(x_89);
lean_ctor_set_uint8(x_91, 0, x_92);
x_93 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, 1, x_93);
x_94 = lean_unbox(x_41);
lean_ctor_set_uint8(x_91, 2, x_94);
x_95 = lean_unbox(x_90);
lean_ctor_set_uint8(x_91, 3, x_95);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_96 = l_Lean_MVarId_apply(x_1, x_88, x_91, x_5, x_6, x_7, x_8, x_87);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_98;
goto block_20;
}
else
{
lean_object* x_99; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_obj_tag(x_99) == 0)
{
uint8_t x_100; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_100 = !lean_is_exclusive(x_96);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_ctor_get(x_96, 0);
lean_dec(x_101);
x_102 = lean_ctor_get(x_97, 0);
lean_inc(x_102);
lean_dec(x_97);
lean_ctor_set(x_96, 0, x_102);
return x_96;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_96, 1);
lean_inc(x_103);
lean_dec(x_96);
x_104 = lean_ctor_get(x_97, 0);
lean_inc(x_104);
lean_dec(x_97);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
lean_object* x_106; 
lean_dec(x_99);
lean_dec(x_97);
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
lean_dec(x_96);
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_106;
goto block_20;
}
}
}
else
{
uint8_t x_107; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_96);
if (x_107 == 0)
{
return x_96;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_96, 0);
x_109 = lean_ctor_get(x_96, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_96);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_85);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_86);
if (x_111 == 0)
{
return x_86;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_86, 0);
x_113 = lean_ctor_get(x_86, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_86);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
uint8_t x_115; 
lean_dec(x_74);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_81);
if (x_115 == 0)
{
return x_81;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_81, 0);
x_117 = lean_ctor_get(x_81, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_81);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_74);
lean_dec(x_57);
lean_free_object(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_75);
if (x_119 == 0)
{
return x_75;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_75, 0);
x_121 = lean_ctor_get(x_75, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_75);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
x_123 = lean_mk_string_unchecked("constructor must have at least two fields", 41, 41);
lean_ctor_set_tag(x_53, 3);
lean_ctor_set(x_53, 0, x_123);
x_124 = l_Lean_MessageData_ofFormat(x_53);
lean_ctor_set(x_43, 0, x_124);
x_125 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_43, x_5, x_6, x_7, x_8, x_54);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_130 = lean_ctor_get(x_53, 0);
lean_inc(x_130);
lean_dec(x_53);
x_131 = lean_ctor_get(x_130, 4);
lean_inc(x_131);
x_132 = lean_unsigned_to_nat(2u);
x_133 = lean_nat_dec_lt(x_131, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_134 = lean_ctor_get(x_130, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
lean_dec(x_134);
x_136 = l_Lean_Expr_const___override(x_135, x_36);
x_137 = lean_box(0);
x_138 = l_Lean_Expr_sort___override(x_137);
x_139 = l_Lean_Expr_getAppNumArgs(x_32);
lean_inc(x_139);
x_140 = lean_mk_array(x_139, x_138);
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_sub(x_139, x_141);
lean_dec(x_139);
x_143 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_32, x_140, x_142);
x_144 = lean_unsigned_to_nat(0u);
x_145 = lean_ctor_get(x_130, 3);
lean_inc(x_145);
lean_dec(x_130);
x_146 = l_Array_toSubarray___redArg(x_143, x_144, x_145);
x_147 = l_Array_ofSubarray___redArg(x_146);
lean_dec(x_146);
x_148 = l_Lean_mkAppN(x_136, x_147);
lean_dec(x_147);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_148);
x_149 = lean_infer_type(x_148, x_5, x_6, x_7, x_8, x_54);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_152 = lean_nat_sub(x_131, x_132);
lean_dec(x_131);
lean_ctor_set(x_43, 0, x_152);
x_153 = lean_box(0);
x_154 = lean_unbox(x_153);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_155 = l_Lean_Meta_forallMetaTelescopeReducing(x_150, x_43, x_154, x_5, x_6, x_7, x_8, x_151);
lean_dec(x_43);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_mkAppN(x_148, x_158);
lean_dec(x_158);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_159);
x_160 = l_Lean_Meta_checkApp(x_159, x_4, x_5, x_6, x_7, x_8, x_157);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; uint8_t x_167; uint8_t x_168; uint8_t x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
lean_dec(x_160);
x_162 = l_Lean_Expr_app___override(x_159, x_4);
x_163 = lean_box(0);
x_164 = lean_box(1);
x_165 = lean_alloc_ctor(0, 0, 4);
x_166 = lean_unbox(x_163);
lean_ctor_set_uint8(x_165, 0, x_166);
x_167 = lean_unbox(x_164);
lean_ctor_set_uint8(x_165, 1, x_167);
x_168 = lean_unbox(x_41);
lean_ctor_set_uint8(x_165, 2, x_168);
x_169 = lean_unbox(x_164);
lean_ctor_set_uint8(x_165, 3, x_169);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_170 = l_Lean_MVarId_apply(x_1, x_162, x_165, x_5, x_6, x_7, x_8, x_161);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_172;
goto block_20;
}
else
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_175 = x_170;
} else {
 lean_dec_ref(x_170);
 x_175 = lean_box(0);
}
x_176 = lean_ctor_get(x_171, 0);
lean_inc(x_176);
lean_dec(x_171);
if (lean_is_scalar(x_175)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_175;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_174);
return x_177;
}
else
{
lean_object* x_178; 
lean_dec(x_173);
lean_dec(x_171);
x_178 = lean_ctor_get(x_170, 1);
lean_inc(x_178);
lean_dec(x_170);
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_178;
goto block_20;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_179 = lean_ctor_get(x_170, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_170, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_181 = x_170;
} else {
 lean_dec_ref(x_170);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_159);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_ctor_get(x_160, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_160, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_185 = x_160;
} else {
 lean_dec_ref(x_160);
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
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_148);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_155, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_155, 1);
lean_inc(x_188);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_189 = x_155;
} else {
 lean_dec_ref(x_155);
 x_189 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_190 = lean_alloc_ctor(1, 2, 0);
} else {
 x_190 = x_189;
}
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_188);
return x_190;
}
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_dec(x_148);
lean_dec(x_131);
lean_free_object(x_43);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_191 = lean_ctor_get(x_149, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_149, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_193 = x_149;
} else {
 lean_dec_ref(x_149);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(1, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
x_195 = lean_mk_string_unchecked("constructor must have at least two fields", 41, 41);
x_196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = l_Lean_MessageData_ofFormat(x_196);
lean_ctor_set(x_43, 0, x_197);
x_198 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_43, x_5, x_6, x_7, x_8, x_54);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_198)) {
 lean_ctor_release(x_198, 0);
 lean_ctor_release(x_198, 1);
 x_201 = x_198;
} else {
 lean_dec_ref(x_198);
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
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_53);
lean_free_object(x_43);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_203 = lean_ctor_get(x_52, 1);
lean_inc(x_203);
lean_dec(x_52);
x_204 = lean_box(0);
x_205 = lean_apply_6(x_3, x_204, x_5, x_6, x_7, x_8, x_203);
return x_205;
}
}
else
{
uint8_t x_206; 
lean_free_object(x_43);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_206 = !lean_is_exclusive(x_52);
if (x_206 == 0)
{
return x_52;
}
else
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_207 = lean_ctor_get(x_52, 0);
x_208 = lean_ctor_get(x_52, 1);
lean_inc(x_208);
lean_inc(x_207);
lean_dec(x_52);
x_209 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
return x_209;
}
}
}
else
{
lean_dec(x_50);
lean_dec(x_49);
lean_free_object(x_43);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_39;
goto block_28;
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_free_object(x_43);
lean_dec(x_47);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_210 = lean_box(0);
x_211 = lean_apply_6(x_3, x_210, x_5, x_6, x_7, x_8, x_39);
return x_211;
}
}
else
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_43, 0);
lean_inc(x_212);
lean_dec(x_43);
if (lean_obj_tag(x_212) == 5)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_ctor_get(x_213, 4);
lean_inc(x_214);
lean_dec(x_213);
if (lean_obj_tag(x_214) == 0)
{
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_39;
goto block_28;
}
else
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
lean_dec(x_214);
x_217 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_216, x_5, x_6, x_7, x_8, x_39);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
if (lean_obj_tag(x_218) == 6)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec(x_3);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = lean_ctor_get(x_220, 4);
lean_inc(x_222);
x_223 = lean_unsigned_to_nat(2u);
x_224 = lean_nat_dec_lt(x_222, x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_221);
x_225 = lean_ctor_get(x_220, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
lean_dec(x_225);
x_227 = l_Lean_Expr_const___override(x_226, x_36);
x_228 = lean_box(0);
x_229 = l_Lean_Expr_sort___override(x_228);
x_230 = l_Lean_Expr_getAppNumArgs(x_32);
lean_inc(x_230);
x_231 = lean_mk_array(x_230, x_229);
x_232 = lean_unsigned_to_nat(1u);
x_233 = lean_nat_sub(x_230, x_232);
lean_dec(x_230);
x_234 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_32, x_231, x_233);
x_235 = lean_unsigned_to_nat(0u);
x_236 = lean_ctor_get(x_220, 3);
lean_inc(x_236);
lean_dec(x_220);
x_237 = l_Array_toSubarray___redArg(x_234, x_235, x_236);
x_238 = l_Array_ofSubarray___redArg(x_237);
lean_dec(x_237);
x_239 = l_Lean_mkAppN(x_227, x_238);
lean_dec(x_238);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_239);
x_240 = lean_infer_type(x_239, x_5, x_6, x_7, x_8, x_219);
if (lean_obj_tag(x_240) == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_246; lean_object* x_247; 
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_nat_sub(x_222, x_223);
lean_dec(x_222);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = lean_box(0);
x_246 = lean_unbox(x_245);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_247 = l_Lean_Meta_forallMetaTelescopeReducing(x_241, x_244, x_246, x_5, x_6, x_7, x_8, x_242);
lean_dec(x_244);
if (lean_obj_tag(x_247) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_248 = lean_ctor_get(x_247, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_247, 1);
lean_inc(x_249);
lean_dec(x_247);
x_250 = lean_ctor_get(x_248, 0);
lean_inc(x_250);
lean_dec(x_248);
x_251 = l_Lean_mkAppN(x_239, x_250);
lean_dec(x_250);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_251);
x_252 = l_Lean_Meta_checkApp(x_251, x_4, x_5, x_6, x_7, x_8, x_249);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; uint8_t x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; 
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Lean_Expr_app___override(x_251, x_4);
x_255 = lean_box(0);
x_256 = lean_box(1);
x_257 = lean_alloc_ctor(0, 0, 4);
x_258 = lean_unbox(x_255);
lean_ctor_set_uint8(x_257, 0, x_258);
x_259 = lean_unbox(x_256);
lean_ctor_set_uint8(x_257, 1, x_259);
x_260 = lean_unbox(x_41);
lean_ctor_set_uint8(x_257, 2, x_260);
x_261 = lean_unbox(x_256);
lean_ctor_set_uint8(x_257, 3, x_261);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_262 = l_Lean_MVarId_apply(x_1, x_254, x_257, x_5, x_6, x_7, x_8, x_253);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; 
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_264;
goto block_20;
}
else
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
if (lean_obj_tag(x_265) == 0)
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_267 = x_262;
} else {
 lean_dec_ref(x_262);
 x_267 = lean_box(0);
}
x_268 = lean_ctor_get(x_263, 0);
lean_inc(x_268);
lean_dec(x_263);
if (lean_is_scalar(x_267)) {
 x_269 = lean_alloc_ctor(0, 2, 0);
} else {
 x_269 = x_267;
}
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_266);
return x_269;
}
else
{
lean_object* x_270; 
lean_dec(x_265);
lean_dec(x_263);
x_270 = lean_ctor_get(x_262, 1);
lean_inc(x_270);
lean_dec(x_262);
x_10 = x_5;
x_11 = x_6;
x_12 = x_7;
x_13 = x_8;
x_14 = x_270;
goto block_20;
}
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_271 = lean_ctor_get(x_262, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_262, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_273 = x_262;
} else {
 lean_dec_ref(x_262);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_251);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_275 = lean_ctor_get(x_252, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_252, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_277 = x_252;
} else {
 lean_dec_ref(x_252);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_239);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_279 = lean_ctor_get(x_247, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_247, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_247)) {
 lean_ctor_release(x_247, 0);
 lean_ctor_release(x_247, 1);
 x_281 = x_247;
} else {
 lean_dec_ref(x_247);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
else
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
lean_dec(x_239);
lean_dec(x_222);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_283 = lean_ctor_get(x_240, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_240, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_240)) {
 lean_ctor_release(x_240, 0);
 lean_ctor_release(x_240, 1);
 x_285 = x_240;
} else {
 lean_dec_ref(x_240);
 x_285 = lean_box(0);
}
if (lean_is_scalar(x_285)) {
 x_286 = lean_alloc_ctor(1, 2, 0);
} else {
 x_286 = x_285;
}
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_284);
return x_286;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
x_287 = lean_mk_string_unchecked("constructor must have at least two fields", 41, 41);
if (lean_is_scalar(x_221)) {
 x_288 = lean_alloc_ctor(3, 1, 0);
} else {
 x_288 = x_221;
 lean_ctor_set_tag(x_288, 3);
}
lean_ctor_set(x_288, 0, x_287);
x_289 = l_Lean_MessageData_ofFormat(x_288);
x_290 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_290, 0, x_289);
x_291 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_290, x_5, x_6, x_7, x_8, x_219);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_294 = x_291;
} else {
 lean_dec_ref(x_291);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_294)) {
 x_295 = lean_alloc_ctor(1, 2, 0);
} else {
 x_295 = x_294;
}
lean_ctor_set(x_295, 0, x_292);
lean_ctor_set(x_295, 1, x_293);
return x_295;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_218);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_296 = lean_ctor_get(x_217, 1);
lean_inc(x_296);
lean_dec(x_217);
x_297 = lean_box(0);
x_298 = lean_apply_6(x_3, x_297, x_5, x_6, x_7, x_8, x_296);
return x_298;
}
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_299 = lean_ctor_get(x_217, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_217, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_301 = x_217;
} else {
 lean_dec_ref(x_217);
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
lean_dec(x_215);
lean_dec(x_214);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_39;
goto block_28;
}
}
}
else
{
lean_object* x_303; lean_object* x_304; 
lean_dec(x_212);
lean_dec(x_36);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_303 = lean_box(0);
x_304 = lean_apply_6(x_3, x_303, x_5, x_6, x_7, x_8, x_39);
return x_304;
}
}
}
}
else
{
lean_object* x_305; lean_object* x_306; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_305 = lean_box(0);
x_306 = lean_apply_6(x_3, x_305, x_5, x_6, x_7, x_8, x_33);
return x_306;
}
}
else
{
uint8_t x_307; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_307 = !lean_is_exclusive(x_31);
if (x_307 == 0)
{
return x_31;
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_308 = lean_ctor_get(x_31, 0);
x_309 = lean_ctor_get(x_31, 1);
lean_inc(x_309);
lean_inc(x_308);
lean_dec(x_31);
x_310 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_310, 0, x_308);
lean_ctor_set(x_310, 1, x_309);
return x_310;
}
}
}
else
{
uint8_t x_311; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_311 = !lean_is_exclusive(x_29);
if (x_311 == 0)
{
return x_29;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_29, 0);
x_313 = lean_ctor_get(x_29, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_29);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
block_20:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_mk_string_unchecked("unexpected number of subgoals", 29, 29);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_18, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_19;
}
block_28:
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_box(0);
x_27 = lean_apply_6(x_3, x_26, x_21, x_22, x_23, x_24, x_25);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_mk_string_unchecked("exists", 6, 6);
x_9 = l_Lean_Name_mkStr1(x_8);
lean_inc(x_1);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_existsIntro___lam__0___boxed), 8, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_1);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_MVarId_existsIntro___lam__1), 9, 4);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_9);
lean_closure_set(x_11, 2, x_10);
lean_closure_set(x_11, 3, x_2);
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_11, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_existsIntro___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_existsIntro___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_MVarId_existsIntro(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Constructor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
