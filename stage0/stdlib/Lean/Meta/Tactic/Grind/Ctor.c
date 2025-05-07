// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Ctor
// Imports: Lean.Meta.Tactic.Grind.Types
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
lean_object* l_Lean_Meta_mkAppOptM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkNoConfusion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_Meta_Grind_pushEqCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Meta_Grind_getFalseExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtor___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l_Lean_Meta_Grind_closeGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_grind_mk_eq_proof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Expr_getForallArity(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtor___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_53; uint8_t x_54; 
lean_inc(x_1);
x_16 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_8, x_11);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_53 = l_Lean_Expr_cleanupAnnotations(x_17);
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_2);
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
goto block_52;
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_inc(x_53);
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_53);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
lean_dec(x_2);
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
goto block_52;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_60 = lean_mk_string_unchecked("And", 3, 3);
x_61 = l_Lean_Name_mkStr1(x_60);
x_62 = l_Lean_Expr_isConstOf(x_59, x_61);
if (x_62 == 0)
{
uint8_t x_63; 
lean_dec(x_61);
x_63 = l_Lean_Expr_isApp(x_59);
if (x_63 == 0)
{
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_2);
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
goto block_52;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_inc(x_59);
x_64 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_65 = lean_mk_string_unchecked("Eq", 2, 2);
x_66 = l_Lean_Name_mkStr1(x_65);
x_67 = l_Lean_Expr_isConstOf(x_64, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
uint8_t x_68; 
lean_dec(x_58);
x_68 = l_Lean_Expr_isApp(x_64);
if (x_68 == 0)
{
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_2);
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
goto block_52;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_70 = lean_mk_string_unchecked("HEq", 3, 3);
x_71 = l_Lean_Name_mkStr1(x_70);
x_72 = l_Lean_Expr_isConstOf(x_69, x_71);
lean_dec(x_71);
lean_dec(x_69);
if (x_72 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_2);
x_20 = x_4;
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
goto block_52;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_19);
lean_dec(x_1);
x_73 = lean_ctor_get(x_59, 1);
lean_inc(x_73);
lean_dec(x_59);
x_74 = l_Lean_Meta_Grind_shareCommon___redArg(x_73, x_6, x_18);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = l_Lean_Meta_Grind_shareCommon___redArg(x_57, x_6, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Meta_Grind_pushEqCore(x_75, x_78, x_2, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_64);
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_1);
x_81 = l_Lean_Meta_Grind_shareCommon___redArg(x_58, x_6, x_18);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
x_84 = l_Lean_Meta_Grind_shareCommon___redArg(x_57, x_6, x_83);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Meta_Grind_pushEqCore(x_82, x_85, x_2, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_59);
lean_dec(x_19);
lean_dec(x_1);
x_88 = lean_unsigned_to_nat(0u);
lean_inc(x_2);
lean_inc(x_61);
x_89 = l_Lean_Expr_proj___override(x_61, x_88, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_90 = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(x_58, x_89, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_18);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_unsigned_to_nat(1u);
x_93 = l_Lean_Expr_proj___override(x_61, x_92, x_2);
x_1 = x_57;
x_2 = x_93;
x_11 = x_91;
goto _start;
}
else
{
lean_dec(x_61);
lean_dec(x_57);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_90;
}
}
}
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_52:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = l_Lean_Meta_Grind_getConfig___redArg(x_21, x_18);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_28, sizeof(void*)*7 + 10);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_1);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
x_12 = x_30;
goto block_15;
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_27, 1);
x_33 = lean_ctor_get(x_27, 0);
lean_dec(x_33);
x_34 = lean_mk_string_unchecked("unexpected injectivity theorem result type", 42, 42);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_27, 7);
lean_ctor_set(x_27, 1, x_36);
lean_ctor_set(x_27, 0, x_35);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
if (lean_is_scalar(x_19)) {
 x_39 = lean_alloc_ctor(7, 2, 0);
} else {
 x_39 = x_19;
 lean_ctor_set_tag(x_39, 7);
}
lean_ctor_set(x_39, 0, x_27);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_Meta_Grind_reportIssue(x_39, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_32);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_12 = x_41;
goto block_15;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_mk_string_unchecked("unexpected injectivity theorem result type", 42, 42);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = l_Lean_indentExpr(x_1);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("", 0, 0);
x_48 = l_Lean_stringToMessageData(x_47);
lean_dec(x_47);
if (lean_is_scalar(x_19)) {
 x_49 = lean_alloc_ctor(7, 2, 0);
} else {
 x_49 = x_19;
 lean_ctor_set_tag(x_49, 7);
}
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_48);
x_50 = l_Lean_Meta_Grind_reportIssue(x_49, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_42);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_12 = x_51;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
lean_inc(x_1);
x_14 = l_Lean_Environment_find_x3f(x_11, x_1, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_7);
x_15 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_unbox(x_12);
x_18 = l_Lean_MessageData_ofConstName(x_1, x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_mk_string_unchecked("'", 1, 1);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(x_22, x_2, x_3, x_4, x_5, x_10);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_1);
x_24 = lean_ctor_get(x_14, 0);
lean_inc(x_24);
lean_dec(x_14);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
lean_inc(x_1);
x_30 = l_Lean_Environment_find_x3f(x_27, x_1, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_unbox(x_28);
x_34 = l_Lean_MessageData_ofConstName(x_1, x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("'", 1, 1);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(x_38, x_2, x_3, x_4, x_5, x_26);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtor___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_1);
x_12 = lean_infer_type(x_1, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_15 = l_Lean_Meta_whnfD(x_13, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_18 = lean_infer_type(x_2, x_7, x_8, x_9, x_10, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_Meta_whnfD(x_19, x_7, x_8, x_9, x_10, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; uint8_t x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; uint8_t x_50; uint64_t x_51; uint64_t x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(1);
x_25 = lean_ctor_get(x_7, 0);
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
x_45 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_shift_left(x_48, x_47);
x_50 = lean_unbox(x_24);
x_51 = l_Lean_Meta_TransparencyMode_toUInt64(x_50);
x_52 = lean_uint64_lor(x_49, x_51);
x_53 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_54 = lean_ctor_get(x_7, 1);
lean_inc(x_54);
x_55 = lean_ctor_get(x_7, 2);
lean_inc(x_55);
x_56 = lean_ctor_get(x_7, 3);
lean_inc(x_56);
x_57 = lean_ctor_get(x_7, 4);
lean_inc(x_57);
x_58 = lean_ctor_get(x_7, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_7, 6);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_61 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
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
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_63 = l_Lean_Meta_isExprDefEq(x_16, x_22, x_62, x_8, x_9, x_10, x_23);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_unbox(x_64);
if (x_65 == 0)
{
uint8_t x_66; 
lean_dec(x_64);
lean_dec(x_16);
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
x_66 = !lean_is_exclusive(x_63);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_63, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set(x_63, 0, x_68);
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 1);
lean_inc(x_69);
lean_dec(x_63);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_63, 1);
lean_inc(x_72);
lean_dec(x_63);
x_73 = l_Lean_Expr_getAppFn(x_1);
x_74 = l_Lean_Expr_getAppFn(x_2);
x_75 = lean_expr_eqv(x_73, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_73);
x_76 = l_Lean_Expr_getAppFn(x_16);
lean_dec(x_16);
switch (lean_obj_tag(x_76)) {
case 0:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
lean_dec(x_76);
x_78 = l_Lean_Expr_bvar___override(x_77);
x_79 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_78, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_78);
return x_79;
}
case 1:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
x_81 = l_Lean_Expr_fvar___override(x_80);
x_82 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_81, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_81);
return x_82;
}
case 2:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_76, 0);
lean_inc(x_83);
lean_dec(x_76);
x_84 = l_Lean_Expr_mvar___override(x_83);
x_85 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_84);
return x_85;
}
case 3:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_ctor_get(x_76, 0);
lean_inc(x_86);
lean_dec(x_76);
x_87 = l_Lean_Expr_sort___override(x_86);
x_88 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_87, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_87);
return x_88;
}
case 4:
{
lean_object* x_89; lean_object* x_90; uint8_t x_91; 
x_89 = lean_ctor_get(x_76, 0);
lean_inc(x_89);
lean_dec(x_76);
x_90 = lean_st_ref_get(x_10, x_72);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; uint8_t x_98; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_90, 1);
x_94 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_95 = l_Lean_Name_str___override(x_89, x_94);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_unbox(x_64);
lean_dec(x_64);
x_98 = l_Lean_Environment_contains(x_96, x_95, x_97);
if (x_98 == 0)
{
lean_object* x_99; 
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
x_99 = lean_box(0);
lean_ctor_set(x_90, 0, x_99);
return x_90;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_90);
x_100 = l_Lean_Meta_Grind_getFalseExpr(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_93);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_103 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_106 = l_Lean_Meta_mkNoConfusion(x_101, x_104, x_7, x_8, x_9, x_10, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Meta_Grind_closeGoal(x_107, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_108);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_109;
}
else
{
uint8_t x_110; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
else
{
uint8_t x_114; 
lean_dec(x_101);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_114 = !lean_is_exclusive(x_103);
if (x_114 == 0)
{
return x_103;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_103, 0);
x_116 = lean_ctor_get(x_103, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_103);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; uint8_t x_124; 
x_118 = lean_ctor_get(x_90, 0);
x_119 = lean_ctor_get(x_90, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_90);
x_120 = lean_mk_string_unchecked("noConfusion", 11, 11);
x_121 = l_Lean_Name_str___override(x_89, x_120);
x_122 = lean_ctor_get(x_118, 0);
lean_inc(x_122);
lean_dec(x_118);
x_123 = lean_unbox(x_64);
lean_dec(x_64);
x_124 = l_Lean_Environment_contains(x_122, x_121, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
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
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_119);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = l_Lean_Meta_Grind_getFalseExpr(x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_119);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_130 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_133 = l_Lean_Meta_mkNoConfusion(x_128, x_131, x_7, x_8, x_9, x_10, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Meta_Grind_closeGoal(x_134, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_135);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_137 = lean_ctor_get(x_133, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_133, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_139 = x_133;
} else {
 lean_dec_ref(x_133);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_128);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_141 = lean_ctor_get(x_130, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_130, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_143 = x_130;
} else {
 lean_dec_ref(x_130);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
}
}
}
case 5:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_ctor_get(x_76, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_76, 1);
lean_inc(x_146);
lean_dec(x_76);
x_147 = l_Lean_Expr_app___override(x_145, x_146);
x_148 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_147, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_147);
return x_148;
}
case 6:
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_149 = lean_ctor_get(x_76, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_76, 1);
lean_inc(x_150);
x_151 = lean_ctor_get(x_76, 2);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_76, sizeof(void*)*3 + 8);
lean_dec(x_76);
x_153 = l_Lean_Expr_lam___override(x_149, x_150, x_151, x_152);
x_154 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_153, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_153);
return x_154;
}
case 7:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_155 = lean_ctor_get(x_76, 0);
lean_inc(x_155);
x_156 = lean_ctor_get(x_76, 1);
lean_inc(x_156);
x_157 = lean_ctor_get(x_76, 2);
lean_inc(x_157);
x_158 = lean_ctor_get_uint8(x_76, sizeof(void*)*3 + 8);
lean_dec(x_76);
x_159 = l_Lean_Expr_forallE___override(x_155, x_156, x_157, x_158);
x_160 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_159, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_159);
return x_160;
}
case 8:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; lean_object* x_166; lean_object* x_167; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_161 = lean_ctor_get(x_76, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_76, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_76, 2);
lean_inc(x_163);
x_164 = lean_ctor_get(x_76, 3);
lean_inc(x_164);
x_165 = lean_ctor_get_uint8(x_76, sizeof(void*)*4 + 8);
lean_dec(x_76);
x_166 = l_Lean_Expr_letE___override(x_161, x_162, x_163, x_164, x_165);
x_167 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_166, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_166);
return x_167;
}
case 9:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_168 = lean_ctor_get(x_76, 0);
lean_inc(x_168);
lean_dec(x_76);
x_169 = l_Lean_Expr_lit___override(x_168);
x_170 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_169, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_169);
return x_170;
}
case 10:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_171 = lean_ctor_get(x_76, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_76, 1);
lean_inc(x_172);
lean_dec(x_76);
x_173 = l_Lean_Expr_mdata___override(x_171, x_172);
x_174 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_173, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_173);
return x_174;
}
default: 
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_175 = lean_ctor_get(x_76, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_76, 1);
lean_inc(x_176);
x_177 = lean_ctor_get(x_76, 2);
lean_inc(x_177);
lean_dec(x_76);
x_178 = l_Lean_Expr_proj___override(x_175, x_176, x_177);
x_179 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_178, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_178);
return x_179;
}
}
}
else
{
lean_dec(x_16);
switch (lean_obj_tag(x_73)) {
case 0:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_180 = lean_ctor_get(x_73, 0);
lean_inc(x_180);
lean_dec(x_73);
x_181 = l_Lean_Expr_bvar___override(x_180);
x_182 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_181, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_181);
return x_182;
}
case 1:
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_ctor_get(x_73, 0);
lean_inc(x_183);
lean_dec(x_73);
x_184 = l_Lean_Expr_fvar___override(x_183);
x_185 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_184, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_184);
return x_185;
}
case 2:
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_186 = lean_ctor_get(x_73, 0);
lean_inc(x_186);
lean_dec(x_73);
x_187 = l_Lean_Expr_mvar___override(x_186);
x_188 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_187, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_187);
return x_188;
}
case 3:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_189 = lean_ctor_get(x_73, 0);
lean_inc(x_189);
lean_dec(x_73);
x_190 = l_Lean_Expr_sort___override(x_189);
x_191 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_190, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_190);
return x_191;
}
case 4:
{
lean_object* x_192; lean_object* x_193; uint8_t x_194; 
x_192 = lean_ctor_get(x_73, 0);
lean_inc(x_192);
lean_dec(x_73);
x_193 = lean_st_ref_get(x_10, x_72);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; uint8_t x_201; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
x_197 = lean_mk_string_unchecked("inj", 3, 3);
x_198 = l_Lean_Name_str___override(x_192, x_197);
x_199 = lean_ctor_get(x_195, 0);
lean_inc(x_199);
lean_dec(x_195);
x_200 = lean_unbox(x_64);
lean_dec(x_64);
lean_inc(x_198);
x_201 = l_Lean_Environment_contains(x_199, x_198, x_200);
if (x_201 == 0)
{
lean_object* x_202; 
lean_dec(x_198);
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
x_202 = lean_box(0);
lean_ctor_set(x_193, 0, x_202);
return x_193;
}
else
{
lean_object* x_203; 
lean_free_object(x_193);
lean_inc(x_198);
x_203 = l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg(x_198, x_7, x_8, x_9, x_10, x_196);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_206 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_205);
if (lean_obj_tag(x_206) == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_206, 1);
lean_inc(x_208);
lean_dec(x_206);
x_209 = l_Lean_ConstantInfo_type(x_204);
lean_dec(x_204);
x_210 = lean_box(0);
x_211 = l_Lean_Expr_getForallArity(x_209);
lean_inc(x_211);
x_212 = lean_mk_array(x_211, x_210);
x_213 = lean_unsigned_to_nat(1u);
x_214 = lean_nat_sub(x_211, x_213);
lean_dec(x_211);
x_215 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_215, 0, x_207);
x_216 = lean_array_set(x_212, x_214, x_215);
lean_dec(x_214);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_217 = l_Lean_Meta_mkAppOptM(x_198, x_216, x_7, x_8, x_9, x_10, x_208);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_218);
x_220 = lean_infer_type(x_218, x_7, x_8, x_9, x_10, x_219);
if (lean_obj_tag(x_220) == 0)
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
lean_dec(x_220);
x_223 = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(x_221, x_218, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_222);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_223;
}
else
{
uint8_t x_224; 
lean_dec(x_218);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_224 = !lean_is_exclusive(x_220);
if (x_224 == 0)
{
return x_220;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_220, 0);
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
lean_inc(x_225);
lean_dec(x_220);
x_227 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
return x_227;
}
}
}
else
{
uint8_t x_228; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_228 = !lean_is_exclusive(x_217);
if (x_228 == 0)
{
return x_217;
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_217, 0);
x_230 = lean_ctor_get(x_217, 1);
lean_inc(x_230);
lean_inc(x_229);
lean_dec(x_217);
x_231 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
return x_231;
}
}
}
else
{
uint8_t x_232; 
lean_dec(x_204);
lean_dec(x_198);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_232 = !lean_is_exclusive(x_206);
if (x_232 == 0)
{
return x_206;
}
else
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_233 = lean_ctor_get(x_206, 0);
x_234 = lean_ctor_get(x_206, 1);
lean_inc(x_234);
lean_inc(x_233);
lean_dec(x_206);
x_235 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_198);
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
x_236 = !lean_is_exclusive(x_203);
if (x_236 == 0)
{
return x_203;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_203, 0);
x_238 = lean_ctor_get(x_203, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_203);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; uint8_t x_246; 
x_240 = lean_ctor_get(x_193, 0);
x_241 = lean_ctor_get(x_193, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_193);
x_242 = lean_mk_string_unchecked("inj", 3, 3);
x_243 = l_Lean_Name_str___override(x_192, x_242);
x_244 = lean_ctor_get(x_240, 0);
lean_inc(x_244);
lean_dec(x_240);
x_245 = lean_unbox(x_64);
lean_dec(x_64);
lean_inc(x_243);
x_246 = l_Lean_Environment_contains(x_244, x_243, x_245);
if (x_246 == 0)
{
lean_object* x_247; lean_object* x_248; 
lean_dec(x_243);
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
x_247 = lean_box(0);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_241);
return x_248;
}
else
{
lean_object* x_249; 
lean_inc(x_243);
x_249 = l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg(x_243, x_7, x_8, x_9, x_10, x_241);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_249, 1);
lean_inc(x_251);
lean_dec(x_249);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_252 = lean_grind_mk_eq_proof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_251);
if (lean_obj_tag(x_252) == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_252, 1);
lean_inc(x_254);
lean_dec(x_252);
x_255 = l_Lean_ConstantInfo_type(x_250);
lean_dec(x_250);
x_256 = lean_box(0);
x_257 = l_Lean_Expr_getForallArity(x_255);
lean_inc(x_257);
x_258 = lean_mk_array(x_257, x_256);
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_nat_sub(x_257, x_259);
lean_dec(x_257);
x_261 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_261, 0, x_253);
x_262 = lean_array_set(x_258, x_260, x_261);
lean_dec(x_260);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_263 = l_Lean_Meta_mkAppOptM(x_243, x_262, x_7, x_8, x_9, x_10, x_254);
if (lean_obj_tag(x_263) == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_264);
x_266 = lean_infer_type(x_264, x_7, x_8, x_9, x_10, x_265);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
lean_dec(x_266);
x_269 = l___private_Lean_Meta_Tactic_Grind_Ctor_0__Lean_Meta_Grind_propagateInjEqs(x_267, x_264, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_268);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_269;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
lean_dec(x_264);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_270 = lean_ctor_get(x_266, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_266, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_272 = x_266;
} else {
 lean_dec_ref(x_266);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(1, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_270);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_274 = lean_ctor_get(x_263, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_263, 1);
lean_inc(x_275);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_276 = x_263;
} else {
 lean_dec_ref(x_263);
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
lean_dec(x_250);
lean_dec(x_243);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_278 = lean_ctor_get(x_252, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_252, 1);
lean_inc(x_279);
if (lean_is_exclusive(x_252)) {
 lean_ctor_release(x_252, 0);
 lean_ctor_release(x_252, 1);
 x_280 = x_252;
} else {
 lean_dec_ref(x_252);
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
lean_dec(x_243);
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
x_282 = lean_ctor_get(x_249, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_249, 1);
lean_inc(x_283);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_284 = x_249;
} else {
 lean_dec_ref(x_249);
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
}
}
case 5:
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_286 = lean_ctor_get(x_73, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_73, 1);
lean_inc(x_287);
lean_dec(x_73);
x_288 = l_Lean_Expr_app___override(x_286, x_287);
x_289 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_288, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_288);
return x_289;
}
case 6:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_290 = lean_ctor_get(x_73, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_73, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_73, 2);
lean_inc(x_292);
x_293 = lean_ctor_get_uint8(x_73, sizeof(void*)*3 + 8);
lean_dec(x_73);
x_294 = l_Lean_Expr_lam___override(x_290, x_291, x_292, x_293);
x_295 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_294, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_294);
return x_295;
}
case 7:
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_296 = lean_ctor_get(x_73, 0);
lean_inc(x_296);
x_297 = lean_ctor_get(x_73, 1);
lean_inc(x_297);
x_298 = lean_ctor_get(x_73, 2);
lean_inc(x_298);
x_299 = lean_ctor_get_uint8(x_73, sizeof(void*)*3 + 8);
lean_dec(x_73);
x_300 = l_Lean_Expr_forallE___override(x_296, x_297, x_298, x_299);
x_301 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_300, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_300);
return x_301;
}
case 8:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_302 = lean_ctor_get(x_73, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_73, 1);
lean_inc(x_303);
x_304 = lean_ctor_get(x_73, 2);
lean_inc(x_304);
x_305 = lean_ctor_get(x_73, 3);
lean_inc(x_305);
x_306 = lean_ctor_get_uint8(x_73, sizeof(void*)*4 + 8);
lean_dec(x_73);
x_307 = l_Lean_Expr_letE___override(x_302, x_303, x_304, x_305, x_306);
x_308 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_307, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_307);
return x_308;
}
case 9:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_309 = lean_ctor_get(x_73, 0);
lean_inc(x_309);
lean_dec(x_73);
x_310 = l_Lean_Expr_lit___override(x_309);
x_311 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_310, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_310);
return x_311;
}
case 10:
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_312 = lean_ctor_get(x_73, 0);
lean_inc(x_312);
x_313 = lean_ctor_get(x_73, 1);
lean_inc(x_313);
lean_dec(x_73);
x_314 = l_Lean_Expr_mdata___override(x_312, x_313);
x_315 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_314, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_314);
return x_315;
}
default: 
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; 
lean_dec(x_64);
lean_dec(x_2);
lean_dec(x_1);
x_316 = lean_ctor_get(x_73, 0);
lean_inc(x_316);
x_317 = lean_ctor_get(x_73, 1);
lean_inc(x_317);
x_318 = lean_ctor_get(x_73, 2);
lean_inc(x_318);
lean_dec(x_73);
x_319 = l_Lean_Expr_proj___override(x_316, x_317, x_318);
x_320 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_319, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_72);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_319);
return x_320;
}
}
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_16);
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
x_321 = !lean_is_exclusive(x_63);
if (x_321 == 0)
{
return x_63;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_63, 0);
x_323 = lean_ctor_get(x_63, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_63);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
else
{
uint8_t x_325; 
lean_dec(x_16);
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
x_325 = !lean_is_exclusive(x_21);
if (x_325 == 0)
{
return x_21;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_21, 0);
x_327 = lean_ctor_get(x_21, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_21);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
else
{
uint8_t x_329; 
lean_dec(x_16);
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
x_329 = !lean_is_exclusive(x_18);
if (x_329 == 0)
{
return x_18;
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; 
x_330 = lean_ctor_get(x_18, 0);
x_331 = lean_ctor_get(x_18, 1);
lean_inc(x_331);
lean_inc(x_330);
lean_dec(x_18);
x_332 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_332, 0, x_330);
lean_ctor_set(x_332, 1, x_331);
return x_332;
}
}
}
else
{
uint8_t x_333; 
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
x_333 = !lean_is_exclusive(x_15);
if (x_333 == 0)
{
return x_15;
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; 
x_334 = lean_ctor_get(x_15, 0);
x_335 = lean_ctor_get(x_15, 1);
lean_inc(x_335);
lean_inc(x_334);
lean_dec(x_15);
x_336 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_336, 0, x_334);
lean_ctor_set(x_336, 1, x_335);
return x_336;
}
}
}
else
{
uint8_t x_337; 
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
x_337 = !lean_is_exclusive(x_12);
if (x_337 == 0)
{
return x_12;
}
else
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_338 = lean_ctor_get(x_12, 0);
x_339 = lean_ctor_get(x_12, 1);
lean_inc(x_339);
lean_inc(x_338);
lean_dec(x_12);
x_340 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
return x_340;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_getConstInfo___at___Lean_Meta_Grind_propagateCtor_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_propagateCtor___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_propagateCtor___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Ctor(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
