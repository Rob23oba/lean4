// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Cutsat.DvdCnstr
// Imports: Lean.Meta.Tactic.Simp.Arith.Int Lean.Meta.Tactic.Grind.PropagatorAttr Lean.Meta.Tactic.Grind.Arith.Cutsat.Var Lean.Meta.Tactic.Grind.Arith.Cutsat.Util Lean.Meta.Tactic.Grind.Arith.Cutsat.Proof Lean.Meta.Tactic.Grind.Arith.Cutsat.Norm
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
lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Meta_Grind_pushNewFact(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_reportIssue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_toPoly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_coeff(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579_(lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(lean_object*);
lean_object* l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
lean_object* l_Int_OfNat_toIntDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getGeneration___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_OfNat_Expr_denoteAsIntExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_updateOccs___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
lean_object* l_Int_Linear_Poly_findVarToSubst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Meta_mkOfEqFalseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
lean_object* l_Int_Linear_Poly_combine(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_mkEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_norm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatDvd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isSorted(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_reflBoolTrue;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqTrue___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_isEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_get_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_set(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_Cutsat_getVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_24; lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = l_Int_Linear_Poly_isSorted(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = l_Int_Linear_Poly_norm(x_33);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_1);
x_38 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_37);
x_24 = x_38;
goto block_32;
}
else
{
lean_dec(x_33);
x_24 = x_1;
goto block_32;
}
block_11:
{
if (x_6 == 0)
{
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_int_ediv(x_3, x_2);
lean_dec(x_3);
x_8 = l_Int_Linear_Poly_div(x_2, x_4);
lean_dec(x_2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_5);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
block_23:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = l_Int_Linear_Poly_getConst(x_15);
x_18 = lean_int_emod(x_17, x_16);
lean_dec(x_17);
x_19 = lean_int_dec_eq(x_18, x_12);
lean_dec(x_12);
lean_dec(x_18);
if (x_19 == 0)
{
x_2 = x_16;
x_3 = x_13;
x_4 = x_15;
x_5 = x_14;
x_6 = x_19;
goto block_11;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_dec_eq(x_16, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
x_2 = x_16;
x_3 = x_13;
x_4 = x_15;
x_5 = x_14;
x_6 = x_19;
goto block_11;
}
else
{
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
return x_14;
}
}
}
block_32:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_inc(x_26);
x_27 = l_Int_Linear_Poly_gcdCoeffs(x_25, x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_int_dec_lt(x_26, x_29);
if (x_30 == 0)
{
x_12 = x_29;
x_13 = x_26;
x_14 = x_24;
x_15 = x_25;
x_16 = x_27;
goto block_23;
}
else
{
lean_object* x_31; 
x_31 = lean_int_neg(x_27);
lean_dec(x_27);
x_12 = x_29;
x_13 = x_26;
x_14 = x_24;
x_15 = x_25;
x_16 = x_31;
goto block_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_39; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_mk_string_unchecked("grind", 5, 5);
x_17 = lean_mk_string_unchecked("debug", 5, 5);
x_18 = lean_mk_string_unchecked("cutsat", 6, 6);
x_19 = lean_mk_string_unchecked("subst", 5, 5);
x_20 = l_Lean_Name_mkStr4(x_16, x_17, x_18, x_19);
lean_inc(x_20);
x_21 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_20, x_12, x_14);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_5, 1);
lean_inc(x_26);
x_27 = lean_int_mul(x_1, x_15);
lean_dec(x_15);
x_28 = lean_int_neg(x_4);
x_29 = lean_nat_abs(x_27);
lean_dec(x_27);
x_30 = l_Int_Linear_Poly_mul(x_26, x_1);
x_31 = l_Int_Linear_Poly_mul(x_25, x_28);
lean_dec(x_28);
x_32 = lean_nat_to_int(x_29);
x_33 = l_Int_Linear_Poly_combine(x_30, x_31);
x_39 = lean_unbox(x_22);
lean_dec(x_22);
if (x_39 == 0)
{
lean_dec(x_20);
x_34 = x_23;
goto block_38;
}
else
{
lean_object* x_40; uint8_t x_41; 
x_40 = l_Lean_Meta_Grind_Arith_Cutsat_getVar(x_2, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_23);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_3);
x_44 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_43);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_5);
x_48 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_47);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
x_52 = lean_mk_string_unchecked("", 0, 0);
x_53 = l_Lean_stringToMessageData(x_52);
lean_dec(x_52);
x_54 = l_Lean_MessageData_ofExpr(x_42);
lean_inc(x_53);
lean_ctor_set_tag(x_48, 7);
lean_ctor_set(x_48, 1, x_54);
lean_ctor_set(x_48, 0, x_53);
x_55 = lean_mk_string_unchecked(", ", 2, 2);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
lean_inc(x_56);
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_56);
lean_ctor_set(x_44, 0, x_48);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_46);
lean_ctor_set(x_40, 0, x_44);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_40);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_50);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_53);
x_60 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_20, x_59, x_10, x_11, x_12, x_13, x_51);
x_61 = lean_ctor_get(x_60, 1);
lean_inc(x_61);
lean_dec(x_60);
x_34 = x_61;
goto block_38;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_62 = lean_ctor_get(x_48, 0);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_48);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = l_Lean_MessageData_ofExpr(x_42);
lean_inc(x_65);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_mk_string_unchecked(", ", 2, 2);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
lean_inc(x_69);
lean_ctor_set_tag(x_44, 7);
lean_ctor_set(x_44, 1, x_69);
lean_ctor_set(x_44, 0, x_67);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_46);
lean_ctor_set(x_40, 0, x_44);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_40);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_62);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_65);
x_73 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_20, x_72, x_10, x_11, x_12, x_13, x_63);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_34 = x_74;
goto block_38;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_75 = lean_ctor_get(x_44, 0);
x_76 = lean_ctor_get(x_44, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_44);
lean_inc(x_5);
x_77 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_76);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_80 = x_77;
} else {
 lean_dec_ref(x_77);
 x_80 = lean_box(0);
}
x_81 = lean_mk_string_unchecked("", 0, 0);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = l_Lean_MessageData_ofExpr(x_42);
lean_inc(x_82);
if (lean_is_scalar(x_80)) {
 x_84 = lean_alloc_ctor(7, 2, 0);
} else {
 x_84 = x_80;
 lean_ctor_set_tag(x_84, 7);
}
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_mk_string_unchecked(", ", 2, 2);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
lean_inc(x_86);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_75);
lean_ctor_set(x_40, 0, x_87);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_40);
lean_ctor_set(x_88, 1, x_86);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_78);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_82);
x_91 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_20, x_90, x_10, x_11, x_12, x_13, x_79);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
x_34 = x_92;
goto block_38;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_93 = lean_ctor_get(x_40, 0);
x_94 = lean_ctor_get(x_40, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_40);
lean_inc(x_3);
x_95 = l_Lean_Meta_Grind_Arith_Cutsat_EqCnstr_pp___redArg(x_3, x_6, x_94);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_98 = x_95;
} else {
 lean_dec_ref(x_95);
 x_98 = lean_box(0);
}
lean_inc(x_5);
x_99 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_5, x_6, x_97);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_102 = x_99;
} else {
 lean_dec_ref(x_99);
 x_102 = lean_box(0);
}
x_103 = lean_mk_string_unchecked("", 0, 0);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = l_Lean_MessageData_ofExpr(x_93);
lean_inc(x_104);
if (lean_is_scalar(x_102)) {
 x_106 = lean_alloc_ctor(7, 2, 0);
} else {
 x_106 = x_102;
 lean_ctor_set_tag(x_106, 7);
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_mk_string_unchecked(", ", 2, 2);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
lean_inc(x_108);
if (lean_is_scalar(x_98)) {
 x_109 = lean_alloc_ctor(7, 2, 0);
} else {
 x_109 = x_98;
 lean_ctor_set_tag(x_109, 7);
}
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_96);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_100);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_104);
x_114 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_20, x_113, x_10, x_11, x_12, x_13, x_101);
x_115 = lean_ctor_get(x_114, 1);
lean_inc(x_115);
lean_dec(x_114);
x_34 = x_115;
goto block_38;
}
}
block_38:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_alloc_ctor(8, 3, 0);
lean_ctor_set(x_35, 0, x_2);
lean_ctor_set(x_35, 1, x_3);
lean_ctor_set(x_35, 2, x_5);
x_36 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_33);
lean_ctor_set(x_36, 2, x_35);
if (lean_is_scalar(x_24)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_24;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 4);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_11, x_15);
lean_dec(x_11);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_8, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_8, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_8, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_8, 7);
lean_inc(x_22);
x_23 = lean_ctor_get(x_8, 8);
lean_inc(x_23);
x_24 = lean_ctor_get(x_8, 9);
lean_inc(x_24);
x_25 = lean_ctor_get(x_8, 10);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_27 = lean_ctor_get(x_8, 11);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_29 = lean_ctor_get(x_8, 12);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_18);
lean_ctor_set(x_30, 2, x_19);
lean_ctor_set(x_30, 3, x_16);
lean_ctor_set(x_30, 4, x_12);
lean_ctor_set(x_30, 5, x_20);
lean_ctor_set(x_30, 6, x_21);
lean_ctor_set(x_30, 7, x_22);
lean_ctor_set(x_30, 8, x_23);
lean_ctor_set(x_30, 9, x_24);
lean_ctor_set(x_30, 10, x_25);
lean_ctor_set(x_30, 11, x_27);
lean_ctor_set(x_30, 12, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*13, x_26);
lean_ctor_set_uint8(x_30, sizeof(void*)*13 + 1, x_28);
x_31 = l_Int_Linear_Poly_findVarToSubst(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_30, x_9, x_10);
lean_dec(x_14);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
lean_dec(x_30);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 0);
lean_dec(x_34);
lean_ctor_set(x_31, 0, x_1);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_40 = lean_ctor_get(x_37, 0);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_ctor_get(x_38, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = l_Int_Linear_Poly_coeff(x_43, x_41);
lean_dec(x_43);
x_45 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applyEq(x_44, x_41, x_42, x_40, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_30, x_9, x_39);
lean_dec(x_40);
lean_dec(x_44);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_1 = x_46;
x_8 = x_30;
x_10 = x_47;
goto _start;
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_1);
x_49 = lean_ctor_get(x_8, 5);
lean_inc(x_49);
x_50 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_box(0), x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_8);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_76; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
x_99 = lean_ctor_get(x_8, 3);
lean_inc(x_99);
x_100 = lean_ctor_get(x_8, 4);
lean_inc(x_100);
x_101 = lean_nat_dec_eq(x_99, x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_102 = lean_unsigned_to_nat(1u);
x_103 = l_Lean_Meta_Grind_Arith_Cutsat_inconsistent___redArg(x_2, x_10);
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_unbox(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_490; lean_object* x_491; lean_object* x_492; uint8_t x_493; 
x_106 = lean_ctor_get(x_103, 1);
lean_inc(x_106);
lean_dec(x_103);
x_107 = lean_nat_add(x_99, x_102);
lean_dec(x_99);
x_108 = lean_ctor_get(x_8, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_8, 1);
lean_inc(x_109);
x_110 = lean_ctor_get(x_8, 2);
lean_inc(x_110);
x_111 = lean_ctor_get(x_8, 5);
lean_inc(x_111);
x_112 = lean_ctor_get(x_8, 6);
lean_inc(x_112);
x_113 = lean_ctor_get(x_8, 7);
lean_inc(x_113);
x_114 = lean_ctor_get(x_8, 8);
lean_inc(x_114);
x_115 = lean_ctor_get(x_8, 9);
lean_inc(x_115);
x_116 = lean_ctor_get(x_8, 10);
lean_inc(x_116);
x_117 = lean_ctor_get_uint8(x_8, sizeof(void*)*13);
x_118 = lean_ctor_get(x_8, 11);
lean_inc(x_118);
x_119 = lean_ctor_get_uint8(x_8, sizeof(void*)*13 + 1);
x_120 = lean_ctor_get(x_8, 12);
lean_inc(x_120);
lean_dec(x_8);
x_121 = lean_box(0);
x_122 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_122, 0, x_108);
lean_ctor_set(x_122, 1, x_109);
lean_ctor_set(x_122, 2, x_110);
lean_ctor_set(x_122, 3, x_107);
lean_ctor_set(x_122, 4, x_100);
lean_ctor_set(x_122, 5, x_111);
lean_ctor_set(x_122, 6, x_112);
lean_ctor_set(x_122, 7, x_113);
lean_ctor_set(x_122, 8, x_114);
lean_ctor_set(x_122, 9, x_115);
lean_ctor_set(x_122, 10, x_116);
lean_ctor_set(x_122, 11, x_118);
lean_ctor_set(x_122, 12, x_120);
lean_ctor_set_uint8(x_122, sizeof(void*)*13, x_117);
lean_ctor_set_uint8(x_122, sizeof(void*)*13 + 1, x_119);
x_123 = lean_mk_string_unchecked("grind", 5, 5);
x_124 = lean_mk_string_unchecked("cutsat", 6, 6);
x_125 = lean_mk_string_unchecked("assert", 6, 6);
lean_inc(x_125);
lean_inc(x_124);
lean_inc(x_123);
x_490 = l_Lean_Name_mkStr3(x_123, x_124, x_125);
lean_inc(x_490);
x_491 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_490, x_122, x_106);
x_492 = lean_ctor_get(x_491, 0);
lean_inc(x_492);
x_493 = lean_unbox(x_492);
lean_dec(x_492);
if (x_493 == 0)
{
lean_object* x_494; 
lean_dec(x_490);
x_494 = lean_ctor_get(x_491, 1);
lean_inc(x_494);
lean_dec(x_491);
x_385 = x_2;
x_386 = x_3;
x_387 = x_4;
x_388 = x_5;
x_389 = x_6;
x_390 = x_7;
x_391 = x_122;
x_392 = x_9;
x_393 = x_494;
goto block_489;
}
else
{
uint8_t x_495; 
x_495 = !lean_is_exclusive(x_491);
if (x_495 == 0)
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; uint8_t x_499; 
x_496 = lean_ctor_get(x_491, 1);
x_497 = lean_ctor_get(x_491, 0);
lean_dec(x_497);
lean_inc(x_1);
x_498 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_496);
x_499 = !lean_is_exclusive(x_498);
if (x_499 == 0)
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
x_500 = lean_ctor_get(x_498, 0);
x_501 = lean_ctor_get(x_498, 1);
x_502 = lean_mk_string_unchecked("", 0, 0);
x_503 = l_Lean_stringToMessageData(x_502);
lean_dec(x_502);
lean_inc(x_503);
lean_ctor_set_tag(x_498, 7);
lean_ctor_set(x_498, 1, x_500);
lean_ctor_set(x_498, 0, x_503);
lean_ctor_set_tag(x_491, 7);
lean_ctor_set(x_491, 1, x_503);
lean_ctor_set(x_491, 0, x_498);
x_504 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_490, x_491, x_6, x_7, x_122, x_9, x_501);
x_505 = lean_ctor_get(x_504, 1);
lean_inc(x_505);
lean_dec(x_504);
x_385 = x_2;
x_386 = x_3;
x_387 = x_4;
x_388 = x_5;
x_389 = x_6;
x_390 = x_7;
x_391 = x_122;
x_392 = x_9;
x_393 = x_505;
goto block_489;
}
else
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; 
x_506 = lean_ctor_get(x_498, 0);
x_507 = lean_ctor_get(x_498, 1);
lean_inc(x_507);
lean_inc(x_506);
lean_dec(x_498);
x_508 = lean_mk_string_unchecked("", 0, 0);
x_509 = l_Lean_stringToMessageData(x_508);
lean_dec(x_508);
lean_inc(x_509);
x_510 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_510, 0, x_509);
lean_ctor_set(x_510, 1, x_506);
lean_ctor_set_tag(x_491, 7);
lean_ctor_set(x_491, 1, x_509);
lean_ctor_set(x_491, 0, x_510);
x_511 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_490, x_491, x_6, x_7, x_122, x_9, x_507);
x_512 = lean_ctor_get(x_511, 1);
lean_inc(x_512);
lean_dec(x_511);
x_385 = x_2;
x_386 = x_3;
x_387 = x_4;
x_388 = x_5;
x_389 = x_6;
x_390 = x_7;
x_391 = x_122;
x_392 = x_9;
x_393 = x_512;
goto block_489;
}
}
else
{
lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; 
x_513 = lean_ctor_get(x_491, 1);
lean_inc(x_513);
lean_dec(x_491);
lean_inc(x_1);
x_514 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_1, x_2, x_513);
x_515 = lean_ctor_get(x_514, 0);
lean_inc(x_515);
x_516 = lean_ctor_get(x_514, 1);
lean_inc(x_516);
if (lean_is_exclusive(x_514)) {
 lean_ctor_release(x_514, 0);
 lean_ctor_release(x_514, 1);
 x_517 = x_514;
} else {
 lean_dec_ref(x_514);
 x_517 = lean_box(0);
}
x_518 = lean_mk_string_unchecked("", 0, 0);
x_519 = l_Lean_stringToMessageData(x_518);
lean_dec(x_518);
lean_inc(x_519);
if (lean_is_scalar(x_517)) {
 x_520 = lean_alloc_ctor(7, 2, 0);
} else {
 x_520 = x_517;
 lean_ctor_set_tag(x_520, 7);
}
lean_ctor_set(x_520, 0, x_519);
lean_ctor_set(x_520, 1, x_515);
x_521 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_521, 0, x_520);
lean_ctor_set(x_521, 1, x_519);
x_522 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_490, x_521, x_6, x_7, x_122, x_9, x_516);
x_523 = lean_ctor_get(x_522, 1);
lean_inc(x_523);
lean_dec(x_522);
x_385 = x_2;
x_386 = x_3;
x_387 = x_4;
x_388 = x_5;
x_389 = x_6;
x_390 = x_7;
x_391 = x_122;
x_392 = x_9;
x_393 = x_523;
goto block_489;
}
}
block_360:
{
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; 
lean_dec(x_140);
lean_dec(x_136);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
x_142 = lean_mk_string_unchecked("store", 5, 5);
x_143 = l_Lean_Name_mkStr4(x_123, x_124, x_125, x_142);
lean_inc(x_143);
x_144 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_143, x_135, x_138);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_unbox(x_145);
lean_dec(x_145);
if (x_146 == 0)
{
lean_object* x_147; 
lean_dec(x_143);
x_147 = lean_ctor_get(x_144, 1);
lean_inc(x_147);
lean_dec(x_144);
x_11 = x_134;
x_12 = x_126;
x_13 = x_127;
x_14 = x_133;
x_15 = x_137;
x_16 = x_128;
x_17 = x_135;
x_18 = x_139;
x_19 = x_147;
goto block_75;
}
else
{
uint8_t x_148; 
x_148 = !lean_is_exclusive(x_144);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_149 = lean_ctor_get(x_144, 1);
x_150 = lean_ctor_get(x_144, 0);
lean_dec(x_150);
lean_inc(x_126);
x_151 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_126, x_133, x_149);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_151, 1);
x_155 = lean_mk_string_unchecked("", 0, 0);
x_156 = l_Lean_stringToMessageData(x_155);
lean_dec(x_155);
lean_inc(x_156);
lean_ctor_set_tag(x_151, 7);
lean_ctor_set(x_151, 1, x_153);
lean_ctor_set(x_151, 0, x_156);
lean_ctor_set_tag(x_144, 7);
lean_ctor_set(x_144, 1, x_156);
lean_ctor_set(x_144, 0, x_151);
x_157 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_143, x_144, x_137, x_128, x_135, x_139, x_154);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
lean_dec(x_157);
x_11 = x_134;
x_12 = x_126;
x_13 = x_127;
x_14 = x_133;
x_15 = x_137;
x_16 = x_128;
x_17 = x_135;
x_18 = x_139;
x_19 = x_158;
goto block_75;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_159 = lean_ctor_get(x_151, 0);
x_160 = lean_ctor_get(x_151, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_151);
x_161 = lean_mk_string_unchecked("", 0, 0);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
lean_inc(x_162);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_159);
lean_ctor_set_tag(x_144, 7);
lean_ctor_set(x_144, 1, x_162);
lean_ctor_set(x_144, 0, x_163);
x_164 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_143, x_144, x_137, x_128, x_135, x_139, x_160);
x_165 = lean_ctor_get(x_164, 1);
lean_inc(x_165);
lean_dec(x_164);
x_11 = x_134;
x_12 = x_126;
x_13 = x_127;
x_14 = x_133;
x_15 = x_137;
x_16 = x_128;
x_17 = x_135;
x_18 = x_139;
x_19 = x_165;
goto block_75;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_166 = lean_ctor_get(x_144, 1);
lean_inc(x_166);
lean_dec(x_144);
lean_inc(x_126);
x_167 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_126, x_133, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
if (lean_is_exclusive(x_167)) {
 lean_ctor_release(x_167, 0);
 lean_ctor_release(x_167, 1);
 x_170 = x_167;
} else {
 lean_dec_ref(x_167);
 x_170 = lean_box(0);
}
x_171 = lean_mk_string_unchecked("", 0, 0);
x_172 = l_Lean_stringToMessageData(x_171);
lean_dec(x_171);
lean_inc(x_172);
if (lean_is_scalar(x_170)) {
 x_173 = lean_alloc_ctor(7, 2, 0);
} else {
 x_173 = x_170;
 lean_ctor_set_tag(x_173, 7);
}
lean_ctor_set(x_173, 0, x_172);
lean_ctor_set(x_173, 1, x_168);
x_174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_172);
x_175 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_143, x_174, x_137, x_128, x_135, x_139, x_169);
x_176 = lean_ctor_get(x_175, 1);
lean_inc(x_176);
lean_dec(x_175);
x_11 = x_134;
x_12 = x_126;
x_13 = x_127;
x_14 = x_133;
x_15 = x_137;
x_16 = x_128;
x_17 = x_135;
x_18 = x_139;
x_19 = x_176;
goto block_75;
}
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_127);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
x_177 = lean_ctor_get(x_141, 0);
lean_inc(x_177);
lean_dec(x_141);
x_178 = lean_ctor_get(x_177, 1);
lean_inc(x_178);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; 
lean_dec(x_178);
lean_dec(x_140);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_130);
lean_dec(x_126);
x_179 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_box(0), x_177, x_133, x_131, x_129, x_136, x_137, x_128, x_135, x_139, x_138);
lean_dec(x_139);
lean_dec(x_135);
lean_dec(x_128);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_129);
lean_dec(x_131);
lean_dec(x_133);
return x_179;
}
else
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; uint8_t x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_181 = lean_ctor_get(x_178, 0);
x_182 = lean_ctor_get(x_178, 2);
x_183 = lean_ctor_get(x_178, 1);
lean_dec(x_183);
x_184 = lean_ctor_get(x_177, 0);
lean_inc(x_184);
x_185 = lean_int_mul(x_130, x_184);
x_186 = lean_int_mul(x_181, x_132);
x_187 = l_Lean_Meta_Grind_Arith_gcdExt(x_185, x_186);
lean_dec(x_186);
lean_dec(x_185);
x_188 = lean_ctor_get(x_187, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 0);
lean_inc(x_189);
lean_dec(x_187);
x_190 = lean_ctor_get(x_188, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_int_mul(x_190, x_184);
lean_dec(x_190);
lean_inc(x_140);
x_193 = l_Int_Linear_Poly_mul(x_140, x_192);
lean_dec(x_192);
x_194 = lean_int_mul(x_191, x_132);
lean_dec(x_191);
lean_inc(x_182);
x_195 = l_Int_Linear_Poly_mul(x_182, x_194);
lean_dec(x_194);
x_196 = lean_st_ref_take(x_133, x_138);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
lean_dec(x_196);
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
x_201 = lean_ctor_get(x_197, 2);
lean_inc(x_201);
x_202 = lean_ctor_get(x_197, 3);
lean_inc(x_202);
x_203 = lean_ctor_get(x_197, 4);
lean_inc(x_203);
x_204 = lean_ctor_get(x_197, 5);
lean_inc(x_204);
x_205 = lean_ctor_get(x_197, 6);
lean_inc(x_205);
x_206 = lean_ctor_get(x_197, 7);
lean_inc(x_206);
x_207 = lean_ctor_get_uint8(x_197, sizeof(void*)*16);
x_208 = lean_ctor_get(x_197, 8);
lean_inc(x_208);
x_209 = lean_ctor_get(x_197, 9);
lean_inc(x_209);
x_210 = lean_ctor_get(x_197, 10);
lean_inc(x_210);
x_211 = lean_ctor_get(x_197, 11);
lean_inc(x_211);
x_212 = lean_ctor_get(x_197, 12);
lean_inc(x_212);
x_213 = lean_ctor_get(x_197, 13);
lean_inc(x_213);
x_214 = lean_ctor_get(x_197, 14);
lean_inc(x_214);
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
x_219 = lean_ctor_get(x_216, 2);
lean_inc(x_219);
x_220 = lean_ctor_get(x_216, 3);
lean_inc(x_220);
x_221 = lean_ctor_get(x_216, 4);
lean_inc(x_221);
x_222 = lean_ctor_get(x_216, 5);
lean_inc(x_222);
x_223 = lean_box(0);
x_224 = l_Lean_PersistentArray_set(lean_box(0), x_222, x_134, x_223);
x_225 = lean_ctor_get(x_216, 6);
lean_inc(x_225);
x_226 = lean_ctor_get(x_216, 7);
lean_inc(x_226);
x_227 = lean_ctor_get(x_216, 8);
lean_inc(x_227);
x_228 = lean_ctor_get(x_216, 9);
lean_inc(x_228);
x_229 = lean_ctor_get(x_216, 10);
lean_inc(x_229);
x_230 = lean_ctor_get(x_216, 11);
lean_inc(x_230);
x_231 = lean_ctor_get(x_216, 12);
lean_inc(x_231);
x_232 = lean_ctor_get(x_216, 13);
lean_inc(x_232);
x_233 = lean_ctor_get_uint8(x_216, sizeof(void*)*17);
x_234 = lean_ctor_get(x_216, 14);
lean_inc(x_234);
x_235 = lean_ctor_get(x_216, 15);
lean_inc(x_235);
x_236 = lean_ctor_get(x_216, 16);
lean_inc(x_236);
lean_dec(x_216);
x_237 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_237, 0, x_217);
lean_ctor_set(x_237, 1, x_218);
lean_ctor_set(x_237, 2, x_219);
lean_ctor_set(x_237, 3, x_220);
lean_ctor_set(x_237, 4, x_221);
lean_ctor_set(x_237, 5, x_224);
lean_ctor_set(x_237, 6, x_225);
lean_ctor_set(x_237, 7, x_226);
lean_ctor_set(x_237, 8, x_227);
lean_ctor_set(x_237, 9, x_228);
lean_ctor_set(x_237, 10, x_229);
lean_ctor_set(x_237, 11, x_230);
lean_ctor_set(x_237, 12, x_231);
lean_ctor_set(x_237, 13, x_232);
lean_ctor_set(x_237, 14, x_234);
lean_ctor_set(x_237, 15, x_235);
lean_ctor_set(x_237, 16, x_236);
lean_ctor_set_uint8(x_237, sizeof(void*)*17, x_233);
x_238 = lean_ctor_get(x_214, 2);
lean_inc(x_238);
lean_dec(x_214);
x_239 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_239, 0, x_215);
lean_ctor_set(x_239, 1, x_237);
lean_ctor_set(x_239, 2, x_238);
x_240 = lean_ctor_get(x_197, 15);
lean_inc(x_240);
lean_dec(x_197);
x_241 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_241, 0, x_199);
lean_ctor_set(x_241, 1, x_200);
lean_ctor_set(x_241, 2, x_201);
lean_ctor_set(x_241, 3, x_202);
lean_ctor_set(x_241, 4, x_203);
lean_ctor_set(x_241, 5, x_204);
lean_ctor_set(x_241, 6, x_205);
lean_ctor_set(x_241, 7, x_206);
lean_ctor_set(x_241, 8, x_208);
lean_ctor_set(x_241, 9, x_209);
lean_ctor_set(x_241, 10, x_210);
lean_ctor_set(x_241, 11, x_211);
lean_ctor_set(x_241, 12, x_212);
lean_ctor_set(x_241, 13, x_213);
lean_ctor_set(x_241, 14, x_239);
lean_ctor_set(x_241, 15, x_240);
lean_ctor_set_uint8(x_241, sizeof(void*)*16, x_207);
x_242 = lean_st_ref_set(x_133, x_241, x_198);
x_243 = !lean_is_exclusive(x_242);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_244 = lean_ctor_get(x_242, 1);
x_245 = lean_ctor_get(x_242, 0);
lean_dec(x_245);
x_246 = l_Int_Linear_Poly_combine(x_193, x_195);
x_247 = lean_int_mul(x_132, x_184);
lean_dec(x_184);
lean_dec(x_132);
lean_inc(x_189);
lean_ctor_set(x_178, 2, x_246);
lean_ctor_set(x_178, 1, x_134);
lean_ctor_set(x_178, 0, x_189);
lean_inc(x_177);
lean_inc(x_126);
lean_ctor_set_tag(x_242, 4);
lean_ctor_set(x_242, 1, x_177);
lean_ctor_set(x_242, 0, x_126);
x_248 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_178);
lean_ctor_set(x_248, 2, x_242);
lean_inc(x_139);
lean_inc(x_135);
lean_inc(x_128);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_129);
lean_inc(x_131);
lean_inc(x_133);
x_249 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_248, x_133, x_131, x_129, x_136, x_137, x_128, x_135, x_139, x_244);
if (lean_obj_tag(x_249) == 0)
{
uint8_t x_250; 
x_250 = !lean_is_exclusive(x_249);
if (x_250 == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_251 = lean_ctor_get(x_249, 1);
x_252 = lean_ctor_get(x_249, 0);
lean_dec(x_252);
x_253 = l_Int_Linear_Poly_mul(x_140, x_181);
lean_dec(x_181);
x_254 = lean_int_neg(x_130);
lean_dec(x_130);
x_255 = l_Int_Linear_Poly_mul(x_182, x_254);
lean_dec(x_254);
x_256 = l_Int_Linear_Poly_combine(x_253, x_255);
lean_ctor_set_tag(x_249, 5);
lean_ctor_set(x_249, 1, x_177);
lean_ctor_set(x_249, 0, x_126);
x_257 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_257, 0, x_189);
lean_ctor_set(x_257, 1, x_256);
lean_ctor_set(x_257, 2, x_249);
x_1 = x_257;
x_2 = x_133;
x_3 = x_131;
x_4 = x_129;
x_5 = x_136;
x_6 = x_137;
x_7 = x_128;
x_8 = x_135;
x_9 = x_139;
x_10 = x_251;
goto _start;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_259 = lean_ctor_get(x_249, 1);
lean_inc(x_259);
lean_dec(x_249);
x_260 = l_Int_Linear_Poly_mul(x_140, x_181);
lean_dec(x_181);
x_261 = lean_int_neg(x_130);
lean_dec(x_130);
x_262 = l_Int_Linear_Poly_mul(x_182, x_261);
lean_dec(x_261);
x_263 = l_Int_Linear_Poly_combine(x_260, x_262);
x_264 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_264, 0, x_126);
lean_ctor_set(x_264, 1, x_177);
x_265 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_265, 0, x_189);
lean_ctor_set(x_265, 1, x_263);
lean_ctor_set(x_265, 2, x_264);
x_1 = x_265;
x_2 = x_133;
x_3 = x_131;
x_4 = x_129;
x_5 = x_136;
x_6 = x_137;
x_7 = x_128;
x_8 = x_135;
x_9 = x_139;
x_10 = x_259;
goto _start;
}
}
else
{
lean_dec(x_189);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
return x_249;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_267 = lean_ctor_get(x_242, 1);
lean_inc(x_267);
lean_dec(x_242);
x_268 = l_Int_Linear_Poly_combine(x_193, x_195);
x_269 = lean_int_mul(x_132, x_184);
lean_dec(x_184);
lean_dec(x_132);
lean_inc(x_189);
lean_ctor_set(x_178, 2, x_268);
lean_ctor_set(x_178, 1, x_134);
lean_ctor_set(x_178, 0, x_189);
lean_inc(x_177);
lean_inc(x_126);
x_270 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_270, 0, x_126);
lean_ctor_set(x_270, 1, x_177);
x_271 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_271, 0, x_269);
lean_ctor_set(x_271, 1, x_178);
lean_ctor_set(x_271, 2, x_270);
lean_inc(x_139);
lean_inc(x_135);
lean_inc(x_128);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_129);
lean_inc(x_131);
lean_inc(x_133);
x_272 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_271, x_133, x_131, x_129, x_136, x_137, x_128, x_135, x_139, x_267);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_273 = lean_ctor_get(x_272, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_274 = x_272;
} else {
 lean_dec_ref(x_272);
 x_274 = lean_box(0);
}
x_275 = l_Int_Linear_Poly_mul(x_140, x_181);
lean_dec(x_181);
x_276 = lean_int_neg(x_130);
lean_dec(x_130);
x_277 = l_Int_Linear_Poly_mul(x_182, x_276);
lean_dec(x_276);
x_278 = l_Int_Linear_Poly_combine(x_275, x_277);
if (lean_is_scalar(x_274)) {
 x_279 = lean_alloc_ctor(5, 2, 0);
} else {
 x_279 = x_274;
 lean_ctor_set_tag(x_279, 5);
}
lean_ctor_set(x_279, 0, x_126);
lean_ctor_set(x_279, 1, x_177);
x_280 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_280, 0, x_189);
lean_ctor_set(x_280, 1, x_278);
lean_ctor_set(x_280, 2, x_279);
x_1 = x_280;
x_2 = x_133;
x_3 = x_131;
x_4 = x_129;
x_5 = x_136;
x_6 = x_137;
x_7 = x_128;
x_8 = x_135;
x_9 = x_139;
x_10 = x_273;
goto _start;
}
else
{
lean_dec(x_189);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_177);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
return x_272;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; uint8_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; uint8_t x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; 
x_282 = lean_ctor_get(x_178, 0);
x_283 = lean_ctor_get(x_178, 2);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_178);
x_284 = lean_ctor_get(x_177, 0);
lean_inc(x_284);
x_285 = lean_int_mul(x_130, x_284);
x_286 = lean_int_mul(x_282, x_132);
x_287 = l_Lean_Meta_Grind_Arith_gcdExt(x_285, x_286);
lean_dec(x_286);
lean_dec(x_285);
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
lean_dec(x_287);
x_290 = lean_ctor_get(x_288, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_288, 1);
lean_inc(x_291);
lean_dec(x_288);
x_292 = lean_int_mul(x_290, x_284);
lean_dec(x_290);
lean_inc(x_140);
x_293 = l_Int_Linear_Poly_mul(x_140, x_292);
lean_dec(x_292);
x_294 = lean_int_mul(x_291, x_132);
lean_dec(x_291);
lean_inc(x_283);
x_295 = l_Int_Linear_Poly_mul(x_283, x_294);
lean_dec(x_294);
x_296 = lean_st_ref_take(x_133, x_138);
x_297 = lean_ctor_get(x_296, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_296, 1);
lean_inc(x_298);
lean_dec(x_296);
x_299 = lean_ctor_get(x_297, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
x_301 = lean_ctor_get(x_297, 2);
lean_inc(x_301);
x_302 = lean_ctor_get(x_297, 3);
lean_inc(x_302);
x_303 = lean_ctor_get(x_297, 4);
lean_inc(x_303);
x_304 = lean_ctor_get(x_297, 5);
lean_inc(x_304);
x_305 = lean_ctor_get(x_297, 6);
lean_inc(x_305);
x_306 = lean_ctor_get(x_297, 7);
lean_inc(x_306);
x_307 = lean_ctor_get_uint8(x_297, sizeof(void*)*16);
x_308 = lean_ctor_get(x_297, 8);
lean_inc(x_308);
x_309 = lean_ctor_get(x_297, 9);
lean_inc(x_309);
x_310 = lean_ctor_get(x_297, 10);
lean_inc(x_310);
x_311 = lean_ctor_get(x_297, 11);
lean_inc(x_311);
x_312 = lean_ctor_get(x_297, 12);
lean_inc(x_312);
x_313 = lean_ctor_get(x_297, 13);
lean_inc(x_313);
x_314 = lean_ctor_get(x_297, 14);
lean_inc(x_314);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_316, 2);
lean_inc(x_319);
x_320 = lean_ctor_get(x_316, 3);
lean_inc(x_320);
x_321 = lean_ctor_get(x_316, 4);
lean_inc(x_321);
x_322 = lean_ctor_get(x_316, 5);
lean_inc(x_322);
x_323 = lean_box(0);
x_324 = l_Lean_PersistentArray_set(lean_box(0), x_322, x_134, x_323);
x_325 = lean_ctor_get(x_316, 6);
lean_inc(x_325);
x_326 = lean_ctor_get(x_316, 7);
lean_inc(x_326);
x_327 = lean_ctor_get(x_316, 8);
lean_inc(x_327);
x_328 = lean_ctor_get(x_316, 9);
lean_inc(x_328);
x_329 = lean_ctor_get(x_316, 10);
lean_inc(x_329);
x_330 = lean_ctor_get(x_316, 11);
lean_inc(x_330);
x_331 = lean_ctor_get(x_316, 12);
lean_inc(x_331);
x_332 = lean_ctor_get(x_316, 13);
lean_inc(x_332);
x_333 = lean_ctor_get_uint8(x_316, sizeof(void*)*17);
x_334 = lean_ctor_get(x_316, 14);
lean_inc(x_334);
x_335 = lean_ctor_get(x_316, 15);
lean_inc(x_335);
x_336 = lean_ctor_get(x_316, 16);
lean_inc(x_336);
lean_dec(x_316);
x_337 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_337, 0, x_317);
lean_ctor_set(x_337, 1, x_318);
lean_ctor_set(x_337, 2, x_319);
lean_ctor_set(x_337, 3, x_320);
lean_ctor_set(x_337, 4, x_321);
lean_ctor_set(x_337, 5, x_324);
lean_ctor_set(x_337, 6, x_325);
lean_ctor_set(x_337, 7, x_326);
lean_ctor_set(x_337, 8, x_327);
lean_ctor_set(x_337, 9, x_328);
lean_ctor_set(x_337, 10, x_329);
lean_ctor_set(x_337, 11, x_330);
lean_ctor_set(x_337, 12, x_331);
lean_ctor_set(x_337, 13, x_332);
lean_ctor_set(x_337, 14, x_334);
lean_ctor_set(x_337, 15, x_335);
lean_ctor_set(x_337, 16, x_336);
lean_ctor_set_uint8(x_337, sizeof(void*)*17, x_333);
x_338 = lean_ctor_get(x_314, 2);
lean_inc(x_338);
lean_dec(x_314);
x_339 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_339, 0, x_315);
lean_ctor_set(x_339, 1, x_337);
lean_ctor_set(x_339, 2, x_338);
x_340 = lean_ctor_get(x_297, 15);
lean_inc(x_340);
lean_dec(x_297);
x_341 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_341, 0, x_299);
lean_ctor_set(x_341, 1, x_300);
lean_ctor_set(x_341, 2, x_301);
lean_ctor_set(x_341, 3, x_302);
lean_ctor_set(x_341, 4, x_303);
lean_ctor_set(x_341, 5, x_304);
lean_ctor_set(x_341, 6, x_305);
lean_ctor_set(x_341, 7, x_306);
lean_ctor_set(x_341, 8, x_308);
lean_ctor_set(x_341, 9, x_309);
lean_ctor_set(x_341, 10, x_310);
lean_ctor_set(x_341, 11, x_311);
lean_ctor_set(x_341, 12, x_312);
lean_ctor_set(x_341, 13, x_313);
lean_ctor_set(x_341, 14, x_339);
lean_ctor_set(x_341, 15, x_340);
lean_ctor_set_uint8(x_341, sizeof(void*)*16, x_307);
x_342 = lean_st_ref_set(x_133, x_341, x_298);
x_343 = lean_ctor_get(x_342, 1);
lean_inc(x_343);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 lean_ctor_release(x_342, 1);
 x_344 = x_342;
} else {
 lean_dec_ref(x_342);
 x_344 = lean_box(0);
}
x_345 = l_Int_Linear_Poly_combine(x_293, x_295);
x_346 = lean_int_mul(x_132, x_284);
lean_dec(x_284);
lean_dec(x_132);
lean_inc(x_289);
x_347 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_347, 0, x_289);
lean_ctor_set(x_347, 1, x_134);
lean_ctor_set(x_347, 2, x_345);
lean_inc(x_177);
lean_inc(x_126);
if (lean_is_scalar(x_344)) {
 x_348 = lean_alloc_ctor(4, 2, 0);
} else {
 x_348 = x_344;
 lean_ctor_set_tag(x_348, 4);
}
lean_ctor_set(x_348, 0, x_126);
lean_ctor_set(x_348, 1, x_177);
x_349 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_349, 0, x_346);
lean_ctor_set(x_349, 1, x_347);
lean_ctor_set(x_349, 2, x_348);
lean_inc(x_139);
lean_inc(x_135);
lean_inc(x_128);
lean_inc(x_137);
lean_inc(x_136);
lean_inc(x_129);
lean_inc(x_131);
lean_inc(x_133);
x_350 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_349, x_133, x_131, x_129, x_136, x_137, x_128, x_135, x_139, x_343);
if (lean_obj_tag(x_350) == 0)
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_352 = x_350;
} else {
 lean_dec_ref(x_350);
 x_352 = lean_box(0);
}
x_353 = l_Int_Linear_Poly_mul(x_140, x_282);
lean_dec(x_282);
x_354 = lean_int_neg(x_130);
lean_dec(x_130);
x_355 = l_Int_Linear_Poly_mul(x_283, x_354);
lean_dec(x_354);
x_356 = l_Int_Linear_Poly_combine(x_353, x_355);
if (lean_is_scalar(x_352)) {
 x_357 = lean_alloc_ctor(5, 2, 0);
} else {
 x_357 = x_352;
 lean_ctor_set_tag(x_357, 5);
}
lean_ctor_set(x_357, 0, x_126);
lean_ctor_set(x_357, 1, x_177);
x_358 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_358, 0, x_289);
lean_ctor_set(x_358, 1, x_356);
lean_ctor_set(x_358, 2, x_357);
x_1 = x_358;
x_2 = x_133;
x_3 = x_131;
x_4 = x_129;
x_5 = x_136;
x_6 = x_137;
x_7 = x_128;
x_8 = x_135;
x_9 = x_139;
x_10 = x_351;
goto _start;
}
else
{
lean_dec(x_289);
lean_dec(x_283);
lean_dec(x_282);
lean_dec(x_177);
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_126);
return x_350;
}
}
}
}
}
block_384:
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; uint8_t x_381; 
x_376 = l_Lean_Meta_Grind_Arith_Cutsat_get_x27(x_367, x_368, x_369, x_370, x_371, x_372, x_373, x_374, x_375);
x_377 = lean_ctor_get(x_376, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_376, 1);
lean_inc(x_378);
lean_dec(x_376);
x_379 = lean_ctor_get(x_377, 5);
lean_inc(x_379);
lean_dec(x_377);
x_380 = lean_ctor_get(x_379, 2);
lean_inc(x_380);
x_381 = lean_nat_dec_lt(x_361, x_380);
lean_dec(x_380);
if (x_381 == 0)
{
lean_object* x_382; 
lean_dec(x_379);
x_382 = l_outOfBounds___redArg(x_121);
x_126 = x_362;
x_127 = x_363;
x_128 = x_372;
x_129 = x_369;
x_130 = x_364;
x_131 = x_368;
x_132 = x_365;
x_133 = x_367;
x_134 = x_361;
x_135 = x_373;
x_136 = x_370;
x_137 = x_371;
x_138 = x_378;
x_139 = x_374;
x_140 = x_366;
x_141 = x_382;
goto block_360;
}
else
{
lean_object* x_383; 
x_383 = l_Lean_PersistentArray_get_x21___redArg(x_121, x_379, x_361);
x_126 = x_362;
x_127 = x_363;
x_128 = x_372;
x_129 = x_369;
x_130 = x_364;
x_131 = x_368;
x_132 = x_365;
x_133 = x_367;
x_134 = x_361;
x_135 = x_373;
x_136 = x_370;
x_137 = x_371;
x_138 = x_378;
x_139 = x_374;
x_140 = x_366;
x_141 = x_383;
goto block_360;
}
}
block_489:
{
lean_object* x_394; lean_object* x_395; 
x_394 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_norm(x_1);
lean_inc(x_391);
x_395 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_applySubsts(x_394, x_385, x_386, x_387, x_388, x_389, x_390, x_391, x_392, x_393);
if (lean_obj_tag(x_395) == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; uint8_t x_400; 
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_395, 1);
lean_inc(x_397);
lean_dec(x_395);
x_398 = lean_ctor_get(x_396, 0);
lean_inc(x_398);
x_399 = lean_ctor_get(x_396, 1);
lean_inc(x_399);
lean_inc(x_398);
x_400 = l_Int_Linear_Poly_isUnsatDvd(x_398, x_399);
if (x_400 == 0)
{
uint8_t x_401; 
x_401 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_isTrivial(x_396);
if (x_401 == 0)
{
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_402; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
x_402 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_throwUnexpected(lean_box(0), x_396, x_385, x_386, x_387, x_388, x_389, x_390, x_391, x_392, x_397);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_385);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; uint8_t x_410; uint8_t x_411; uint8_t x_412; 
x_403 = lean_ctor_get(x_399, 0);
lean_inc(x_403);
x_404 = lean_ctor_get(x_399, 1);
lean_inc(x_404);
x_405 = lean_ctor_get(x_399, 2);
lean_inc(x_405);
lean_inc(x_396);
x_406 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_satisfied___redArg(x_396, x_385, x_397);
x_407 = lean_ctor_get(x_406, 0);
lean_inc(x_407);
x_408 = lean_ctor_get(x_406, 1);
lean_inc(x_408);
lean_dec(x_406);
x_409 = lean_box(0);
x_410 = lean_unbox(x_407);
lean_dec(x_407);
x_411 = lean_unbox(x_409);
x_412 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_410, x_411);
if (x_412 == 0)
{
x_361 = x_404;
x_362 = x_396;
x_363 = x_399;
x_364 = x_403;
x_365 = x_398;
x_366 = x_405;
x_367 = x_385;
x_368 = x_386;
x_369 = x_387;
x_370 = x_388;
x_371 = x_389;
x_372 = x_390;
x_373 = x_391;
x_374 = x_392;
x_375 = x_408;
goto block_384;
}
else
{
lean_object* x_413; lean_object* x_414; 
x_413 = l_Lean_Meta_Grind_Arith_Cutsat_resetAssignmentFrom___redArg(x_404, x_385, x_408);
x_414 = lean_ctor_get(x_413, 1);
lean_inc(x_414);
lean_dec(x_413);
x_361 = x_404;
x_362 = x_396;
x_363 = x_399;
x_364 = x_403;
x_365 = x_398;
x_366 = x_405;
x_367 = x_385;
x_368 = x_386;
x_369 = x_387;
x_370 = x_388;
x_371 = x_389;
x_372 = x_390;
x_373 = x_391;
x_374 = x_392;
x_375 = x_414;
goto block_384;
}
}
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; uint8_t x_419; 
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_386);
x_415 = lean_mk_string_unchecked("trivial", 7, 7);
x_416 = l_Lean_Name_mkStr4(x_123, x_124, x_125, x_415);
lean_inc(x_416);
x_417 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_416, x_391, x_397);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
x_419 = lean_unbox(x_418);
lean_dec(x_418);
if (x_419 == 0)
{
lean_object* x_420; 
lean_dec(x_416);
lean_dec(x_396);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_385);
x_420 = lean_ctor_get(x_417, 1);
lean_inc(x_420);
lean_dec(x_417);
x_76 = x_420;
goto block_79;
}
else
{
uint8_t x_421; 
x_421 = !lean_is_exclusive(x_417);
if (x_421 == 0)
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; uint8_t x_425; 
x_422 = lean_ctor_get(x_417, 1);
x_423 = lean_ctor_get(x_417, 0);
lean_dec(x_423);
x_424 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_396, x_385, x_422);
lean_dec(x_385);
x_425 = !lean_is_exclusive(x_424);
if (x_425 == 0)
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
x_426 = lean_ctor_get(x_424, 0);
x_427 = lean_ctor_get(x_424, 1);
x_428 = lean_mk_string_unchecked("", 0, 0);
x_429 = l_Lean_stringToMessageData(x_428);
lean_dec(x_428);
lean_inc(x_429);
lean_ctor_set_tag(x_424, 7);
lean_ctor_set(x_424, 1, x_426);
lean_ctor_set(x_424, 0, x_429);
lean_ctor_set_tag(x_417, 7);
lean_ctor_set(x_417, 1, x_429);
lean_ctor_set(x_417, 0, x_424);
x_430 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_416, x_417, x_389, x_390, x_391, x_392, x_427);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
x_431 = lean_ctor_get(x_430, 1);
lean_inc(x_431);
lean_dec(x_430);
x_76 = x_431;
goto block_79;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; 
x_432 = lean_ctor_get(x_424, 0);
x_433 = lean_ctor_get(x_424, 1);
lean_inc(x_433);
lean_inc(x_432);
lean_dec(x_424);
x_434 = lean_mk_string_unchecked("", 0, 0);
x_435 = l_Lean_stringToMessageData(x_434);
lean_dec(x_434);
lean_inc(x_435);
x_436 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_436, 1, x_432);
lean_ctor_set_tag(x_417, 7);
lean_ctor_set(x_417, 1, x_435);
lean_ctor_set(x_417, 0, x_436);
x_437 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_416, x_417, x_389, x_390, x_391, x_392, x_433);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
x_438 = lean_ctor_get(x_437, 1);
lean_inc(x_438);
lean_dec(x_437);
x_76 = x_438;
goto block_79;
}
}
else
{
lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
x_439 = lean_ctor_get(x_417, 1);
lean_inc(x_439);
lean_dec(x_417);
x_440 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_396, x_385, x_439);
lean_dec(x_385);
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_443 = x_440;
} else {
 lean_dec_ref(x_440);
 x_443 = lean_box(0);
}
x_444 = lean_mk_string_unchecked("", 0, 0);
x_445 = l_Lean_stringToMessageData(x_444);
lean_dec(x_444);
lean_inc(x_445);
if (lean_is_scalar(x_443)) {
 x_446 = lean_alloc_ctor(7, 2, 0);
} else {
 x_446 = x_443;
 lean_ctor_set_tag(x_446, 7);
}
lean_ctor_set(x_446, 0, x_445);
lean_ctor_set(x_446, 1, x_441);
x_447 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_445);
x_448 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_416, x_447, x_389, x_390, x_391, x_392, x_442);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
x_449 = lean_ctor_get(x_448, 1);
lean_inc(x_449);
lean_dec(x_448);
x_76 = x_449;
goto block_79;
}
}
}
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; 
lean_dec(x_399);
lean_dec(x_398);
x_450 = lean_mk_string_unchecked("unsat", 5, 5);
x_451 = l_Lean_Name_mkStr4(x_123, x_124, x_125, x_450);
lean_inc(x_451);
x_452 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Grind_updateLastTag_spec__0___redArg(x_451, x_391, x_397);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
x_454 = lean_unbox(x_453);
lean_dec(x_453);
if (x_454 == 0)
{
lean_object* x_455; 
lean_dec(x_451);
x_455 = lean_ctor_get(x_452, 1);
lean_inc(x_455);
lean_dec(x_452);
x_80 = x_396;
x_81 = x_385;
x_82 = x_386;
x_83 = x_387;
x_84 = x_388;
x_85 = x_389;
x_86 = x_390;
x_87 = x_391;
x_88 = x_392;
x_89 = x_455;
goto block_98;
}
else
{
uint8_t x_456; 
x_456 = !lean_is_exclusive(x_452);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; uint8_t x_460; 
x_457 = lean_ctor_get(x_452, 1);
x_458 = lean_ctor_get(x_452, 0);
lean_dec(x_458);
lean_inc(x_396);
x_459 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_396, x_385, x_457);
x_460 = !lean_is_exclusive(x_459);
if (x_460 == 0)
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; 
x_461 = lean_ctor_get(x_459, 0);
x_462 = lean_ctor_get(x_459, 1);
x_463 = lean_mk_string_unchecked("", 0, 0);
x_464 = l_Lean_stringToMessageData(x_463);
lean_dec(x_463);
lean_inc(x_464);
lean_ctor_set_tag(x_459, 7);
lean_ctor_set(x_459, 1, x_461);
lean_ctor_set(x_459, 0, x_464);
lean_ctor_set_tag(x_452, 7);
lean_ctor_set(x_452, 1, x_464);
lean_ctor_set(x_452, 0, x_459);
x_465 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_451, x_452, x_389, x_390, x_391, x_392, x_462);
x_466 = lean_ctor_get(x_465, 1);
lean_inc(x_466);
lean_dec(x_465);
x_80 = x_396;
x_81 = x_385;
x_82 = x_386;
x_83 = x_387;
x_84 = x_388;
x_85 = x_389;
x_86 = x_390;
x_87 = x_391;
x_88 = x_392;
x_89 = x_466;
goto block_98;
}
else
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_467 = lean_ctor_get(x_459, 0);
x_468 = lean_ctor_get(x_459, 1);
lean_inc(x_468);
lean_inc(x_467);
lean_dec(x_459);
x_469 = lean_mk_string_unchecked("", 0, 0);
x_470 = l_Lean_stringToMessageData(x_469);
lean_dec(x_469);
lean_inc(x_470);
x_471 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_471, 0, x_470);
lean_ctor_set(x_471, 1, x_467);
lean_ctor_set_tag(x_452, 7);
lean_ctor_set(x_452, 1, x_470);
lean_ctor_set(x_452, 0, x_471);
x_472 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_451, x_452, x_389, x_390, x_391, x_392, x_468);
x_473 = lean_ctor_get(x_472, 1);
lean_inc(x_473);
lean_dec(x_472);
x_80 = x_396;
x_81 = x_385;
x_82 = x_386;
x_83 = x_387;
x_84 = x_388;
x_85 = x_389;
x_86 = x_390;
x_87 = x_391;
x_88 = x_392;
x_89 = x_473;
goto block_98;
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; 
x_474 = lean_ctor_get(x_452, 1);
lean_inc(x_474);
lean_dec(x_452);
lean_inc(x_396);
x_475 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_pp___redArg(x_396, x_385, x_474);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
if (lean_is_exclusive(x_475)) {
 lean_ctor_release(x_475, 0);
 lean_ctor_release(x_475, 1);
 x_478 = x_475;
} else {
 lean_dec_ref(x_475);
 x_478 = lean_box(0);
}
x_479 = lean_mk_string_unchecked("", 0, 0);
x_480 = l_Lean_stringToMessageData(x_479);
lean_dec(x_479);
lean_inc(x_480);
if (lean_is_scalar(x_478)) {
 x_481 = lean_alloc_ctor(7, 2, 0);
} else {
 x_481 = x_478;
 lean_ctor_set_tag(x_481, 7);
}
lean_ctor_set(x_481, 0, x_480);
lean_ctor_set(x_481, 1, x_476);
x_482 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_482, 0, x_481);
lean_ctor_set(x_482, 1, x_480);
x_483 = l_Lean_addTrace___at___Lean_Meta_Grind_updateLastTag_spec__1___redArg(x_451, x_482, x_389, x_390, x_391, x_392, x_477);
x_484 = lean_ctor_get(x_483, 1);
lean_inc(x_484);
lean_dec(x_483);
x_80 = x_396;
x_81 = x_385;
x_82 = x_386;
x_83 = x_387;
x_84 = x_388;
x_85 = x_389;
x_86 = x_390;
x_87 = x_391;
x_88 = x_392;
x_89 = x_484;
goto block_98;
}
}
}
}
else
{
uint8_t x_485; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_389);
lean_dec(x_388);
lean_dec(x_387);
lean_dec(x_386);
lean_dec(x_385);
lean_dec(x_125);
lean_dec(x_124);
lean_dec(x_123);
x_485 = !lean_is_exclusive(x_395);
if (x_485 == 0)
{
return x_395;
}
else
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_486 = lean_ctor_get(x_395, 0);
x_487 = lean_ctor_get(x_395, 1);
lean_inc(x_487);
lean_inc(x_486);
lean_dec(x_395);
x_488 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
return x_488;
}
}
}
}
else
{
uint8_t x_524; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_524 = !lean_is_exclusive(x_103);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; 
x_525 = lean_ctor_get(x_103, 0);
lean_dec(x_525);
x_526 = lean_box(0);
lean_ctor_set(x_103, 0, x_526);
return x_103;
}
else
{
lean_object* x_527; lean_object* x_528; lean_object* x_529; 
x_527 = lean_ctor_get(x_103, 1);
lean_inc(x_527);
lean_dec(x_103);
x_528 = lean_box(0);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set(x_529, 1, x_527);
return x_529;
}
}
}
else
{
lean_object* x_530; lean_object* x_531; 
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_1);
x_530 = lean_ctor_get(x_8, 5);
lean_inc(x_530);
x_531 = l_Lean_throwMaxRecDepthAt___at___Lean_Meta_Grind_Arith_Cutsat_assertDenoteAsIntNonneg_spec__0(lean_box(0), x_530, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_531;
}
block_75:
{
lean_object* x_20; 
x_20 = l_Int_Linear_Poly_updateOccs___redArg(x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_14, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 3);
lean_inc(x_28);
x_29 = lean_ctor_get(x_23, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_23, 6);
lean_inc(x_31);
x_32 = lean_ctor_get(x_23, 7);
lean_inc(x_32);
x_33 = lean_ctor_get_uint8(x_23, sizeof(void*)*16);
x_34 = lean_ctor_get(x_23, 8);
lean_inc(x_34);
x_35 = lean_ctor_get(x_23, 9);
lean_inc(x_35);
x_36 = lean_ctor_get(x_23, 10);
lean_inc(x_36);
x_37 = lean_ctor_get(x_23, 11);
lean_inc(x_37);
x_38 = lean_ctor_get(x_23, 12);
lean_inc(x_38);
x_39 = lean_ctor_get(x_23, 13);
lean_inc(x_39);
x_40 = lean_ctor_get(x_23, 14);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 3);
lean_inc(x_46);
x_47 = lean_ctor_get(x_42, 4);
lean_inc(x_47);
x_48 = lean_ctor_get(x_42, 5);
lean_inc(x_48);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_12);
x_50 = l_Lean_PersistentArray_set(lean_box(0), x_48, x_11, x_49);
lean_dec(x_11);
x_51 = lean_ctor_get(x_42, 6);
lean_inc(x_51);
x_52 = lean_ctor_get(x_42, 7);
lean_inc(x_52);
x_53 = lean_ctor_get(x_42, 8);
lean_inc(x_53);
x_54 = lean_ctor_get(x_42, 9);
lean_inc(x_54);
x_55 = lean_ctor_get(x_42, 10);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 11);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 12);
lean_inc(x_57);
x_58 = lean_ctor_get(x_42, 13);
lean_inc(x_58);
x_59 = lean_ctor_get_uint8(x_42, sizeof(void*)*17);
x_60 = lean_ctor_get(x_42, 14);
lean_inc(x_60);
x_61 = lean_ctor_get(x_42, 15);
lean_inc(x_61);
x_62 = lean_ctor_get(x_42, 16);
lean_inc(x_62);
lean_dec(x_42);
x_63 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_63, 0, x_43);
lean_ctor_set(x_63, 1, x_44);
lean_ctor_set(x_63, 2, x_45);
lean_ctor_set(x_63, 3, x_46);
lean_ctor_set(x_63, 4, x_47);
lean_ctor_set(x_63, 5, x_50);
lean_ctor_set(x_63, 6, x_51);
lean_ctor_set(x_63, 7, x_52);
lean_ctor_set(x_63, 8, x_53);
lean_ctor_set(x_63, 9, x_54);
lean_ctor_set(x_63, 10, x_55);
lean_ctor_set(x_63, 11, x_56);
lean_ctor_set(x_63, 12, x_57);
lean_ctor_set(x_63, 13, x_58);
lean_ctor_set(x_63, 14, x_60);
lean_ctor_set(x_63, 15, x_61);
lean_ctor_set(x_63, 16, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*17, x_59);
x_64 = lean_ctor_get(x_40, 2);
lean_inc(x_64);
lean_dec(x_40);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_41);
lean_ctor_set(x_65, 1, x_63);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_ctor_get(x_23, 15);
lean_inc(x_66);
lean_dec(x_23);
x_67 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_67, 0, x_25);
lean_ctor_set(x_67, 1, x_26);
lean_ctor_set(x_67, 2, x_27);
lean_ctor_set(x_67, 3, x_28);
lean_ctor_set(x_67, 4, x_29);
lean_ctor_set(x_67, 5, x_30);
lean_ctor_set(x_67, 6, x_31);
lean_ctor_set(x_67, 7, x_32);
lean_ctor_set(x_67, 8, x_34);
lean_ctor_set(x_67, 9, x_35);
lean_ctor_set(x_67, 10, x_36);
lean_ctor_set(x_67, 11, x_37);
lean_ctor_set(x_67, 12, x_38);
lean_ctor_set(x_67, 13, x_39);
lean_ctor_set(x_67, 14, x_65);
lean_ctor_set(x_67, 15, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*16, x_33);
x_68 = lean_st_ref_set(x_14, x_67, x_24);
lean_dec(x_14);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_68, 0);
lean_dec(x_70);
x_71 = lean_box(0);
lean_ctor_set(x_68, 0, x_71);
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
lean_dec(x_68);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_11);
return x_20;
}
}
block_79:
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
block_98:
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_80);
x_91 = l_Lean_Meta_Grind_Arith_Cutsat_setInconsistent(x_90, x_81, x_82, x_83, x_84, x_85, x_86, x_87, x_88, x_89);
if (lean_obj_tag(x_91) == 0)
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_91, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set(x_91, 0, x_94);
return x_91;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_91, 1);
lean_inc(x_95);
lean_dec(x_91);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
return x_91;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_22; uint8_t x_23; 
lean_inc(x_1);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_10);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_22 = l_Lean_Expr_cleanupAnnotations(x_16);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_inc(x_22);
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_inc(x_24);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_inc(x_26);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = l_Lean_Expr_isApp(x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_28);
x_31 = lean_mk_string_unchecked("Dvd", 3, 3);
x_32 = lean_mk_string_unchecked("dvd", 3, 3);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = l_Lean_Expr_isConstOf(x_30, x_33);
lean_dec(x_33);
lean_dec(x_30);
if (x_34 == 0)
{
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_21;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_18);
x_35 = lean_ctor_get(x_26, 1);
lean_inc(x_35);
lean_dec(x_26);
x_36 = l_Lean_Meta_isInstDvdInt___redArg(x_35, x_7, x_17);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
uint8_t x_39; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_36);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_36, 0);
lean_dec(x_40);
x_41 = lean_box(0);
lean_ctor_set(x_36, 0, x_41);
return x_36;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_dec(x_36);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_36, 1);
lean_inc(x_45);
lean_dec(x_36);
x_46 = lean_ctor_get(x_24, 1);
lean_inc(x_46);
lean_dec(x_24);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_46);
x_47 = l_Lean_Meta_getIntValue_x3f(x_46, x_6, x_7, x_8, x_9, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_2);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_51, sizeof(void*)*7 + 10);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_11 = x_53;
goto block_14;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_50);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_55 = lean_ctor_get(x_50, 1);
x_56 = lean_ctor_get(x_50, 0);
lean_dec(x_56);
x_57 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
x_58 = l_Lean_stringToMessageData(x_57);
lean_dec(x_57);
x_59 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_59);
lean_ctor_set(x_50, 0, x_58);
x_60 = lean_mk_string_unchecked("", 0, 0);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_50);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Lean_Meta_Grind_reportIssue(x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_55);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = lean_ctor_get(x_63, 1);
lean_inc(x_64);
lean_dec(x_63);
x_11 = x_64;
goto block_14;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_50, 1);
lean_inc(x_65);
lean_dec(x_50);
x_66 = lean_mk_string_unchecked("non-linear divisibility constraint found", 40, 40);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = l_Lean_indentExpr(x_1);
x_69 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("", 0, 0);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
x_72 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_71);
x_73 = l_Lean_Meta_Grind_reportIssue(x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_65);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_11 = x_74;
goto block_14;
}
}
}
else
{
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_47, 1);
lean_inc(x_75);
lean_dec(x_47);
x_76 = !lean_is_exclusive(x_48);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_48, 0);
lean_inc(x_1);
x_78 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_75);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_unbox(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_free_object(x_48);
lean_dec(x_77);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
lean_dec(x_78);
x_82 = lean_ctor_get(x_22, 1);
lean_inc(x_82);
lean_dec(x_22);
lean_inc(x_1);
x_83 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; uint8_t x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
uint8_t x_86; 
lean_dec(x_82);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_83, 0, x_88);
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_dec(x_83);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_93 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_mk_string_unchecked("Int", 3, 3);
x_97 = lean_mk_string_unchecked("Linear", 6, 6);
x_98 = lean_mk_string_unchecked("of_not_dvd", 10, 10);
x_99 = l_Lean_Name_mkStr3(x_96, x_97, x_98);
x_100 = lean_box(0);
x_101 = l_Lean_Expr_const___override(x_99, x_100);
x_102 = l_Lean_reflBoolTrue;
x_103 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_94);
x_104 = l_Lean_mkApp4(x_101, x_46, x_82, x_102, x_103);
x_105 = lean_unsigned_to_nat(0u);
x_106 = l_Lean_Meta_Grind_pushNewFact(x_104, x_105, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_95);
return x_106;
}
else
{
uint8_t x_107; 
lean_dec(x_82);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_107 = !lean_is_exclusive(x_93);
if (x_107 == 0)
{
return x_93;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_93, 0);
x_109 = lean_ctor_get(x_93, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_93);
x_110 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
}
}
}
else
{
uint8_t x_111; 
lean_dec(x_82);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = !lean_is_exclusive(x_83);
if (x_111 == 0)
{
return x_83;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_83, 0);
x_113 = lean_ctor_get(x_83, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_83);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_46);
x_115 = lean_ctor_get(x_78, 1);
lean_inc(x_115);
lean_dec(x_78);
x_116 = lean_ctor_get(x_22, 1);
lean_inc(x_116);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_117 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_116, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_115);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
lean_ctor_set_tag(x_48, 0);
lean_ctor_set(x_48, 0, x_1);
x_120 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_120, 0, x_77);
lean_ctor_set(x_120, 1, x_118);
lean_ctor_set(x_120, 2, x_48);
x_121 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_120, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_119);
return x_121;
}
else
{
uint8_t x_122; 
lean_free_object(x_48);
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_122 = !lean_is_exclusive(x_117);
if (x_122 == 0)
{
return x_117;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_123 = lean_ctor_get(x_117, 0);
x_124 = lean_ctor_get(x_117, 1);
lean_inc(x_124);
lean_inc(x_123);
lean_dec(x_117);
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
lean_free_object(x_48);
lean_dec(x_77);
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_78);
if (x_126 == 0)
{
return x_78;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_78, 0);
x_128 = lean_ctor_get(x_78, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_78);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_48, 0);
lean_inc(x_130);
lean_dec(x_48);
lean_inc(x_1);
x_131 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_75);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; uint8_t x_133; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_unbox(x_132);
lean_dec(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_130);
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_ctor_get(x_22, 1);
lean_inc(x_135);
lean_dec(x_22);
lean_inc(x_1);
x_136 = l_Lean_Meta_Grind_isEqFalse(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_134);
if (lean_obj_tag(x_136) == 0)
{
lean_object* x_137; uint8_t x_138; 
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_135);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_140 = x_136;
} else {
 lean_dec_ref(x_136);
 x_140 = lean_box(0);
}
x_141 = lean_box(0);
if (lean_is_scalar(x_140)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_140;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_139);
return x_142;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_136, 1);
lean_inc(x_143);
lean_dec(x_136);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_144 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_143);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_mk_string_unchecked("Int", 3, 3);
x_148 = lean_mk_string_unchecked("Linear", 6, 6);
x_149 = lean_mk_string_unchecked("of_not_dvd", 10, 10);
x_150 = l_Lean_Name_mkStr3(x_147, x_148, x_149);
x_151 = lean_box(0);
x_152 = l_Lean_Expr_const___override(x_150, x_151);
x_153 = l_Lean_reflBoolTrue;
x_154 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_145);
x_155 = l_Lean_mkApp4(x_152, x_46, x_135, x_153, x_154);
x_156 = lean_unsigned_to_nat(0u);
x_157 = l_Lean_Meta_Grind_pushNewFact(x_155, x_156, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_146);
return x_157;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_135);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_158 = lean_ctor_get(x_144, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_144, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_160 = x_144;
} else {
 lean_dec_ref(x_144);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_dec(x_135);
lean_dec(x_46);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_162 = lean_ctor_get(x_136, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_136, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_164 = x_136;
} else {
 lean_dec_ref(x_136);
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
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_46);
x_166 = lean_ctor_get(x_131, 1);
lean_inc(x_166);
lean_dec(x_131);
x_167 = lean_ctor_get(x_22, 1);
lean_inc(x_167);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_168 = l_Lean_Meta_Grind_Arith_Cutsat_toPoly(x_167, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_166);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_171, 0, x_1);
x_172 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_172, 0, x_130);
lean_ctor_set(x_172, 1, x_169);
lean_ctor_set(x_172, 2, x_171);
x_173 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_172, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_170);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_130);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_174 = lean_ctor_get(x_168, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_168, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_176 = x_168;
} else {
 lean_dec_ref(x_168);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_130);
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_178 = lean_ctor_get(x_131, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_131, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_180 = x_131;
} else {
 lean_dec_ref(x_131);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_47);
if (x_182 == 0)
{
return x_47;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_47, 0);
x_184 = lean_ctor_get(x_47, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_47);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
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
block_21:
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_box(0);
if (lean_is_scalar(x_18)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_18;
}
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_11 = l_Int_OfNat_toIntDvd_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_19 = lean_ctor_get(x_12, 0);
lean_inc(x_19);
lean_dec(x_12);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_dec(x_11);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = l_Lean_Meta_Grind_getGeneration___redArg(x_1, x_2, x_20);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_27 = l_Lean_Meta_Grind_Arith_Cutsat_getForeignVars(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_25);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_22);
x_30 = l_Int_OfNat_Expr_denoteAsIntExpr___redArg(x_28, x_22, x_5, x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_33 = l_Lean_Meta_Grind_Arith_Cutsat_toLinearExpr(x_31, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_1);
x_36 = l_Lean_Meta_Grind_isEqTrue___redArg(x_1, x_2, x_5, x_8, x_9, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_47; uint8_t x_48; 
lean_dec(x_34);
lean_dec(x_22);
lean_dec(x_21);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
lean_inc(x_1);
x_40 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_7, x_39);
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
x_47 = l_Lean_Expr_cleanupAnnotations(x_41);
x_48 = l_Lean_Expr_isApp(x_47);
if (x_48 == 0)
{
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_46;
}
else
{
lean_object* x_49; uint8_t x_50; 
lean_inc(x_47);
x_49 = l_Lean_Expr_appFnCleanup___redArg(x_47);
x_50 = l_Lean_Expr_isApp(x_49);
if (x_50 == 0)
{
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_46;
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_inc(x_49);
x_51 = l_Lean_Expr_appFnCleanup___redArg(x_49);
x_52 = l_Lean_Expr_isApp(x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_46;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = l_Lean_Expr_appFnCleanup___redArg(x_51);
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_46;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_53);
x_56 = lean_mk_string_unchecked("Dvd", 3, 3);
x_57 = lean_mk_string_unchecked("dvd", 3, 3);
x_58 = l_Lean_Name_mkStr2(x_56, x_57);
x_59 = l_Lean_Expr_isConstOf(x_55, x_58);
lean_dec(x_58);
lean_dec(x_55);
if (x_59 == 0)
{
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
goto block_46;
}
else
{
lean_object* x_60; 
lean_dec(x_43);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_60 = l_Lean_Meta_Grind_mkEqFalseProof(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_42);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_ctor_get(x_47, 1);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_ctor_get(x_49, 1);
lean_inc(x_64);
lean_dec(x_49);
x_65 = lean_mk_string_unchecked("Nat", 3, 3);
x_66 = lean_mk_string_unchecked("emod_pos_of_not_dvd", 19, 19);
x_67 = l_Lean_Name_mkStr2(x_65, x_66);
x_68 = lean_box(0);
x_69 = l_Lean_Expr_const___override(x_67, x_68);
x_70 = l_Lean_Meta_mkOfEqFalseCore(x_1, x_61);
x_71 = l_Lean_mkApp3(x_69, x_64, x_63, x_70);
x_72 = lean_unsigned_to_nat(0u);
x_73 = l_Lean_Meta_Grind_pushNewFact(x_71, x_72, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_62);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_74 = !lean_is_exclusive(x_60);
if (x_74 == 0)
{
return x_60;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_60, 0);
x_76 = lean_ctor_get(x_60, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_60);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
}
}
block_46:
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_box(0);
if (lean_is_scalar(x_43)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_43;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_78 = lean_ctor_get(x_36, 1);
lean_inc(x_78);
lean_dec(x_36);
x_79 = l_Int_Linear_Expr_norm(x_34);
lean_inc(x_21);
x_80 = lean_nat_to_int(x_21);
x_81 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_21);
lean_ctor_set(x_81, 2, x_22);
lean_ctor_set(x_81, 3, x_34);
x_82 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_82, 2, x_81);
x_83 = l_Lean_Meta_Grind_Arith_Cutsat_DvdCnstr_assert(x_82, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_78);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_dec(x_34);
lean_dec(x_22);
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
x_84 = !lean_is_exclusive(x_36);
if (x_84 == 0)
{
return x_36;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_36, 0);
x_86 = lean_ctor_get(x_36, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_36);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_22);
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
x_88 = !lean_is_exclusive(x_33);
if (x_88 == 0)
{
return x_33;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_33, 0);
x_90 = lean_ctor_get(x_33, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_33);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_11);
if (x_92 == 0)
{
return x_11;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_11, 0);
x_94 = lean_ctor_get(x_11, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_11);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
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
goto block_17;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = l_Lean_Expr_isApp(x_22);
if (x_23 == 0)
{
lean_dec(x_22);
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
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_Expr_appFnCleanup___redArg(x_22);
x_25 = l_Lean_Expr_isApp(x_24);
if (x_25 == 0)
{
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
goto block_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_inc(x_24);
x_26 = l_Lean_Expr_appFnCleanup___redArg(x_24);
x_27 = lean_mk_string_unchecked("Dvd", 3, 3);
x_28 = lean_mk_string_unchecked("dvd", 3, 3);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_26, x_29);
lean_dec(x_29);
lean_dec(x_26);
if (x_30 == 0)
{
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
goto block_17;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_14);
x_31 = lean_ctor_get(x_24, 1);
lean_inc(x_31);
lean_dec(x_24);
x_32 = lean_mk_string_unchecked("Nat", 3, 3);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Lean_Expr_isConstOf(x_31, x_33);
lean_dec(x_33);
lean_dec(x_31);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = l_Lean_Meta_Grind_Arith_Cutsat_propagateIntDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Grind_Arith_Cutsat_propagateNatDvd(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
return x_36;
}
}
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Dvd", 3, 3);
x_3 = lean_mk_string_unchecked("dvd", 3, 3);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_Cutsat_propagateDvd), 10, 0);
x_6 = l_Lean_Meta_Grind_registerBuiltinDownwardPropagator(x_4, x_5, x_1);
return x_6;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_PropagatorAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Norm(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Meta_Grind_Arith_Cutsat_propagateDvd_declare__1____x40_Lean_Meta_Tactic_Grind_Arith_Cutsat_DvdCnstr___hyg_2579_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
