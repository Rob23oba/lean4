// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Basic
// Imports: Init.Data.Int.Linear Lean.Util.SortExprs Lean.Meta.Check Lean.Meta.Offset Lean.Meta.IntInstTesters Lean.Meta.AppBuilder Lean.Meta.KExprMap Lean.Data.RArray
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
lean_object* l_Lean_Meta_isInstHAddInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstAddInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_mkIntSub(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntMul(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly;
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstMulInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr;
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Meta_KExprMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getIntValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstHMulInt___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLTInt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___lam__0(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstDvdInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
lean_object* l_Lean_Meta_isInstHSubInt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(lean_object*, lean_object*);
lean_object* l_Int_repr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object*);
lean_object* l_Lean_RArray_ofArray(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instReprPoly__lean;
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstNegInt___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Int_toNat(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLEInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_instReprExpr__lean;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstSubInt___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_neg(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntNeg(lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr_go(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_to_int(x_9);
x_11 = lean_int_dec_eq(x_6, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_7);
x_13 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_1 = x_14;
x_2 = x_8;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_7);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_1 = x_17;
x_2 = x_8;
goto _start;
}
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
lean_dec(x_1);
x_20 = !lean_is_exclusive(x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_2, 0);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_nat_to_int(x_22);
x_24 = lean_int_dec_eq(x_21, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_25, 0, x_19);
lean_ctor_set(x_25, 1, x_2);
return x_25;
}
else
{
lean_free_object(x_2);
lean_dec(x_21);
return x_19;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_int_dec_eq(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_26);
x_31 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_31, 0, x_19);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
else
{
lean_dec(x_26);
return x_19;
}
}
}
else
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_33 = lean_ctor_get(x_1, 0);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_int_dec_eq(x_34, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_35);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set(x_1, 0, x_42);
x_2 = x_36;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_34);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_35);
x_45 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_1, 0, x_45);
x_2 = x_36;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_ctor_get(x_2, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 2);
lean_inc(x_50);
lean_dec(x_2);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_to_int(x_51);
x_53 = lean_int_dec_eq(x_48, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_54, 0, x_49);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_48);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_56, 0, x_47);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_1 = x_57;
x_2 = x_50;
goto _start;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_48);
x_59 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_59, 0, x_49);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_47);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_1 = x_61;
x_2 = x_50;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_toExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Int_Linear_Poly_toExpr_go(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; size_t x_15; size_t x_16; lean_object* x_17; size_t x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_array_get_size(x_4);
x_6 = lean_uint64_of_nat(x_3);
x_7 = lean_unsigned_to_nat(32u);
x_8 = lean_uint64_of_nat(x_7);
x_9 = lean_uint64_shift_right(x_6, x_8);
x_10 = lean_uint64_xor(x_6, x_9);
x_11 = lean_unsigned_to_nat(16u);
x_12 = lean_uint64_of_nat(x_11);
x_13 = lean_uint64_shift_right(x_10, x_12);
x_14 = lean_uint64_xor(x_10, x_13);
x_15 = lean_uint64_to_usize(x_14);
x_16 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_sub(x_16, x_18);
x_20 = lean_usize_land(x_15, x_19);
x_21 = lean_array_uget(x_4, x_20);
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_3, x_21);
lean_dec(x_21);
lean_dec(x_3);
if (lean_obj_tag(x_22) == 0)
{
return x_2;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_2);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 0);
lean_dec(x_24);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
lean_dec(x_22);
lean_ctor_set(x_2, 0, x_25);
return x_2;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
case 2:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_2, 0);
x_30 = lean_ctor_get(x_2, 1);
x_31 = l_Int_Linear_Expr_applyPerm_go(x_1, x_29);
x_32 = l_Int_Linear_Expr_applyPerm_go(x_1, x_30);
lean_ctor_set(x_2, 1, x_32);
lean_ctor_set(x_2, 0, x_31);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_2, 0);
x_34 = lean_ctor_get(x_2, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_2);
x_35 = l_Int_Linear_Expr_applyPerm_go(x_1, x_33);
x_36 = l_Int_Linear_Expr_applyPerm_go(x_1, x_34);
x_37 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
case 3:
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_2);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = l_Int_Linear_Expr_applyPerm_go(x_1, x_39);
x_42 = l_Int_Linear_Expr_applyPerm_go(x_1, x_40);
lean_ctor_set(x_2, 1, x_42);
lean_ctor_set(x_2, 0, x_41);
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_45 = l_Int_Linear_Expr_applyPerm_go(x_1, x_43);
x_46 = l_Int_Linear_Expr_applyPerm_go(x_1, x_44);
x_47 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
case 4:
{
uint8_t x_48; 
x_48 = !lean_is_exclusive(x_2);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_2, 0);
x_50 = l_Int_Linear_Expr_applyPerm_go(x_1, x_49);
lean_ctor_set(x_2, 0, x_50);
return x_2;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
lean_dec(x_2);
x_52 = l_Int_Linear_Expr_applyPerm_go(x_1, x_51);
x_53 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_53, 0, x_52);
return x_53;
}
}
case 5:
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_2, 1);
x_56 = l_Int_Linear_Expr_applyPerm_go(x_1, x_55);
lean_ctor_set(x_2, 1, x_56);
return x_2;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_2);
x_59 = l_Int_Linear_Expr_applyPerm_go(x_1, x_58);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
default: 
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_2);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_2, 0);
x_63 = l_Int_Linear_Expr_applyPerm_go(x_1, x_62);
lean_ctor_set(x_2, 0, x_63);
return x_2;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_2, 0);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_2);
x_66 = l_Int_Linear_Expr_applyPerm_go(x_1, x_64);
x_67 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Int_Linear_Expr_applyPerm_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_applyPerm_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_applyPerm_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Expr_applyPerm(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_30; uint8_t x_31; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_14 = x_1;
} else {
 lean_dec_ref(x_1);
 x_14 = lean_box(0);
}
x_30 = lean_unsigned_to_nat(1024u);
x_31 = lean_nat_dec_le(x_30, x_2);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_to_int(x_32);
x_15 = x_33;
goto block_29;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_nat_to_int(x_34);
x_15 = x_35;
goto block_29;
}
block_29:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_mk_string_unchecked("Int.Linear.Poly.num", 19, 19);
if (lean_is_scalar(x_14)) {
 x_17 = lean_alloc_ctor(3, 1, 0);
} else {
 x_17 = x_14;
 lean_ctor_set_tag(x_17, 3);
}
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_dec_lt(x_13, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Int_repr(x_13);
lean_dec(x_13);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_3 = x_19;
x_4 = x_15;
x_5 = x_24;
goto block_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_unsigned_to_nat(1024u);
x_26 = l_Int_repr(x_13);
lean_dec(x_13);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Repr_addAppParen(x_27, x_25);
x_3 = x_19;
x_4 = x_15;
x_5 = x_28;
goto block_12;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_58; uint8_t x_72; 
x_36 = lean_ctor_get(x_1, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 2);
lean_inc(x_38);
lean_dec(x_1);
x_39 = lean_unsigned_to_nat(1024u);
x_72 = lean_nat_dec_le(x_39, x_2);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_unsigned_to_nat(2u);
x_74 = lean_nat_to_int(x_73);
x_58 = x_74;
goto block_71;
}
else
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_to_int(x_75);
x_58 = x_76;
goto block_71;
}
block_57:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; 
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_41);
x_45 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_41);
x_46 = l___private_Init_Data_Repr_0__Nat_reprFast(x_37);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_41);
x_50 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(x_38, x_39);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_40);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
x_56 = l_Repr_addAppParen(x_54, x_2);
return x_56;
}
block_71:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_59 = lean_mk_string_unchecked("Int.Linear.Poly.add", 19, 19);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_box(1);
x_62 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_unsigned_to_nat(0u);
x_64 = lean_nat_to_int(x_63);
x_65 = lean_int_dec_lt(x_36, x_64);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Int_repr(x_36);
lean_dec(x_36);
x_67 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_67, 0, x_66);
x_40 = x_58;
x_41 = x_61;
x_42 = x_62;
x_43 = x_67;
goto block_57;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = l_Int_repr(x_36);
lean_dec(x_36);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Repr_addAppParen(x_69, x_39);
x_40 = x_58;
x_41 = x_61;
x_42 = x_62;
x_43 = x_70;
goto block_57;
}
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = l_Repr_addAppParen(x_9, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprPoly__lean() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprPoly____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_348____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_40; uint8_t x_41; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_24 = x_1;
} else {
 lean_dec_ref(x_1);
 x_24 = lean_box(0);
}
x_40 = lean_unsigned_to_nat(1024u);
x_41 = lean_nat_dec_le(x_40, x_2);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_to_int(x_42);
x_25 = x_43;
goto block_39;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_to_int(x_44);
x_25 = x_45;
goto block_39;
}
block_39:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_mk_string_unchecked("Int.Linear.Expr.num", 19, 19);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(3, 1, 0);
} else {
 x_27 = x_24;
 lean_ctor_set_tag(x_27, 3);
}
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_nat_to_int(x_30);
x_32 = lean_int_dec_lt(x_23, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Int_repr(x_23);
lean_dec(x_23);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_13 = x_25;
x_14 = x_29;
x_15 = x_34;
goto block_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_unsigned_to_nat(1024u);
x_36 = l_Int_repr(x_23);
lean_dec(x_23);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Repr_addAppParen(x_37, x_35);
x_13 = x_25;
x_14 = x_29;
x_15 = x_38;
goto block_22;
}
}
}
case 1:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_62; uint8_t x_63; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_47 = x_1;
} else {
 lean_dec_ref(x_1);
 x_47 = lean_box(0);
}
x_62 = lean_unsigned_to_nat(1024u);
x_63 = lean_nat_dec_le(x_62, x_2);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_nat_to_int(x_64);
x_48 = x_65;
goto block_61;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_to_int(x_66);
x_48 = x_67;
goto block_61;
}
block_61:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; lean_object* x_60; 
x_49 = lean_mk_string_unchecked("Int.Linear.Expr.var", 19, 19);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(3, 1, 0);
} else {
 x_50 = x_47;
 lean_ctor_set_tag(x_50, 3);
}
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_box(1);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
x_53 = l___private_Init_Data_Repr_0__Nat_reprFast(x_46);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_56, 0, x_48);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_58, 0, x_56);
x_59 = lean_unbox(x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*1, x_59);
x_60 = l_Repr_addAppParen(x_58, x_2);
return x_60;
}
}
case 2:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_88; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_70 = x_1;
} else {
 lean_dec_ref(x_1);
 x_70 = lean_box(0);
}
x_71 = lean_unsigned_to_nat(1024u);
x_88 = lean_nat_dec_le(x_71, x_2);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_to_int(x_89);
x_72 = x_90;
goto block_87;
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_to_int(x_91);
x_72 = x_92;
goto block_87;
}
block_87:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; 
x_73 = lean_mk_string_unchecked("Int.Linear.Expr.add", 19, 19);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_box(1);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(5, 2, 0);
} else {
 x_76 = x_70;
 lean_ctor_set_tag(x_76, 5);
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_68, x_71);
x_78 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_75);
x_80 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_69, x_71);
x_81 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_box(0);
x_84 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_84, 0, x_82);
x_85 = lean_unbox(x_83);
lean_ctor_set_uint8(x_84, sizeof(void*)*1, x_85);
x_86 = l_Repr_addAppParen(x_84, x_2);
return x_86;
}
}
case 3:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_113; 
x_93 = lean_ctor_get(x_1, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_95 = x_1;
} else {
 lean_dec_ref(x_1);
 x_95 = lean_box(0);
}
x_96 = lean_unsigned_to_nat(1024u);
x_113 = lean_nat_dec_le(x_96, x_2);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_unsigned_to_nat(2u);
x_115 = lean_nat_to_int(x_114);
x_97 = x_115;
goto block_112;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_to_int(x_116);
x_97 = x_117;
goto block_112;
}
block_112:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_98 = lean_mk_string_unchecked("Int.Linear.Expr.sub", 19, 19);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_box(1);
if (lean_is_scalar(x_95)) {
 x_101 = lean_alloc_ctor(5, 2, 0);
} else {
 x_101 = x_95;
 lean_ctor_set_tag(x_101, 5);
}
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_93, x_96);
x_103 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
x_105 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_94, x_96);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_107, 0, x_97);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_109, 0, x_107);
x_110 = lean_unbox(x_108);
lean_ctor_set_uint8(x_109, sizeof(void*)*1, x_110);
x_111 = l_Repr_addAppParen(x_109, x_2);
return x_111;
}
}
case 4:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_134; 
x_118 = lean_ctor_get(x_1, 0);
lean_inc(x_118);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_119 = x_1;
} else {
 lean_dec_ref(x_1);
 x_119 = lean_box(0);
}
x_120 = lean_unsigned_to_nat(1024u);
x_134 = lean_nat_dec_le(x_120, x_2);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
x_135 = lean_unsigned_to_nat(2u);
x_136 = lean_nat_to_int(x_135);
x_121 = x_136;
goto block_133;
}
else
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = lean_nat_to_int(x_137);
x_121 = x_138;
goto block_133;
}
block_133:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; 
x_122 = lean_mk_string_unchecked("Int.Linear.Expr.neg", 19, 19);
if (lean_is_scalar(x_119)) {
 x_123 = lean_alloc_ctor(3, 1, 0);
} else {
 x_123 = x_119;
 lean_ctor_set_tag(x_123, 3);
}
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_box(1);
x_125 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_118, x_120);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_128, 0, x_121);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_box(0);
x_130 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_130, 0, x_128);
x_131 = lean_unbox(x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*1, x_131);
x_132 = l_Repr_addAppParen(x_130, x_2);
return x_132;
}
}
case 5:
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_157; uint8_t x_171; 
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_141 = x_1;
} else {
 lean_dec_ref(x_1);
 x_141 = lean_box(0);
}
x_142 = lean_unsigned_to_nat(1024u);
x_171 = lean_nat_dec_le(x_142, x_2);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = lean_unsigned_to_nat(2u);
x_173 = lean_nat_to_int(x_172);
x_157 = x_173;
goto block_170;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_unsigned_to_nat(1u);
x_175 = lean_nat_to_int(x_174);
x_157 = x_175;
goto block_170;
}
block_156:
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; 
if (lean_is_scalar(x_141)) {
 x_147 = lean_alloc_ctor(5, 2, 0);
} else {
 x_147 = x_141;
}
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_143);
x_149 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_140, x_142);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_151, 0, x_144);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_153, 0, x_151);
x_154 = lean_unbox(x_152);
lean_ctor_set_uint8(x_153, sizeof(void*)*1, x_154);
x_155 = l_Repr_addAppParen(x_153, x_2);
return x_155;
}
block_170:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_158 = lean_mk_string_unchecked("Int.Linear.Expr.mulL", 20, 20);
x_159 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_159, 0, x_158);
x_160 = lean_box(1);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_159);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_unsigned_to_nat(0u);
x_163 = lean_nat_to_int(x_162);
x_164 = lean_int_dec_lt(x_139, x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = l_Int_repr(x_139);
lean_dec(x_139);
x_166 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_166, 0, x_165);
x_143 = x_160;
x_144 = x_157;
x_145 = x_161;
x_146 = x_166;
goto block_156;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_167 = l_Int_repr(x_139);
lean_dec(x_139);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = l_Repr_addAppParen(x_168, x_142);
x_143 = x_160;
x_144 = x_157;
x_145 = x_161;
x_146 = x_169;
goto block_156;
}
}
}
default: 
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_197; 
x_176 = lean_ctor_get(x_1, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_1, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_178 = x_1;
} else {
 lean_dec_ref(x_1);
 x_178 = lean_box(0);
}
x_179 = lean_unsigned_to_nat(1024u);
x_197 = lean_nat_dec_le(x_179, x_2);
if (x_197 == 0)
{
lean_object* x_198; lean_object* x_199; 
x_198 = lean_unsigned_to_nat(2u);
x_199 = lean_nat_to_int(x_198);
x_180 = x_199;
goto block_196;
}
else
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_unsigned_to_nat(1u);
x_201 = lean_nat_to_int(x_200);
x_180 = x_201;
goto block_196;
}
block_196:
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_181 = lean_mk_string_unchecked("Int.Linear.Expr.mulR", 20, 20);
x_182 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_182, 0, x_181);
x_183 = lean_box(1);
if (lean_is_scalar(x_178)) {
 x_184 = lean_alloc_ctor(5, 2, 0);
} else {
 x_184 = x_178;
 lean_ctor_set_tag(x_184, 5);
}
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
x_185 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_176, x_179);
x_186 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_183);
x_188 = lean_unsigned_to_nat(0u);
x_189 = lean_nat_to_int(x_188);
x_190 = lean_int_dec_lt(x_177, x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; 
x_191 = l_Int_repr(x_177);
lean_dec(x_177);
x_192 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_192, 0, x_191);
x_3 = x_180;
x_4 = x_187;
x_5 = x_192;
goto block_12;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = l_Int_repr(x_177);
lean_dec(x_177);
x_194 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Repr_addAppParen(x_194, x_179);
x_3 = x_180;
x_4 = x_187;
x_5 = x_195;
goto block_12;
}
}
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = l_Repr_addAppParen(x_9, x_2);
return x_11;
}
block_22:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_19, 0, x_17);
x_20 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*1, x_20);
x_21 = l_Repr_addAppParen(x_19, x_2);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Int_Linear_instReprExpr__lean() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Int_Linear_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Int_Basic___hyg_476____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("Int", 3, 3);
x_4 = lean_mk_string_unchecked("Linear", 6, 6);
x_5 = lean_mk_string_unchecked("Poly", 4, 4);
x_6 = lean_mk_string_unchecked("num", 3, 3);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_dec_le(x_11, x_2);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_mk_string_unchecked("Neg", 3, 3);
x_14 = lean_mk_string_unchecked("neg", 3, 3);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = l_Lean_Level_ofNat(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = l_Lean_Expr_const___override(x_15, x_17);
lean_inc(x_3);
x_19 = l_Lean_Name_mkStr1(x_3);
x_20 = l_Lean_Expr_const___override(x_19, x_8);
x_21 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_22 = l_Lean_Name_mkStr2(x_3, x_21);
x_23 = l_Lean_Expr_const___override(x_22, x_8);
x_24 = lean_int_neg(x_2);
lean_dec(x_2);
x_25 = l_Int_toNat(x_24);
lean_dec(x_24);
x_26 = l_Lean_instToExprInt_mkNat(x_25);
x_27 = l_Lean_mkApp3(x_18, x_20, x_23, x_26);
x_28 = l_Lean_Expr_app___override(x_9, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_29 = l_Int_toNat(x_2);
lean_dec(x_2);
x_30 = l_Lean_instToExprInt_mkNat(x_29);
x_31 = l_Lean_Expr_app___override(x_9, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_mk_string_unchecked("Int", 3, 3);
x_36 = lean_mk_string_unchecked("Linear", 6, 6);
x_37 = lean_mk_string_unchecked("Poly", 4, 4);
x_38 = lean_mk_string_unchecked("add", 3, 3);
lean_inc(x_35);
x_39 = l_Lean_Name_mkStr4(x_35, x_36, x_37, x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Expr_const___override(x_39, x_40);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_to_int(x_47);
x_49 = lean_int_dec_le(x_48, x_32);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_50 = lean_mk_string_unchecked("Neg", 3, 3);
x_51 = lean_mk_string_unchecked("neg", 3, 3);
x_52 = l_Lean_Name_mkStr2(x_50, x_51);
x_53 = l_Lean_Level_ofNat(x_47);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_40);
x_55 = l_Lean_Expr_const___override(x_52, x_54);
lean_inc(x_35);
x_56 = l_Lean_Name_mkStr1(x_35);
x_57 = l_Lean_Expr_const___override(x_56, x_40);
x_58 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_59 = l_Lean_Name_mkStr2(x_35, x_58);
x_60 = l_Lean_Expr_const___override(x_59, x_40);
x_61 = lean_int_neg(x_32);
lean_dec(x_32);
x_62 = l_Int_toNat(x_61);
lean_dec(x_61);
x_63 = l_Lean_instToExprInt_mkNat(x_62);
x_64 = l_Lean_mkApp3(x_55, x_57, x_60, x_63);
x_42 = x_64;
goto block_46;
}
else
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_35);
x_65 = l_Int_toNat(x_32);
lean_dec(x_32);
x_66 = l_Lean_instToExprInt_mkNat(x_65);
x_42 = x_66;
goto block_46;
}
block_46:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = l_Lean_mkNatLit(x_33);
x_44 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_34);
x_45 = l_Lean_mkApp3(x_41, x_42, x_43, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprPoly___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_instToExprPoly___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("Linear", 6, 6);
x_4 = lean_mk_string_unchecked("Poly", 4, 4);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("Int", 3, 3);
x_4 = lean_mk_string_unchecked("Linear", 6, 6);
x_5 = lean_mk_string_unchecked("Expr", 4, 4);
x_6 = lean_mk_string_unchecked("num", 3, 3);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_dec_le(x_11, x_2);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_mk_string_unchecked("Neg", 3, 3);
x_14 = lean_mk_string_unchecked("neg", 3, 3);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = l_Lean_Level_ofNat(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_8);
x_18 = l_Lean_Expr_const___override(x_15, x_17);
lean_inc(x_3);
x_19 = l_Lean_Name_mkStr1(x_3);
x_20 = l_Lean_Expr_const___override(x_19, x_8);
x_21 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_22 = l_Lean_Name_mkStr2(x_3, x_21);
x_23 = l_Lean_Expr_const___override(x_22, x_8);
x_24 = lean_int_neg(x_2);
lean_dec(x_2);
x_25 = l_Int_toNat(x_24);
lean_dec(x_24);
x_26 = l_Lean_instToExprInt_mkNat(x_25);
x_27 = l_Lean_mkApp3(x_18, x_20, x_23, x_26);
x_28 = l_Lean_Expr_app___override(x_9, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
x_29 = l_Int_toNat(x_2);
lean_dec(x_2);
x_30 = l_Lean_instToExprInt_mkNat(x_29);
x_31 = l_Lean_Expr_app___override(x_9, x_30);
return x_31;
}
}
case 1:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
lean_dec(x_1);
x_33 = lean_mk_string_unchecked("Int", 3, 3);
x_34 = lean_mk_string_unchecked("Linear", 6, 6);
x_35 = lean_mk_string_unchecked("Expr", 4, 4);
x_36 = lean_mk_string_unchecked("var", 3, 3);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
x_38 = lean_box(0);
x_39 = l_Lean_Expr_const___override(x_37, x_38);
x_40 = l_Lean_mkNatLit(x_32);
x_41 = l_Lean_Expr_app___override(x_39, x_40);
return x_41;
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_mk_string_unchecked("Int", 3, 3);
x_45 = lean_mk_string_unchecked("Linear", 6, 6);
x_46 = lean_mk_string_unchecked("Expr", 4, 4);
x_47 = lean_mk_string_unchecked("add", 3, 3);
x_48 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_const___override(x_48, x_49);
x_51 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_42);
x_52 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_43);
x_53 = l_Lean_mkAppB(x_50, x_51, x_52);
return x_53;
}
case 3:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
lean_dec(x_1);
x_56 = lean_mk_string_unchecked("Int", 3, 3);
x_57 = lean_mk_string_unchecked("Linear", 6, 6);
x_58 = lean_mk_string_unchecked("Expr", 4, 4);
x_59 = lean_mk_string_unchecked("sub", 3, 3);
x_60 = l_Lean_Name_mkStr4(x_56, x_57, x_58, x_59);
x_61 = lean_box(0);
x_62 = l_Lean_Expr_const___override(x_60, x_61);
x_63 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_54);
x_64 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_55);
x_65 = l_Lean_mkAppB(x_62, x_63, x_64);
return x_65;
}
case 4:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_67 = lean_mk_string_unchecked("Int", 3, 3);
x_68 = lean_mk_string_unchecked("Linear", 6, 6);
x_69 = lean_mk_string_unchecked("Expr", 4, 4);
x_70 = lean_mk_string_unchecked("neg", 3, 3);
x_71 = l_Lean_Name_mkStr4(x_67, x_68, x_69, x_70);
x_72 = lean_box(0);
x_73 = l_Lean_Expr_const___override(x_71, x_72);
x_74 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_66);
x_75 = l_Lean_Expr_app___override(x_73, x_74);
return x_75;
}
case 5:
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_1);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_77 = lean_ctor_get(x_1, 0);
x_78 = lean_ctor_get(x_1, 1);
x_79 = lean_mk_string_unchecked("Int", 3, 3);
x_80 = lean_mk_string_unchecked("Linear", 6, 6);
x_81 = lean_mk_string_unchecked("Expr", 4, 4);
x_82 = lean_mk_string_unchecked("mulL", 4, 4);
lean_inc(x_79);
x_83 = l_Lean_Name_mkStr4(x_79, x_80, x_81, x_82);
x_84 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_83, x_84);
x_90 = lean_unsigned_to_nat(0u);
x_91 = lean_nat_to_int(x_90);
x_92 = lean_int_dec_le(x_91, x_77);
lean_dec(x_91);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_93 = lean_mk_string_unchecked("Neg", 3, 3);
x_94 = lean_mk_string_unchecked("neg", 3, 3);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = l_Lean_Level_ofNat(x_90);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_84);
lean_ctor_set(x_1, 0, x_96);
x_97 = l_Lean_Expr_const___override(x_95, x_1);
lean_inc(x_79);
x_98 = l_Lean_Name_mkStr1(x_79);
x_99 = l_Lean_Expr_const___override(x_98, x_84);
x_100 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_101 = l_Lean_Name_mkStr2(x_79, x_100);
x_102 = l_Lean_Expr_const___override(x_101, x_84);
x_103 = lean_int_neg(x_77);
lean_dec(x_77);
x_104 = l_Int_toNat(x_103);
lean_dec(x_103);
x_105 = l_Lean_instToExprInt_mkNat(x_104);
x_106 = l_Lean_mkApp3(x_97, x_99, x_102, x_105);
x_86 = x_106;
goto block_89;
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_79);
lean_free_object(x_1);
x_107 = l_Int_toNat(x_77);
lean_dec(x_77);
x_108 = l_Lean_instToExprInt_mkNat(x_107);
x_86 = x_108;
goto block_89;
}
block_89:
{
lean_object* x_87; lean_object* x_88; 
x_87 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_78);
x_88 = l_Lean_mkAppB(x_85, x_86, x_87);
return x_88;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_109 = lean_ctor_get(x_1, 0);
x_110 = lean_ctor_get(x_1, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_1);
x_111 = lean_mk_string_unchecked("Int", 3, 3);
x_112 = lean_mk_string_unchecked("Linear", 6, 6);
x_113 = lean_mk_string_unchecked("Expr", 4, 4);
x_114 = lean_mk_string_unchecked("mulL", 4, 4);
lean_inc(x_111);
x_115 = l_Lean_Name_mkStr4(x_111, x_112, x_113, x_114);
x_116 = lean_box(0);
x_117 = l_Lean_Expr_const___override(x_115, x_116);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_nat_to_int(x_122);
x_124 = lean_int_dec_le(x_123, x_109);
lean_dec(x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_mk_string_unchecked("Neg", 3, 3);
x_126 = lean_mk_string_unchecked("neg", 3, 3);
x_127 = l_Lean_Name_mkStr2(x_125, x_126);
x_128 = l_Lean_Level_ofNat(x_122);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_116);
x_130 = l_Lean_Expr_const___override(x_127, x_129);
lean_inc(x_111);
x_131 = l_Lean_Name_mkStr1(x_111);
x_132 = l_Lean_Expr_const___override(x_131, x_116);
x_133 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_134 = l_Lean_Name_mkStr2(x_111, x_133);
x_135 = l_Lean_Expr_const___override(x_134, x_116);
x_136 = lean_int_neg(x_109);
lean_dec(x_109);
x_137 = l_Int_toNat(x_136);
lean_dec(x_136);
x_138 = l_Lean_instToExprInt_mkNat(x_137);
x_139 = l_Lean_mkApp3(x_130, x_132, x_135, x_138);
x_118 = x_139;
goto block_121;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_111);
x_140 = l_Int_toNat(x_109);
lean_dec(x_109);
x_141 = l_Lean_instToExprInt_mkNat(x_140);
x_118 = x_141;
goto block_121;
}
block_121:
{
lean_object* x_119; lean_object* x_120; 
x_119 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_110);
x_120 = l_Lean_mkAppB(x_117, x_118, x_119);
return x_120;
}
}
}
default: 
{
uint8_t x_142; 
x_142 = !lean_is_exclusive(x_1);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_143 = lean_ctor_get(x_1, 0);
x_144 = lean_ctor_get(x_1, 1);
x_145 = lean_mk_string_unchecked("Int", 3, 3);
x_146 = lean_mk_string_unchecked("Linear", 6, 6);
x_147 = lean_mk_string_unchecked("Expr", 4, 4);
x_148 = lean_mk_string_unchecked("mulR", 4, 4);
lean_inc(x_145);
x_149 = l_Lean_Name_mkStr4(x_145, x_146, x_147, x_148);
x_150 = lean_box(0);
x_151 = l_Lean_Expr_const___override(x_149, x_150);
x_152 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_143);
x_153 = lean_unsigned_to_nat(0u);
x_154 = lean_nat_to_int(x_153);
x_155 = lean_int_dec_le(x_154, x_144);
lean_dec(x_154);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_156 = lean_mk_string_unchecked("Neg", 3, 3);
x_157 = lean_mk_string_unchecked("neg", 3, 3);
x_158 = l_Lean_Name_mkStr2(x_156, x_157);
x_159 = l_Lean_Level_ofNat(x_153);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_150);
lean_ctor_set(x_1, 0, x_159);
x_160 = l_Lean_Expr_const___override(x_158, x_1);
lean_inc(x_145);
x_161 = l_Lean_Name_mkStr1(x_145);
x_162 = l_Lean_Expr_const___override(x_161, x_150);
x_163 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_164 = l_Lean_Name_mkStr2(x_145, x_163);
x_165 = l_Lean_Expr_const___override(x_164, x_150);
x_166 = lean_int_neg(x_144);
lean_dec(x_144);
x_167 = l_Int_toNat(x_166);
lean_dec(x_166);
x_168 = l_Lean_instToExprInt_mkNat(x_167);
x_169 = l_Lean_mkApp3(x_160, x_162, x_165, x_168);
x_170 = l_Lean_mkAppB(x_151, x_152, x_169);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_145);
lean_free_object(x_1);
x_171 = l_Int_toNat(x_144);
lean_dec(x_144);
x_172 = l_Lean_instToExprInt_mkNat(x_171);
x_173 = l_Lean_mkAppB(x_151, x_152, x_172);
return x_173;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_174 = lean_ctor_get(x_1, 0);
x_175 = lean_ctor_get(x_1, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_1);
x_176 = lean_mk_string_unchecked("Int", 3, 3);
x_177 = lean_mk_string_unchecked("Linear", 6, 6);
x_178 = lean_mk_string_unchecked("Expr", 4, 4);
x_179 = lean_mk_string_unchecked("mulR", 4, 4);
lean_inc(x_176);
x_180 = l_Lean_Name_mkStr4(x_176, x_177, x_178, x_179);
x_181 = lean_box(0);
x_182 = l_Lean_Expr_const___override(x_180, x_181);
x_183 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_174);
x_184 = lean_unsigned_to_nat(0u);
x_185 = lean_nat_to_int(x_184);
x_186 = lean_int_dec_le(x_185, x_175);
lean_dec(x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_187 = lean_mk_string_unchecked("Neg", 3, 3);
x_188 = lean_mk_string_unchecked("neg", 3, 3);
x_189 = l_Lean_Name_mkStr2(x_187, x_188);
x_190 = l_Lean_Level_ofNat(x_184);
x_191 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_181);
x_192 = l_Lean_Expr_const___override(x_189, x_191);
lean_inc(x_176);
x_193 = l_Lean_Name_mkStr1(x_176);
x_194 = l_Lean_Expr_const___override(x_193, x_181);
x_195 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_196 = l_Lean_Name_mkStr2(x_176, x_195);
x_197 = l_Lean_Expr_const___override(x_196, x_181);
x_198 = lean_int_neg(x_175);
lean_dec(x_175);
x_199 = l_Int_toNat(x_198);
lean_dec(x_198);
x_200 = l_Lean_instToExprInt_mkNat(x_199);
x_201 = l_Lean_mkApp3(x_192, x_194, x_197, x_200);
x_202 = l_Lean_mkAppB(x_182, x_183, x_201);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_176);
x_203 = l_Int_toNat(x_175);
lean_dec(x_175);
x_204 = l_Lean_instToExprInt_mkNat(x_203);
x_205 = l_Lean_mkAppB(x_182, x_183, x_204);
return x_205;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_instToExprExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_instToExprExpr___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = lean_mk_string_unchecked("Linear", 6, 6);
x_4 = lean_mk_string_unchecked("Expr", 4, 4);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_dec_le(x_6, x_4);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_mk_string_unchecked("Neg", 3, 3);
x_9 = lean_mk_string_unchecked("neg", 3, 3);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = l_Lean_Level_ofNat(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Expr_const___override(x_10, x_13);
x_15 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_15);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_12);
x_18 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_19 = l_Lean_Name_mkStr2(x_15, x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_12);
x_21 = lean_int_neg(x_4);
lean_dec(x_4);
x_22 = l_Int_toNat(x_21);
lean_dec(x_21);
x_23 = l_Lean_instToExprInt_mkNat(x_22);
x_24 = l_Lean_mkApp3(x_14, x_17, x_20, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Int_toNat(x_4);
lean_dec(x_4);
x_27 = l_Lean_instToExprInt_mkNat(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
case 1:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_apply_1(x_1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
case 2:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_2, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_dec(x_2);
lean_inc(x_1);
x_34 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_32, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_33, x_36);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = l_Lean_mkIntAdd(x_35, x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = l_Lean_mkIntAdd(x_35, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
case 3:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
lean_dec(x_2);
lean_inc(x_1);
x_47 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_45, x_3);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_46, x_49);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = l_Lean_mkIntSub(x_48, x_52);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_50, 0);
x_55 = lean_ctor_get(x_50, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_50);
x_56 = l_Lean_mkIntSub(x_48, x_54);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
case 4:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_2, 0);
lean_inc(x_58);
lean_dec(x_2);
x_59 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_58, x_3);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = l_Lean_mkIntNeg(x_61);
lean_ctor_set(x_59, 0, x_62);
return x_59;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_59, 0);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_59);
x_65 = l_Lean_mkIntNeg(x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_64);
return x_66;
}
}
case 5:
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_68 = lean_ctor_get(x_2, 0);
x_69 = lean_ctor_get(x_2, 1);
x_70 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_69, x_3);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_to_int(x_78);
x_80 = lean_int_dec_le(x_79, x_68);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_81 = lean_mk_string_unchecked("Neg", 3, 3);
x_82 = lean_mk_string_unchecked("neg", 3, 3);
x_83 = l_Lean_Name_mkStr2(x_81, x_82);
x_84 = l_Lean_Level_ofNat(x_78);
x_85 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_85);
lean_ctor_set(x_2, 0, x_84);
x_86 = l_Lean_Expr_const___override(x_83, x_2);
x_87 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_87);
x_88 = l_Lean_Name_mkStr1(x_87);
x_89 = l_Lean_Expr_const___override(x_88, x_85);
x_90 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_91 = l_Lean_Name_mkStr2(x_87, x_90);
x_92 = l_Lean_Expr_const___override(x_91, x_85);
x_93 = lean_int_neg(x_68);
lean_dec(x_68);
x_94 = l_Int_toNat(x_93);
lean_dec(x_93);
x_95 = l_Lean_instToExprInt_mkNat(x_94);
x_96 = l_Lean_mkApp3(x_86, x_89, x_92, x_95);
x_74 = x_96;
goto block_77;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_free_object(x_2);
x_97 = l_Int_toNat(x_68);
lean_dec(x_68);
x_98 = l_Lean_instToExprInt_mkNat(x_97);
x_74 = x_98;
goto block_77;
}
block_77:
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Lean_mkIntMul(x_74, x_71);
if (lean_is_scalar(x_73)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_73;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_72);
return x_76;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_99 = lean_ctor_get(x_2, 0);
x_100 = lean_ctor_get(x_2, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_2);
x_101 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_100, x_3);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_104 = x_101;
} else {
 lean_dec_ref(x_101);
 x_104 = lean_box(0);
}
x_109 = lean_unsigned_to_nat(0u);
x_110 = lean_nat_to_int(x_109);
x_111 = lean_int_dec_le(x_110, x_99);
lean_dec(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_112 = lean_mk_string_unchecked("Neg", 3, 3);
x_113 = lean_mk_string_unchecked("neg", 3, 3);
x_114 = l_Lean_Name_mkStr2(x_112, x_113);
x_115 = l_Lean_Level_ofNat(x_109);
x_116 = lean_box(0);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_Expr_const___override(x_114, x_117);
x_119 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_119);
x_120 = l_Lean_Name_mkStr1(x_119);
x_121 = l_Lean_Expr_const___override(x_120, x_116);
x_122 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_123 = l_Lean_Name_mkStr2(x_119, x_122);
x_124 = l_Lean_Expr_const___override(x_123, x_116);
x_125 = lean_int_neg(x_99);
lean_dec(x_99);
x_126 = l_Int_toNat(x_125);
lean_dec(x_125);
x_127 = l_Lean_instToExprInt_mkNat(x_126);
x_128 = l_Lean_mkApp3(x_118, x_121, x_124, x_127);
x_105 = x_128;
goto block_108;
}
else
{
lean_object* x_129; lean_object* x_130; 
x_129 = l_Int_toNat(x_99);
lean_dec(x_99);
x_130 = l_Lean_instToExprInt_mkNat(x_129);
x_105 = x_130;
goto block_108;
}
block_108:
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Lean_mkIntMul(x_105, x_102);
if (lean_is_scalar(x_104)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_104;
}
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_103);
return x_107;
}
}
}
default: 
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_2);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_132 = lean_ctor_get(x_2, 0);
x_133 = lean_ctor_get(x_2, 1);
x_134 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_132, x_3);
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_137 = x_134;
} else {
 lean_dec_ref(x_134);
 x_137 = lean_box(0);
}
x_142 = lean_unsigned_to_nat(0u);
x_143 = lean_nat_to_int(x_142);
x_144 = lean_int_dec_le(x_143, x_133);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_145 = lean_mk_string_unchecked("Neg", 3, 3);
x_146 = lean_mk_string_unchecked("neg", 3, 3);
x_147 = l_Lean_Name_mkStr2(x_145, x_146);
x_148 = l_Lean_Level_ofNat(x_142);
x_149 = lean_box(0);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_149);
lean_ctor_set(x_2, 0, x_148);
x_150 = l_Lean_Expr_const___override(x_147, x_2);
x_151 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_151);
x_152 = l_Lean_Name_mkStr1(x_151);
x_153 = l_Lean_Expr_const___override(x_152, x_149);
x_154 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_155 = l_Lean_Name_mkStr2(x_151, x_154);
x_156 = l_Lean_Expr_const___override(x_155, x_149);
x_157 = lean_int_neg(x_133);
lean_dec(x_133);
x_158 = l_Int_toNat(x_157);
lean_dec(x_157);
x_159 = l_Lean_instToExprInt_mkNat(x_158);
x_160 = l_Lean_mkApp3(x_150, x_153, x_156, x_159);
x_138 = x_160;
goto block_141;
}
else
{
lean_object* x_161; lean_object* x_162; 
lean_free_object(x_2);
x_161 = l_Int_toNat(x_133);
lean_dec(x_133);
x_162 = l_Lean_instToExprInt_mkNat(x_161);
x_138 = x_162;
goto block_141;
}
block_141:
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_mkIntMul(x_135, x_138);
if (lean_is_scalar(x_137)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_137;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_136);
return x_140;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
x_163 = lean_ctor_get(x_2, 0);
x_164 = lean_ctor_get(x_2, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_2);
x_165 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_163, x_3);
x_166 = lean_ctor_get(x_165, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_165, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_165)) {
 lean_ctor_release(x_165, 0);
 lean_ctor_release(x_165, 1);
 x_168 = x_165;
} else {
 lean_dec_ref(x_165);
 x_168 = lean_box(0);
}
x_173 = lean_unsigned_to_nat(0u);
x_174 = lean_nat_to_int(x_173);
x_175 = lean_int_dec_le(x_174, x_164);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_176 = lean_mk_string_unchecked("Neg", 3, 3);
x_177 = lean_mk_string_unchecked("neg", 3, 3);
x_178 = l_Lean_Name_mkStr2(x_176, x_177);
x_179 = l_Lean_Level_ofNat(x_173);
x_180 = lean_box(0);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_179);
lean_ctor_set(x_181, 1, x_180);
x_182 = l_Lean_Expr_const___override(x_178, x_181);
x_183 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_183);
x_184 = l_Lean_Name_mkStr1(x_183);
x_185 = l_Lean_Expr_const___override(x_184, x_180);
x_186 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_187 = l_Lean_Name_mkStr2(x_183, x_186);
x_188 = l_Lean_Expr_const___override(x_187, x_180);
x_189 = lean_int_neg(x_164);
lean_dec(x_164);
x_190 = l_Int_toNat(x_189);
lean_dec(x_189);
x_191 = l_Lean_instToExprInt_mkNat(x_190);
x_192 = l_Lean_mkApp3(x_182, x_185, x_188, x_191);
x_169 = x_192;
goto block_172;
}
else
{
lean_object* x_193; lean_object* x_194; 
x_193 = l_Int_toNat(x_164);
lean_dec(x_164);
x_194 = l_Lean_instToExprInt_mkNat(x_193);
x_169 = x_194;
goto block_172;
}
block_172:
{
lean_object* x_170; lean_object* x_171; 
x_170 = l_Lean_mkIntMul(x_166, x_169);
if (lean_is_scalar(x_168)) {
 x_171 = lean_alloc_ctor(0, 2, 0);
} else {
 x_171 = x_168;
}
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_167);
return x_171;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Expr_denoteExpr___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Expr_denoteExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Expr_denoteExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_dec(x_1);
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_dec_eq(x_9, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_int_dec_le(x_11, x_9);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_mk_string_unchecked("Neg", 3, 3);
x_15 = lean_mk_string_unchecked("neg", 3, 3);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
x_17 = l_Lean_Level_ofNat(x_10);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_Expr_const___override(x_16, x_19);
x_21 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_21);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Expr_const___override(x_22, x_18);
x_24 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_25 = l_Lean_Name_mkStr2(x_21, x_24);
x_26 = l_Lean_Expr_const___override(x_25, x_18);
x_27 = lean_int_neg(x_9);
lean_dec(x_9);
x_28 = l_Int_toNat(x_27);
lean_dec(x_27);
x_29 = l_Lean_instToExprInt_mkNat(x_28);
x_30 = l_Lean_mkApp3(x_20, x_23, x_26, x_29);
x_5 = x_30;
goto block_8;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = l_Int_toNat(x_9);
lean_dec(x_9);
x_32 = l_Lean_instToExprInt_mkNat(x_31);
x_5 = x_32;
goto block_8;
}
}
else
{
lean_object* x_33; 
lean_dec(x_11);
lean_dec(x_9);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_4);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_3, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_3, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 2);
lean_inc(x_36);
lean_dec(x_3);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_int_dec_eq(x_34, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_to_int(x_46);
x_48 = lean_int_dec_le(x_47, x_34);
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_49 = lean_mk_string_unchecked("Neg", 3, 3);
x_50 = lean_mk_string_unchecked("neg", 3, 3);
x_51 = l_Lean_Name_mkStr2(x_49, x_50);
x_52 = l_Lean_Level_ofNat(x_46);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Lean_Expr_const___override(x_51, x_54);
x_56 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_56);
x_57 = l_Lean_Name_mkStr1(x_56);
x_58 = l_Lean_Expr_const___override(x_57, x_53);
x_59 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_60 = l_Lean_Name_mkStr2(x_56, x_59);
x_61 = l_Lean_Expr_const___override(x_60, x_53);
x_62 = lean_int_neg(x_34);
lean_dec(x_34);
x_63 = l_Int_toNat(x_62);
lean_dec(x_62);
x_64 = l_Lean_instToExprInt_mkNat(x_63);
x_65 = l_Lean_mkApp3(x_55, x_58, x_61, x_64);
x_37 = x_65;
goto block_42;
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = l_Int_toNat(x_34);
lean_dec(x_34);
x_67 = l_Lean_instToExprInt_mkNat(x_66);
x_37 = x_67;
goto block_42;
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_34);
lean_inc(x_1);
x_68 = lean_apply_1(x_1, x_35);
x_69 = l_Lean_mkIntAdd(x_2, x_68);
x_2 = x_69;
x_3 = x_36;
goto _start;
}
block_42:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_inc(x_1);
x_38 = lean_apply_1(x_1, x_35);
x_39 = l_Lean_mkIntMul(x_37, x_38);
x_40 = l_Lean_mkIntAdd(x_2, x_39);
x_2 = x_40;
x_3 = x_36;
goto _start;
}
}
block_8:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_mkIntAdd(x_2, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Int_Linear_Poly_denoteExpr_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_dec_le(x_6, x_4);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_8 = lean_mk_string_unchecked("Neg", 3, 3);
x_9 = lean_mk_string_unchecked("neg", 3, 3);
x_10 = l_Lean_Name_mkStr2(x_8, x_9);
x_11 = l_Lean_Level_ofNat(x_5);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Expr_const___override(x_10, x_13);
x_15 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_15);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_12);
x_18 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_19 = l_Lean_Name_mkStr2(x_15, x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_12);
x_21 = lean_int_neg(x_4);
lean_dec(x_4);
x_22 = l_Int_toNat(x_21);
lean_dec(x_21);
x_23 = l_Lean_instToExprInt_mkNat(x_22);
x_24 = l_Lean_mkApp3(x_14, x_17, x_20, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_3);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = l_Int_toNat(x_4);
lean_dec(x_4);
x_27 = l_Lean_instToExprInt_mkNat(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
lean_dec(x_2);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_to_int(x_37);
x_39 = lean_int_dec_eq(x_29, x_38);
lean_dec(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_40 = lean_unsigned_to_nat(0u);
x_41 = lean_nat_to_int(x_40);
x_42 = lean_int_dec_le(x_41, x_29);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_43 = lean_mk_string_unchecked("Neg", 3, 3);
x_44 = lean_mk_string_unchecked("neg", 3, 3);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
x_46 = l_Lean_Level_ofNat(x_40);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_Expr_const___override(x_45, x_48);
x_50 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_50);
x_51 = l_Lean_Name_mkStr1(x_50);
x_52 = l_Lean_Expr_const___override(x_51, x_47);
x_53 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_54 = l_Lean_Name_mkStr2(x_50, x_53);
x_55 = l_Lean_Expr_const___override(x_54, x_47);
x_56 = lean_int_neg(x_29);
lean_dec(x_29);
x_57 = l_Int_toNat(x_56);
lean_dec(x_56);
x_58 = l_Lean_instToExprInt_mkNat(x_57);
x_59 = l_Lean_mkApp3(x_49, x_52, x_55, x_58);
x_32 = x_59;
goto block_36;
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = l_Int_toNat(x_29);
lean_dec(x_29);
x_61 = l_Lean_instToExprInt_mkNat(x_60);
x_32 = x_61;
goto block_36;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_29);
lean_inc(x_1);
x_62 = lean_apply_1(x_1, x_30);
x_63 = l_Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_62, x_31, x_3);
return x_63;
}
block_36:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_inc(x_1);
x_33 = lean_apply_1(x_1, x_30);
x_34 = l_Lean_mkIntMul(x_32, x_33);
x_35 = l_Int_Linear_Poly_denoteExpr_go___redArg(x_1, x_34, x_31, x_3);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Poly_denoteExpr___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_denoteExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Int_Linear_Poly_denoteExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_st_ref_get(x_2, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_12 = l_Lean_Meta_KExprMap_find_x3f(lean_box(0), x_11, x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_st_ref_get(x_2, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_st_ref_get(x_2, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_array_get_size(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_1);
x_25 = l_Lean_Meta_KExprMap_insert(lean_box(0), x_24, x_1, x_23, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = lean_array_push(x_28, x_1);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_26);
x_30 = lean_st_ref_set(x_2, x_18, x_27);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_23);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_23);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_1);
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
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_18, 0);
x_42 = lean_ctor_get(x_18, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_18);
x_43 = lean_ctor_get(x_16, 1);
lean_inc(x_43);
lean_dec(x_16);
x_44 = lean_array_get_size(x_43);
lean_dec(x_43);
x_45 = lean_ctor_get(x_41, 0);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_1);
x_46 = l_Lean_Meta_KExprMap_insert(lean_box(0), x_45, x_1, x_44, x_3, x_4, x_5, x_6, x_42);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_ctor_get(x_41, 1);
lean_inc(x_49);
lean_dec(x_41);
x_50 = lean_array_push(x_49, x_1);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_47);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_st_ref_set(x_2, x_51, x_48);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_52)) {
 lean_ctor_release(x_52, 0);
 lean_ctor_release(x_52, 1);
 x_54 = x_52;
} else {
 lean_dec_ref(x_52);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_44);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_44);
lean_dec(x_41);
lean_dec(x_1);
x_57 = lean_ctor_get(x_46, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_46, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_59 = x_46;
} else {
 lean_dec_ref(x_46);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(1, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_61 = !lean_is_exclusive(x_12);
if (x_61 == 0)
{
lean_object* x_62; uint8_t x_63; 
x_62 = lean_ctor_get(x_12, 0);
lean_dec(x_62);
x_63 = !lean_is_exclusive(x_13);
if (x_63 == 0)
{
return x_12;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_13, 0);
lean_inc(x_64);
lean_dec(x_13);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_12, 0, x_65);
return x_12;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_dec(x_12);
x_67 = lean_ctor_get(x_13, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_68 = x_13;
} else {
 lean_dec_ref(x_13);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 1, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_67);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_66);
return x_70;
}
}
}
else
{
uint8_t x_71; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_12);
if (x_71 == 0)
{
return x_12;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_12, 0);
x_73 = lean_ctor_get(x_12, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_12);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_1);
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_12 = l_Lean_Expr_cleanupAnnotations(x_9);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
x_14 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_17 = lean_mk_string_unchecked("Int", 3, 3);
x_18 = lean_mk_string_unchecked("neg", 3, 3);
lean_inc(x_18);
lean_inc(x_17);
x_19 = l_Lean_Name_mkStr2(x_17, x_18);
x_20 = l_Lean_Expr_isConstOf(x_16, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lean_Expr_isApp(x_16);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
x_22 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
x_67 = l_Lean_Expr_appFnCleanup___redArg(x_16);
x_68 = lean_mk_string_unchecked("mul", 3, 3);
lean_inc(x_68);
lean_inc(x_17);
x_69 = l_Lean_Name_mkStr2(x_17, x_68);
x_70 = l_Lean_Expr_isConstOf(x_67, x_69);
lean_dec(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_mk_string_unchecked("sub", 3, 3);
lean_inc(x_71);
lean_inc(x_17);
x_72 = l_Lean_Name_mkStr2(x_17, x_71);
x_73 = l_Lean_Expr_isConstOf(x_67, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_74 = lean_mk_string_unchecked("add", 3, 3);
lean_inc(x_74);
x_75 = l_Lean_Name_mkStr2(x_17, x_74);
x_76 = l_Lean_Expr_isConstOf(x_67, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
x_77 = l_Lean_Expr_isApp(x_67);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_11);
x_78 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
lean_inc(x_67);
x_79 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_80 = lean_mk_string_unchecked("Neg", 3, 3);
x_81 = l_Lean_Name_mkStr2(x_80, x_18);
x_82 = l_Lean_Expr_isConstOf(x_79, x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_83 = lean_mk_string_unchecked("OfNat", 5, 5);
x_84 = lean_mk_string_unchecked("ofNat", 5, 5);
x_85 = l_Lean_Name_mkStr2(x_83, x_84);
x_86 = l_Lean_Expr_isConstOf(x_79, x_85);
lean_dec(x_85);
if (x_86 == 0)
{
uint8_t x_87; 
x_87 = l_Lean_Expr_isApp(x_79);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_88 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_89 = lean_ctor_get(x_67, 1);
lean_inc(x_89);
lean_dec(x_67);
x_90 = l_Lean_Expr_appFnCleanup___redArg(x_79);
x_91 = lean_mk_string_unchecked("Mul", 3, 3);
x_92 = l_Lean_Name_mkStr2(x_91, x_68);
x_93 = l_Lean_Expr_isConstOf(x_90, x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_94 = lean_mk_string_unchecked("Sub", 3, 3);
x_95 = l_Lean_Name_mkStr2(x_94, x_71);
x_96 = l_Lean_Expr_isConstOf(x_90, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_mk_string_unchecked("Add", 3, 3);
x_98 = l_Lean_Name_mkStr2(x_97, x_74);
x_99 = l_Lean_Expr_isConstOf(x_90, x_98);
lean_dec(x_98);
if (x_99 == 0)
{
uint8_t x_100; 
x_100 = l_Lean_Expr_isApp(x_90);
if (x_100 == 0)
{
lean_object* x_101; 
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_101 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_101;
}
else
{
lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_Expr_appFnCleanup___redArg(x_90);
x_103 = l_Lean_Expr_isApp(x_102);
if (x_103 == 0)
{
lean_object* x_104; 
lean_dec(x_102);
lean_dec(x_89);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_104 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_104;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_105 = l_Lean_Expr_appFnCleanup___redArg(x_102);
x_106 = lean_mk_string_unchecked("HMul", 4, 4);
x_107 = lean_mk_string_unchecked("hMul", 4, 4);
x_108 = l_Lean_Name_mkStr2(x_106, x_107);
x_109 = l_Lean_Expr_isConstOf(x_105, x_108);
lean_dec(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
lean_dec(x_11);
x_110 = lean_mk_string_unchecked("HSub", 4, 4);
x_111 = lean_mk_string_unchecked("hSub", 4, 4);
x_112 = l_Lean_Name_mkStr2(x_110, x_111);
x_113 = l_Lean_Expr_isConstOf(x_105, x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; 
x_114 = lean_mk_string_unchecked("HAdd", 4, 4);
x_115 = lean_mk_string_unchecked("hAdd", 4, 4);
x_116 = l_Lean_Name_mkStr2(x_114, x_115);
x_117 = l_Lean_Expr_isConstOf(x_105, x_116);
lean_dec(x_116);
lean_dec(x_105);
if (x_117 == 0)
{
lean_object* x_118; 
lean_dec(x_89);
lean_dec(x_23);
lean_dec(x_15);
x_118 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = l_Lean_Meta_isInstHAddInt___redArg(x_89, x_4, x_10);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_unbox(x_120);
lean_dec(x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
lean_dec(x_23);
lean_dec(x_15);
x_122 = lean_ctor_get(x_119, 1);
lean_inc(x_122);
lean_dec(x_119);
x_123 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_122);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_124 = lean_ctor_get(x_119, 1);
lean_inc(x_124);
lean_dec(x_119);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_125 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_125) == 0)
{
uint8_t x_126; 
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
x_129 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_128);
if (lean_obj_tag(x_129) == 0)
{
uint8_t x_130; 
x_130 = !lean_is_exclusive(x_129);
if (x_130 == 0)
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_129, 0);
lean_ctor_set_tag(x_125, 2);
lean_ctor_set(x_125, 1, x_131);
lean_ctor_set(x_129, 0, x_125);
return x_129;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_129, 0);
x_133 = lean_ctor_get(x_129, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_129);
lean_ctor_set_tag(x_125, 2);
lean_ctor_set(x_125, 1, x_132);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_125);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
else
{
lean_free_object(x_125);
lean_dec(x_127);
return x_129;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_125, 0);
x_136 = lean_ctor_get(x_125, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_125);
x_137 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_136);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_141, 0, x_135);
lean_ctor_set(x_141, 1, x_138);
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
lean_dec(x_135);
return x_137;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_125;
}
}
}
}
else
{
lean_object* x_143; lean_object* x_144; uint8_t x_145; 
lean_dec(x_105);
x_143 = l_Lean_Meta_isInstHSubInt___redArg(x_89, x_4, x_10);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_unbox(x_144);
lean_dec(x_144);
if (x_145 == 0)
{
lean_object* x_146; lean_object* x_147; 
lean_dec(x_23);
lean_dec(x_15);
x_146 = lean_ctor_get(x_143, 1);
lean_inc(x_146);
lean_dec(x_143);
x_147 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_146);
return x_147;
}
else
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_1);
x_148 = lean_ctor_get(x_143, 1);
lean_inc(x_148);
lean_dec(x_143);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_149 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_148);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_ctor_get(x_149, 1);
x_153 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_152);
if (lean_obj_tag(x_153) == 0)
{
uint8_t x_154; 
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = lean_ctor_get(x_153, 0);
lean_ctor_set_tag(x_149, 3);
lean_ctor_set(x_149, 1, x_155);
lean_ctor_set(x_153, 0, x_149);
return x_153;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_153, 0);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
lean_inc(x_156);
lean_dec(x_153);
lean_ctor_set_tag(x_149, 3);
lean_ctor_set(x_149, 1, x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_149);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
else
{
lean_free_object(x_149);
lean_dec(x_151);
return x_153;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_ctor_get(x_149, 0);
x_160 = lean_ctor_get(x_149, 1);
lean_inc(x_160);
lean_inc(x_159);
lean_dec(x_149);
x_161 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_160);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_165, 0, x_159);
lean_ctor_set(x_165, 1, x_162);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_166, 1, x_163);
return x_166;
}
else
{
lean_dec(x_159);
return x_161;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_149;
}
}
}
}
else
{
lean_object* x_167; lean_object* x_168; uint8_t x_169; 
lean_dec(x_105);
x_167 = l_Lean_Meta_isInstHMulInt___redArg(x_89, x_4, x_10);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_unbox(x_168);
lean_dec(x_168);
if (x_169 == 0)
{
lean_object* x_170; lean_object* x_171; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_170 = lean_ctor_get(x_167, 1);
lean_inc(x_170);
lean_dec(x_167);
x_171 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_170);
return x_171;
}
else
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_167, 1);
lean_inc(x_172);
lean_dec(x_167);
x_24 = x_15;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_172;
goto block_66;
}
}
}
}
}
else
{
lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_90);
lean_dec(x_11);
x_173 = l_Lean_Meta_isInstAddInt___redArg(x_89, x_4, x_10);
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_unbox(x_174);
lean_dec(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; 
lean_dec(x_23);
lean_dec(x_15);
x_176 = lean_ctor_get(x_173, 1);
lean_inc(x_176);
lean_dec(x_173);
x_177 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_176);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; 
lean_dec(x_1);
x_178 = lean_ctor_get(x_173, 1);
lean_inc(x_178);
lean_dec(x_173);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_179 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_178);
if (lean_obj_tag(x_179) == 0)
{
uint8_t x_180; 
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
x_183 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_182);
if (lean_obj_tag(x_183) == 0)
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_183, 0);
lean_ctor_set_tag(x_179, 2);
lean_ctor_set(x_179, 1, x_185);
lean_ctor_set(x_183, 0, x_179);
return x_183;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_183, 0);
x_187 = lean_ctor_get(x_183, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_183);
lean_ctor_set_tag(x_179, 2);
lean_ctor_set(x_179, 1, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_179);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
else
{
lean_free_object(x_179);
lean_dec(x_181);
return x_183;
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_179, 0);
x_190 = lean_ctor_get(x_179, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_179);
x_191 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_194 = x_191;
} else {
 lean_dec_ref(x_191);
 x_194 = lean_box(0);
}
x_195 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_195, 0, x_189);
lean_ctor_set(x_195, 1, x_192);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_193);
return x_196;
}
else
{
lean_dec(x_189);
return x_191;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_179;
}
}
}
}
else
{
lean_object* x_197; lean_object* x_198; uint8_t x_199; 
lean_dec(x_90);
lean_dec(x_74);
lean_dec(x_11);
x_197 = l_Lean_Meta_isInstSubInt___redArg(x_89, x_4, x_10);
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_unbox(x_198);
lean_dec(x_198);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
lean_dec(x_23);
lean_dec(x_15);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
lean_dec(x_197);
x_201 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_1);
x_202 = lean_ctor_get(x_197, 1);
lean_inc(x_202);
lean_dec(x_197);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_203 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_202);
if (lean_obj_tag(x_203) == 0)
{
uint8_t x_204; 
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
x_207 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_206);
if (lean_obj_tag(x_207) == 0)
{
uint8_t x_208; 
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; 
x_209 = lean_ctor_get(x_207, 0);
lean_ctor_set_tag(x_203, 3);
lean_ctor_set(x_203, 1, x_209);
lean_ctor_set(x_207, 0, x_203);
return x_207;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_207, 0);
x_211 = lean_ctor_get(x_207, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_207);
lean_ctor_set_tag(x_203, 3);
lean_ctor_set(x_203, 1, x_210);
x_212 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_212, 0, x_203);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
else
{
lean_free_object(x_203);
lean_dec(x_205);
return x_207;
}
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_203, 0);
x_214 = lean_ctor_get(x_203, 1);
lean_inc(x_214);
lean_inc(x_213);
lean_dec(x_203);
x_215 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_214);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_218 = x_215;
} else {
 lean_dec_ref(x_215);
 x_218 = lean_box(0);
}
x_219 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_219, 0, x_213);
lean_ctor_set(x_219, 1, x_216);
if (lean_is_scalar(x_218)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_218;
}
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_220, 1, x_217);
return x_220;
}
else
{
lean_dec(x_213);
return x_215;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_203;
}
}
}
}
else
{
lean_object* x_221; lean_object* x_222; uint8_t x_223; 
lean_dec(x_90);
lean_dec(x_74);
lean_dec(x_71);
x_221 = l_Lean_Meta_isInstMulInt___redArg(x_89, x_4, x_10);
x_222 = lean_ctor_get(x_221, 0);
lean_inc(x_222);
x_223 = lean_unbox(x_222);
lean_dec(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_224 = lean_ctor_get(x_221, 1);
lean_inc(x_224);
lean_dec(x_221);
x_225 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_224);
return x_225;
}
else
{
lean_object* x_226; 
x_226 = lean_ctor_get(x_221, 1);
lean_inc(x_226);
lean_dec(x_221);
x_24 = x_15;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_226;
goto block_66;
}
}
}
}
else
{
lean_object* x_227; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_227 = l_Lean_Meta_getIntValue_x3f(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_227) == 0)
{
lean_object* x_228; 
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
x_230 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_229);
return x_230;
}
else
{
uint8_t x_231; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_231 = !lean_is_exclusive(x_227);
if (x_231 == 0)
{
lean_object* x_232; uint8_t x_233; 
x_232 = lean_ctor_get(x_227, 0);
lean_dec(x_232);
x_233 = !lean_is_exclusive(x_228);
if (x_233 == 0)
{
lean_ctor_set_tag(x_228, 0);
return x_227;
}
else
{
lean_object* x_234; lean_object* x_235; 
x_234 = lean_ctor_get(x_228, 0);
lean_inc(x_234);
lean_dec(x_228);
x_235 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_227, 0, x_235);
return x_227;
}
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_236 = lean_ctor_get(x_227, 1);
lean_inc(x_236);
lean_dec(x_227);
x_237 = lean_ctor_get(x_228, 0);
lean_inc(x_237);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 x_238 = x_228;
} else {
 lean_dec_ref(x_228);
 x_238 = lean_box(0);
}
if (lean_is_scalar(x_238)) {
 x_239 = lean_alloc_ctor(0, 1, 0);
} else {
 x_239 = x_238;
 lean_ctor_set_tag(x_239, 0);
}
lean_ctor_set(x_239, 0, x_237);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_236);
return x_240;
}
}
}
else
{
uint8_t x_241; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_241 = !lean_is_exclusive(x_227);
if (x_241 == 0)
{
return x_227;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_242 = lean_ctor_get(x_227, 0);
x_243 = lean_ctor_get(x_227, 1);
lean_inc(x_243);
lean_inc(x_242);
lean_dec(x_227);
x_244 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_244, 0, x_242);
lean_ctor_set(x_244, 1, x_243);
return x_244;
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; uint8_t x_247; 
lean_dec(x_79);
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_11);
x_245 = l_Lean_Meta_isInstNegInt___redArg(x_23, x_4, x_10);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_unbox(x_246);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_15);
x_248 = lean_ctor_get(x_245, 1);
lean_inc(x_248);
lean_dec(x_245);
x_249 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_1);
x_250 = lean_ctor_get(x_245, 1);
lean_inc(x_250);
lean_dec(x_245);
x_251 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_250);
if (lean_obj_tag(x_251) == 0)
{
uint8_t x_252; 
x_252 = !lean_is_exclusive(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_251, 0);
x_254 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_251, 0, x_254);
return x_251;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_255 = lean_ctor_get(x_251, 0);
x_256 = lean_ctor_get(x_251, 1);
lean_inc(x_256);
lean_inc(x_255);
lean_dec(x_251);
x_257 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_257, 0, x_255);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_256);
return x_258;
}
}
else
{
return x_251;
}
}
}
}
}
else
{
lean_object* x_259; 
lean_dec(x_74);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_259 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_259) == 0)
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_259);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_259, 0);
x_262 = lean_ctor_get(x_259, 1);
x_263 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_262);
if (lean_obj_tag(x_263) == 0)
{
uint8_t x_264; 
x_264 = !lean_is_exclusive(x_263);
if (x_264 == 0)
{
lean_object* x_265; 
x_265 = lean_ctor_get(x_263, 0);
lean_ctor_set_tag(x_259, 2);
lean_ctor_set(x_259, 1, x_265);
lean_ctor_set(x_263, 0, x_259);
return x_263;
}
else
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_266 = lean_ctor_get(x_263, 0);
x_267 = lean_ctor_get(x_263, 1);
lean_inc(x_267);
lean_inc(x_266);
lean_dec(x_263);
lean_ctor_set_tag(x_259, 2);
lean_ctor_set(x_259, 1, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_259);
lean_ctor_set(x_268, 1, x_267);
return x_268;
}
}
else
{
lean_free_object(x_259);
lean_dec(x_261);
return x_263;
}
}
else
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_269 = lean_ctor_get(x_259, 0);
x_270 = lean_ctor_get(x_259, 1);
lean_inc(x_270);
lean_inc(x_269);
lean_dec(x_259);
x_271 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_270);
if (lean_obj_tag(x_271) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_271, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_271)) {
 lean_ctor_release(x_271, 0);
 lean_ctor_release(x_271, 1);
 x_274 = x_271;
} else {
 lean_dec_ref(x_271);
 x_274 = lean_box(0);
}
x_275 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_275, 0, x_269);
lean_ctor_set(x_275, 1, x_272);
if (lean_is_scalar(x_274)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_274;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_273);
return x_276;
}
else
{
lean_dec(x_269);
return x_271;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_259;
}
}
}
else
{
lean_object* x_277; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_277 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_277) == 0)
{
uint8_t x_278; 
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_277, 0);
x_280 = lean_ctor_get(x_277, 1);
x_281 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_280);
if (lean_obj_tag(x_281) == 0)
{
uint8_t x_282; 
x_282 = !lean_is_exclusive(x_281);
if (x_282 == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_281, 0);
lean_ctor_set_tag(x_277, 3);
lean_ctor_set(x_277, 1, x_283);
lean_ctor_set(x_281, 0, x_277);
return x_281;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_281, 0);
x_285 = lean_ctor_get(x_281, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_281);
lean_ctor_set_tag(x_277, 3);
lean_ctor_set(x_277, 1, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_277);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
else
{
lean_free_object(x_277);
lean_dec(x_279);
return x_281;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_287 = lean_ctor_get(x_277, 0);
x_288 = lean_ctor_get(x_277, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_277);
x_289 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_288);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_290 = lean_ctor_get(x_289, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
x_293 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_293, 0, x_287);
lean_ctor_set(x_293, 1, x_290);
if (lean_is_scalar(x_292)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_292;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_291);
return x_294;
}
else
{
lean_dec(x_287);
return x_289;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_277;
}
}
}
else
{
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_18);
lean_dec(x_17);
x_24 = x_15;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_10;
goto block_66;
}
block_66:
{
lean_object* x_31; 
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_23);
x_31 = l_Lean_Meta_getIntValue_x3f(x_23, x_26, x_27, x_28, x_29, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_34 = l_Lean_Meta_getIntValue_x3f(x_24, x_26, x_27, x_28, x_29, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_23);
lean_dec(x_11);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_25, x_26, x_27, x_28, x_29, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_34, 1);
lean_inc(x_38);
lean_dec(x_34);
x_39 = lean_ctor_get(x_35, 0);
lean_inc(x_39);
lean_dec(x_35);
x_40 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_23, x_25, x_26, x_27, x_28, x_29, x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
if (lean_is_scalar(x_11)) {
 x_43 = lean_alloc_ctor(6, 2, 0);
} else {
 x_43 = x_11;
 lean_ctor_set_tag(x_43, 6);
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
lean_ctor_set(x_40, 0, x_43);
return x_40;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_40, 0);
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_40);
if (lean_is_scalar(x_11)) {
 x_46 = lean_alloc_ctor(6, 2, 0);
} else {
 x_46 = x_11;
 lean_ctor_set_tag(x_46, 6);
}
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_39);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_dec(x_39);
lean_dec(x_11);
return x_40;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_23);
lean_dec(x_1);
x_52 = lean_ctor_get(x_31, 1);
lean_inc(x_52);
lean_dec(x_31);
x_53 = lean_ctor_get(x_32, 0);
lean_inc(x_53);
lean_dec(x_32);
x_54 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_24, x_25, x_26, x_27, x_28, x_29, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
if (lean_is_scalar(x_11)) {
 x_57 = lean_alloc_ctor(5, 2, 0);
} else {
 x_57 = x_11;
 lean_ctor_set_tag(x_57, 5);
}
lean_ctor_set(x_57, 0, x_53);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
if (lean_is_scalar(x_11)) {
 x_60 = lean_alloc_ctor(5, 2, 0);
} else {
 x_60 = x_11;
 lean_ctor_set_tag(x_60, 5);
}
lean_ctor_set(x_60, 0, x_53);
lean_ctor_set(x_60, 1, x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_dec(x_53);
lean_dec(x_11);
return x_54;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_11);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_31);
if (x_62 == 0)
{
return x_31;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_31, 0);
x_64 = lean_ctor_get(x_31, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_31);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
}
}
else
{
lean_object* x_295; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_1);
x_295 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_295) == 0)
{
uint8_t x_296; 
x_296 = !lean_is_exclusive(x_295);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_295, 0);
x_298 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_298, 0, x_297);
lean_ctor_set(x_295, 0, x_298);
return x_295;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_299 = lean_ctor_get(x_295, 0);
x_300 = lean_ctor_get(x_295, 1);
lean_inc(x_300);
lean_inc(x_299);
lean_dec(x_295);
x_301 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_301, 0, x_299);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_300);
return x_302;
}
}
else
{
return x_295;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 5:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
case 10:
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_1 = x_10;
goto _start;
}
default: 
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Arith_Int_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_15 = l_Lean_Expr_cleanupAnnotations(x_9);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = lean_mk_string_unchecked("Eq", 2, 2);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = l_Lean_Expr_isConstOf(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
if (x_24 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
lean_dec(x_11);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_25, x_4, x_10);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = l_Lean_Expr_cleanupAnnotations(x_28);
x_31 = lean_mk_string_unchecked("Int", 3, 3);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = l_Lean_Expr_isConstOf(x_30, x_32);
lean_dec(x_32);
lean_dec(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_34 = lean_box(0);
lean_ctor_set(x_26, 0, x_34);
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_free_object(x_26);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_36 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_35, x_2, x_3, x_4, x_5, x_6, x_29);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_15, 1);
lean_inc(x_40);
lean_dec(x_15);
x_41 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_40, x_2, x_3, x_4, x_5, x_6, x_39);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
switch (lean_obj_tag(x_38)) {
case 0:
{
if (lean_obj_tag(x_42) == 1)
{
lean_object* x_49; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_38);
x_49 = lean_box(0);
lean_ctor_set(x_36, 1, x_43);
lean_ctor_set(x_36, 0, x_49);
return x_36;
}
else
{
lean_free_object(x_36);
goto block_48;
}
}
case 1:
{
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_50; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_38);
x_50 = lean_box(0);
lean_ctor_set(x_36, 1, x_43);
lean_ctor_set(x_36, 0, x_50);
return x_36;
}
case 1:
{
lean_object* x_51; 
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_38);
x_51 = lean_box(0);
lean_ctor_set(x_36, 1, x_43);
lean_ctor_set(x_36, 0, x_51);
return x_36;
}
default: 
{
lean_free_object(x_36);
goto block_48;
}
}
}
default: 
{
lean_free_object(x_36);
goto block_48;
}
}
block_48:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_38);
lean_ctor_set(x_45, 1, x_42);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_45);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_43);
return x_47;
}
}
else
{
uint8_t x_52; 
lean_free_object(x_36);
lean_dec(x_38);
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
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_36, 0);
x_57 = lean_ctor_get(x_36, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_36);
x_58 = lean_ctor_get(x_15, 1);
lean_inc(x_58);
lean_dec(x_15);
x_59 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_58, x_2, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
switch (lean_obj_tag(x_56)) {
case 0:
{
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_56);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_61);
return x_68;
}
else
{
goto block_66;
}
}
case 1:
{
switch (lean_obj_tag(x_60)) {
case 0:
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_56);
x_69 = lean_box(0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_61);
return x_70;
}
case 1:
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_56);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_61);
return x_72;
}
default: 
{
goto block_66;
}
}
}
default: 
{
goto block_66;
}
}
block_66:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_60);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_62)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_62;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
return x_65;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_56);
x_73 = lean_ctor_get(x_59, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_75 = x_59;
} else {
 lean_dec_ref(x_59);
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
}
else
{
uint8_t x_77; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_36);
if (x_77 == 0)
{
return x_36;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_36, 0);
x_79 = lean_ctor_get(x_36, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_36);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_26, 0);
x_82 = lean_ctor_get(x_26, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_26);
x_83 = l_Lean_Expr_cleanupAnnotations(x_81);
x_84 = lean_mk_string_unchecked("Int", 3, 3);
x_85 = l_Lean_Name_mkStr1(x_84);
x_86 = l_Lean_Expr_isConstOf(x_83, x_85);
lean_dec(x_85);
lean_dec(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_82);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_17, 1);
lean_inc(x_89);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_90 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_89, x_2, x_3, x_4, x_5, x_6, x_82);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_15, 1);
lean_inc(x_94);
lean_dec(x_15);
x_95 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_94, x_2, x_3, x_4, x_5, x_6, x_92);
if (lean_obj_tag(x_95) == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
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
switch (lean_obj_tag(x_91)) {
case 0:
{
if (lean_obj_tag(x_96) == 1)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_91);
x_103 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_93;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_97);
return x_104;
}
else
{
lean_dec(x_93);
goto block_102;
}
}
case 1:
{
switch (lean_obj_tag(x_96)) {
case 0:
{
lean_object* x_105; lean_object* x_106; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_91);
x_105 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_93;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_97);
return x_106;
}
case 1:
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_98);
lean_dec(x_96);
lean_dec(x_91);
x_107 = lean_box(0);
if (lean_is_scalar(x_93)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_93;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_97);
return x_108;
}
default: 
{
lean_dec(x_93);
goto block_102;
}
}
}
default: 
{
lean_dec(x_93);
goto block_102;
}
}
block_102:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_91);
lean_ctor_set(x_99, 1, x_96);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
if (lean_is_scalar(x_98)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_98;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_97);
return x_101;
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_93);
lean_dec(x_91);
x_109 = lean_ctor_get(x_95, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_95, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_111 = x_95;
} else {
 lean_dec_ref(x_95);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_113 = lean_ctor_get(x_90, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_90, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_115 = x_90;
} else {
 lean_dec_ref(x_90);
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
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_11;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_15 = l_Lean_Expr_cleanupAnnotations(x_9);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_22 = lean_mk_string_unchecked("Int", 3, 3);
x_23 = lean_mk_string_unchecked("lt", 2, 2);
lean_inc(x_23);
lean_inc(x_22);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_21, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_mk_string_unchecked("le", 2, 2);
lean_inc(x_26);
x_27 = l_Lean_Name_mkStr2(x_22, x_26);
x_28 = l_Lean_Expr_isConstOf(x_21, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = l_Lean_Expr_isApp(x_21);
if (x_29 == 0)
{
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_30; uint8_t x_31; 
lean_inc(x_21);
x_30 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_31 = l_Lean_Expr_isApp(x_30);
if (x_31 == 0)
{
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_21, 1);
lean_inc(x_32);
lean_dec(x_21);
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_30);
x_34 = lean_mk_string_unchecked("GT", 2, 2);
x_35 = lean_mk_string_unchecked("gt", 2, 2);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = l_Lean_Expr_isConstOf(x_33, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_mk_string_unchecked("GE", 2, 2);
x_39 = lean_mk_string_unchecked("ge", 2, 2);
x_40 = l_Lean_Name_mkStr2(x_38, x_39);
x_41 = l_Lean_Expr_isConstOf(x_33, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_mk_string_unchecked("LT", 2, 2);
x_43 = l_Lean_Name_mkStr2(x_42, x_23);
x_44 = l_Lean_Expr_isConstOf(x_33, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_mk_string_unchecked("LE", 2, 2);
x_46 = l_Lean_Name_mkStr2(x_45, x_26);
x_47 = l_Lean_Expr_isConstOf(x_33, x_46);
lean_dec(x_46);
lean_dec(x_33);
if (x_47 == 0)
{
lean_dec(x_32);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
lean_dec(x_11);
x_48 = l_Lean_Meta_isInstLEInt___redArg(x_32, x_4, x_10);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_unbox(x_49);
lean_dec(x_49);
if (x_50 == 0)
{
uint8_t x_51; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_48, 0);
lean_dec(x_52);
x_53 = lean_box(0);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_48, 1);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_48, 1);
lean_inc(x_57);
lean_dec(x_48);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_58 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_59);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_61, 0, x_65);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_61, 0);
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_61);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_59);
lean_ctor_set(x_68, 1, x_66);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
}
else
{
uint8_t x_71; 
lean_dec(x_59);
x_71 = !lean_is_exclusive(x_61);
if (x_71 == 0)
{
return x_61;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_61, 0);
x_73 = lean_ctor_get(x_61, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_61);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
else
{
uint8_t x_75; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_75 = !lean_is_exclusive(x_58);
if (x_75 == 0)
{
return x_58;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_58, 0);
x_77 = lean_ctor_get(x_58, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_58);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_11);
x_79 = l_Lean_Meta_isInstLTInt(x_32, x_3, x_4, x_5, x_6, x_10);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
uint8_t x_82; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_79);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_79, 0);
lean_dec(x_83);
x_84 = lean_box(0);
lean_ctor_set(x_79, 0, x_84);
return x_79;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_dec(x_79);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_89 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_91);
if (lean_obj_tag(x_92) == 0)
{
uint8_t x_93; 
x_93 = !lean_is_exclusive(x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_92, 0);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_nat_to_int(x_95);
x_97 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_97, 0, x_96);
x_98 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_92, 0, x_100);
return x_92;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_92, 0);
x_102 = lean_ctor_get(x_92, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_92);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_to_int(x_103);
x_105 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_106, 0, x_90);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_101);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_102);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_dec(x_90);
x_110 = !lean_is_exclusive(x_92);
if (x_110 == 0)
{
return x_92;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_92, 0);
x_112 = lean_ctor_get(x_92, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_92);
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
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = !lean_is_exclusive(x_89);
if (x_114 == 0)
{
return x_89;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_89, 0);
x_116 = lean_ctor_get(x_89, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_89);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_11);
x_118 = l_Lean_Meta_isInstLEInt___redArg(x_32, x_4, x_10);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_unbox(x_119);
lean_dec(x_119);
if (x_120 == 0)
{
uint8_t x_121; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_118);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_118, 0);
lean_dec(x_122);
x_123 = lean_box(0);
lean_ctor_set(x_118, 0, x_123);
return x_118;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_118, 1);
lean_inc(x_124);
lean_dec(x_118);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_118, 1);
lean_inc(x_127);
lean_dec(x_118);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_128 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_127);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_130);
if (lean_obj_tag(x_131) == 0)
{
uint8_t x_132; 
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_133 = lean_ctor_get(x_131, 0);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_129);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_131, 0, x_135);
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
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_129);
lean_ctor_set(x_138, 1, x_136);
x_139 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_139, 0, x_138);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_137);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_129);
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
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
lean_dec(x_33);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_11);
x_149 = l_Lean_Meta_isInstLTInt(x_32, x_3, x_4, x_5, x_6, x_10);
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_unbox(x_150);
lean_dec(x_150);
if (x_151 == 0)
{
uint8_t x_152; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_152 = !lean_is_exclusive(x_149);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_ctor_get(x_149, 0);
lean_dec(x_153);
x_154 = lean_box(0);
lean_ctor_set(x_149, 0, x_154);
return x_149;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_149, 1);
lean_inc(x_155);
lean_dec(x_149);
x_156 = lean_box(0);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
else
{
lean_object* x_158; lean_object* x_159; 
x_158 = lean_ctor_get(x_149, 1);
lean_inc(x_158);
lean_dec(x_149);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_159 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_161);
if (lean_obj_tag(x_162) == 0)
{
uint8_t x_163; 
x_163 = !lean_is_exclusive(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_164 = lean_ctor_get(x_162, 0);
x_165 = lean_unsigned_to_nat(1u);
x_166 = lean_nat_to_int(x_165);
x_167 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_168, 0, x_160);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_164);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_162, 0, x_170);
return x_162;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_171 = lean_ctor_get(x_162, 0);
x_172 = lean_ctor_get(x_162, 1);
lean_inc(x_172);
lean_inc(x_171);
lean_dec(x_162);
x_173 = lean_unsigned_to_nat(1u);
x_174 = lean_nat_to_int(x_173);
x_175 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_175, 0, x_174);
x_176 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_176, 0, x_160);
lean_ctor_set(x_176, 1, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_171);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_172);
return x_179;
}
}
else
{
uint8_t x_180; 
lean_dec(x_160);
x_180 = !lean_is_exclusive(x_162);
if (x_180 == 0)
{
return x_162;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_181 = lean_ctor_get(x_162, 0);
x_182 = lean_ctor_get(x_162, 1);
lean_inc(x_182);
lean_inc(x_181);
lean_dec(x_162);
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
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_184 = !lean_is_exclusive(x_159);
if (x_184 == 0)
{
return x_159;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_159, 0);
x_186 = lean_ctor_get(x_159, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_159);
x_187 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
return x_187;
}
}
}
}
}
}
}
else
{
lean_object* x_188; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_188 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_188) == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
lean_dec(x_188);
x_191 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_190);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_189);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_195, 0, x_194);
lean_ctor_set(x_191, 0, x_195);
return x_191;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_196 = lean_ctor_get(x_191, 0);
x_197 = lean_ctor_get(x_191, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_191);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_189);
lean_ctor_set(x_198, 1, x_196);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
x_200 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_200, 0, x_199);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
}
else
{
uint8_t x_201; 
lean_dec(x_189);
x_201 = !lean_is_exclusive(x_191);
if (x_201 == 0)
{
return x_191;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_191, 0);
x_203 = lean_ctor_get(x_191, 1);
lean_inc(x_203);
lean_inc(x_202);
lean_dec(x_191);
x_204 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_205 = !lean_is_exclusive(x_188);
if (x_205 == 0)
{
return x_188;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_188, 0);
x_207 = lean_ctor_get(x_188, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_188);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
else
{
lean_object* x_209; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_209 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_209) == 0)
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
lean_dec(x_209);
x_212 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_211);
if (lean_obj_tag(x_212) == 0)
{
uint8_t x_213; 
x_213 = !lean_is_exclusive(x_212);
if (x_213 == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_214 = lean_ctor_get(x_212, 0);
x_215 = lean_unsigned_to_nat(1u);
x_216 = lean_nat_to_int(x_215);
x_217 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_217, 0, x_216);
x_218 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_218, 0, x_210);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_214);
x_220 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set(x_212, 0, x_220);
return x_212;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_221 = lean_ctor_get(x_212, 0);
x_222 = lean_ctor_get(x_212, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_212);
x_223 = lean_unsigned_to_nat(1u);
x_224 = lean_nat_to_int(x_223);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_226, 0, x_210);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set(x_227, 1, x_221);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_222);
return x_229;
}
}
else
{
uint8_t x_230; 
lean_dec(x_210);
x_230 = !lean_is_exclusive(x_212);
if (x_230 == 0)
{
return x_212;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_212, 0);
x_232 = lean_ctor_get(x_212, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_212);
x_233 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_233, 0, x_231);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
}
}
else
{
uint8_t x_234; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_234 = !lean_is_exclusive(x_209);
if (x_234 == 0)
{
return x_209;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; 
x_235 = lean_ctor_get(x_209, 0);
x_236 = lean_ctor_get(x_209, 1);
lean_inc(x_236);
lean_inc(x_235);
lean_dec(x_209);
x_237 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_237, 0, x_235);
lean_ctor_set(x_237, 1, x_236);
return x_237;
}
}
}
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
if (lean_is_scalar(x_11)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_11;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_15; uint8_t x_16; 
x_8 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_4, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_11 = x_8;
} else {
 lean_dec_ref(x_8);
 x_11 = lean_box(0);
}
x_15 = l_Lean_Expr_cleanupAnnotations(x_9);
x_16 = l_Lean_Expr_isApp(x_15);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("Dvd", 3, 3);
x_25 = lean_mk_string_unchecked("dvd", 3, 3);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = l_Lean_Expr_isConstOf(x_23, x_26);
lean_dec(x_26);
lean_dec(x_23);
if (x_27 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
goto block_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = l_Lean_Meta_isInstDvdInt___redArg(x_28, x_4, x_10);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_29, 1);
lean_inc(x_38);
lean_dec(x_29);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_dec(x_17);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_40 = l_Lean_Meta_getIntValue_x3f(x_39, x_3, x_4, x_5, x_6, x_38);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 0)
{
uint8_t x_42; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_40, 0, x_44);
return x_40;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_40, 1);
lean_inc(x_45);
lean_dec(x_40);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_dec(x_40);
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_41, 0);
x_51 = lean_ctor_get(x_15, 1);
lean_inc(x_51);
lean_dec(x_15);
x_52 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_51, x_2, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_52) == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_52, 0);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_41, 0, x_55);
lean_ctor_set(x_52, 0, x_41);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_52, 0);
x_57 = lean_ctor_get(x_52, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_41, 0, x_58);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_41);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_free_object(x_41);
lean_dec(x_50);
x_60 = !lean_is_exclusive(x_52);
if (x_60 == 0)
{
return x_52;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_52, 0);
x_62 = lean_ctor_get(x_52, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_52);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_41, 0);
lean_inc(x_64);
lean_dec(x_41);
x_65 = lean_ctor_get(x_15, 1);
lean_inc(x_65);
lean_dec(x_15);
x_66 = l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr(x_65, x_2, x_3, x_4, x_5, x_6, x_48);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_64);
lean_ctor_set(x_70, 1, x_67);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_70);
if (lean_is_scalar(x_69)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_69;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_68);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_64);
x_73 = lean_ctor_get(x_66, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_66, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_75 = x_66;
} else {
 lean_dec_ref(x_66);
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
}
}
else
{
uint8_t x_77; 
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_40);
if (x_77 == 0)
{
return x_40;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_40, 0);
x_79 = lean_ctor_get(x_40, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_40);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
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
if (lean_is_scalar(x_11)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_11;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_st_mk_ref(x_11, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_16 = lean_apply_6(x_1, x_14, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
lean_ctor_set(x_12, 1, x_22);
lean_ctor_set(x_12, 0, x_17);
lean_ctor_set(x_19, 0, x_12);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_19, 0);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_19);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
lean_ctor_set(x_12, 1, x_25);
lean_ctor_set(x_12, 0, x_17);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_12);
lean_dec(x_14);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
return x_16;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_16, 0);
x_29 = lean_ctor_get(x_16, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_16);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
lean_inc(x_31);
x_33 = lean_apply_6(x_1, x_31, x_2, x_3, x_4, x_5, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_31, x_35);
lean_dec(x_31);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_36)) {
 lean_ctor_release(x_36, 0);
 lean_ctor_release(x_36, 1);
 x_39 = x_36;
} else {
 lean_dec_ref(x_36);
 x_39 = lean_box(0);
}
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_40);
if (lean_is_scalar(x_39)) {
 x_42 = lean_alloc_ctor(0, 2, 0);
} else {
 x_42 = x_39;
}
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_31);
x_43 = lean_ctor_get(x_33, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_45 = x_33;
} else {
 lean_dec_ref(x_33);
 x_45 = lean_box(0);
}
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(1, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_ToLinear_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_toLinearExpr___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_array_get_size(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_8, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = l_Lean_sortExprs(x_12, x_15);
lean_dec(x_12);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = l_Int_Linear_Expr_applyPerm_go(x_22, x_11);
lean_dec(x_22);
lean_ctor_set(x_19, 1, x_21);
lean_ctor_set(x_19, 0, x_23);
lean_ctor_set(x_8, 0, x_19);
return x_8;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_19);
x_26 = l_Int_Linear_Expr_applyPerm_go(x_25, x_11);
lean_dec(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_8, 0, x_27);
return x_8;
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_8);
x_28 = l_Lean_sortExprs(x_12, x_15);
lean_dec(x_12);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_31 = x_28;
} else {
 lean_dec_ref(x_28);
 x_31 = lean_box(0);
}
x_32 = l_Int_Linear_Expr_applyPerm_go(x_30, x_11);
lean_dec(x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_29);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_10);
return x_34;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_8;
}
}
else
{
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Int_Basic_0__Lean_Meta_Simp_Arith_Int_adapter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_2, x_1);
x_9 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_8, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_10);
x_12 = !lean_is_exclusive(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_11, 0);
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
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
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
x_28 = lean_array_get_size(x_23);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_dec_le(x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; uint8_t x_32; 
lean_free_object(x_10);
x_31 = l_Lean_sortExprs(x_23, x_30);
lean_dec(x_23);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = l_Int_Linear_Expr_applyPerm_go(x_34, x_26);
x_36 = l_Int_Linear_Expr_applyPerm_go(x_34, x_27);
lean_dec(x_34);
lean_ctor_set(x_31, 1, x_33);
lean_ctor_set(x_31, 0, x_36);
lean_ctor_set(x_20, 1, x_31);
lean_ctor_set(x_20, 0, x_35);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_37 = lean_ctor_get(x_31, 0);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_31);
x_39 = l_Int_Linear_Expr_applyPerm_go(x_38, x_26);
x_40 = l_Int_Linear_Expr_applyPerm_go(x_38, x_27);
lean_dec(x_38);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_37);
lean_ctor_set(x_20, 1, x_41);
lean_ctor_set(x_20, 0, x_39);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
else
{
lean_ctor_set(x_20, 1, x_23);
lean_ctor_set(x_20, 0, x_27);
lean_ctor_set(x_10, 1, x_20);
lean_ctor_set(x_10, 0, x_26);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_20, 0);
x_43 = lean_ctor_get(x_20, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_20);
x_44 = lean_array_get_size(x_23);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_dec_le(x_44, x_45);
lean_dec(x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_free_object(x_10);
x_47 = l_Lean_sortExprs(x_23, x_46);
lean_dec(x_23);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = l_Int_Linear_Expr_applyPerm_go(x_49, x_42);
x_52 = l_Int_Linear_Expr_applyPerm_go(x_49, x_43);
lean_dec(x_49);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_11, 0, x_54);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_43);
lean_ctor_set(x_55, 1, x_23);
lean_ctor_set(x_10, 1, x_55);
lean_ctor_set(x_10, 0, x_42);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_10, 1);
lean_inc(x_56);
lean_dec(x_10);
x_57 = lean_ctor_get(x_20, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_20, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_59 = x_20;
} else {
 lean_dec_ref(x_20);
 x_59 = lean_box(0);
}
x_60 = lean_array_get_size(x_56);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_dec_le(x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = l_Lean_sortExprs(x_56, x_62);
lean_dec(x_56);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = l_Int_Linear_Expr_applyPerm_go(x_65, x_57);
x_68 = l_Int_Linear_Expr_applyPerm_go(x_65, x_58);
lean_dec(x_65);
if (lean_is_scalar(x_66)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_66;
}
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
if (lean_is_scalar(x_59)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_59;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
lean_ctor_set(x_11, 0, x_70);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
else
{
lean_object* x_71; lean_object* x_72; 
if (lean_is_scalar(x_59)) {
 x_71 = lean_alloc_ctor(0, 2, 0);
} else {
 x_71 = x_59;
}
lean_ctor_set(x_71, 0, x_58);
lean_ctor_set(x_71, 1, x_56);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_57);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_11, 0, x_72);
lean_ctor_set(x_9, 0, x_11);
return x_9;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_73 = lean_ctor_get(x_11, 0);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
lean_dec(x_9);
x_75 = lean_ctor_get(x_10, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_76 = x_10;
} else {
 lean_dec_ref(x_10);
 x_76 = lean_box(0);
}
x_77 = lean_ctor_get(x_73, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_73, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_79 = x_73;
} else {
 lean_dec_ref(x_73);
 x_79 = lean_box(0);
}
x_80 = lean_array_get_size(x_75);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_dec_le(x_80, x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
x_83 = l_Lean_sortExprs(x_75, x_82);
lean_dec(x_75);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_86 = x_83;
} else {
 lean_dec_ref(x_83);
 x_86 = lean_box(0);
}
x_87 = l_Int_Linear_Expr_applyPerm_go(x_85, x_77);
x_88 = l_Int_Linear_Expr_applyPerm_go(x_85, x_78);
lean_dec(x_85);
if (lean_is_scalar(x_86)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_86;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
if (lean_is_scalar(x_79)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_79;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
lean_ctor_set(x_11, 0, x_90);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_11);
lean_ctor_set(x_91, 1, x_74);
return x_91;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_scalar(x_79)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_79;
}
lean_ctor_set(x_92, 0, x_78);
lean_ctor_set(x_92, 1, x_75);
if (lean_is_scalar(x_76)) {
 x_93 = lean_alloc_ctor(0, 2, 0);
} else {
 x_93 = x_76;
}
lean_ctor_set(x_93, 0, x_77);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_11, 0, x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_11);
lean_ctor_set(x_94, 1, x_74);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_95 = lean_ctor_get(x_11, 0);
lean_inc(x_95);
lean_dec(x_11);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_97 = x_9;
} else {
 lean_dec_ref(x_9);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_10, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_99 = x_10;
} else {
 lean_dec_ref(x_10);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_95, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_95, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_95)) {
 lean_ctor_release(x_95, 0);
 lean_ctor_release(x_95, 1);
 x_102 = x_95;
} else {
 lean_dec_ref(x_95);
 x_102 = lean_box(0);
}
x_103 = lean_array_get_size(x_98);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_dec_le(x_103, x_104);
lean_dec(x_103);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_99);
x_106 = l_Lean_sortExprs(x_98, x_105);
lean_dec(x_98);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = l_Int_Linear_Expr_applyPerm_go(x_108, x_100);
x_111 = l_Int_Linear_Expr_applyPerm_go(x_108, x_101);
lean_dec(x_108);
if (lean_is_scalar(x_109)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_109;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_107);
if (lean_is_scalar(x_102)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_102;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
if (lean_is_scalar(x_97)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_97;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_96);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
if (lean_is_scalar(x_102)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_102;
}
lean_ctor_set(x_116, 0, x_101);
lean_ctor_set(x_116, 1, x_98);
if (lean_is_scalar(x_99)) {
 x_117 = lean_alloc_ctor(0, 2, 0);
} else {
 x_117 = x_99;
}
lean_ctor_set(x_117, 0, x_100);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_117);
if (lean_is_scalar(x_97)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_97;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_96);
return x_119;
}
}
}
}
else
{
uint8_t x_120; 
x_120 = !lean_is_exclusive(x_9);
if (x_120 == 0)
{
return x_9;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_9, 0);
x_122 = lean_ctor_get(x_9, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_9);
x_123 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_123, 0, x_121);
lean_ctor_set(x_123, 1, x_122);
return x_123;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_eqCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_array_get_size(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_free_object(x_9);
x_30 = l_Lean_sortExprs(x_22, x_29);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Int_Linear_Expr_applyPerm_go(x_33, x_25);
x_35 = l_Int_Linear_Expr_applyPerm_go(x_33, x_26);
lean_dec(x_33);
lean_ctor_set(x_30, 1, x_32);
lean_ctor_set(x_30, 0, x_35);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = l_Int_Linear_Expr_applyPerm_go(x_37, x_25);
x_39 = l_Int_Linear_Expr_applyPerm_go(x_37, x_26);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_38);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_array_get_size(x_22);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_9);
x_46 = l_Lean_sortExprs(x_22, x_45);
lean_dec(x_22);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Int_Linear_Expr_applyPerm_go(x_48, x_41);
x_51 = l_Int_Linear_Expr_applyPerm_go(x_48, x_42);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_10, 0, x_53);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_22);
lean_ctor_set(x_9, 1, x_54);
lean_ctor_set(x_9, 0, x_41);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_58 = x_19;
} else {
 lean_dec_ref(x_19);
 x_58 = lean_box(0);
}
x_59 = lean_array_get_size(x_55);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = l_Lean_sortExprs(x_55, x_61);
lean_dec(x_55);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Int_Linear_Expr_applyPerm_go(x_64, x_56);
x_67 = l_Int_Linear_Expr_applyPerm_go(x_64, x_57);
lean_dec(x_64);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
if (lean_is_scalar(x_58)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_58;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_10, 0, x_69);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_58)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_58;
}
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_55);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_10, 0, x_71);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_8, 1);
lean_inc(x_73);
lean_dec(x_8);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_75 = x_9;
} else {
 lean_dec_ref(x_9);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
 x_78 = lean_box(0);
}
x_79 = lean_array_get_size(x_74);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_82 = l_Lean_sortExprs(x_74, x_81);
lean_dec(x_74);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = l_Int_Linear_Expr_applyPerm_go(x_84, x_76);
x_87 = l_Int_Linear_Expr_applyPerm_go(x_84, x_77);
lean_dec(x_84);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_10, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set(x_90, 1, x_73);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_74);
if (lean_is_scalar(x_75)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_75;
}
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_10, 0, x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_73);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_94 = lean_ctor_get(x_10, 0);
lean_inc(x_94);
lean_dec(x_10);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_96 = x_8;
} else {
 lean_dec_ref(x_8);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_9, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_98 = x_9;
} else {
 lean_dec_ref(x_9);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_101 = x_94;
} else {
 lean_dec_ref(x_94);
 x_101 = lean_box(0);
}
x_102 = lean_array_get_size(x_97);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_98);
x_105 = l_Lean_sortExprs(x_97, x_104);
lean_dec(x_97);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = l_Int_Linear_Expr_applyPerm_go(x_107, x_99);
x_110 = l_Int_Linear_Expr_applyPerm_go(x_107, x_100);
lean_dec(x_107);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
if (lean_is_scalar(x_101)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_101;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_96)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_96;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_95);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
if (lean_is_scalar(x_101)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_101;
}
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_97);
if (lean_is_scalar(x_98)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_98;
}
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
if (lean_is_scalar(x_96)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_96;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_95);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_8);
if (x_119 == 0)
{
return x_8;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_8, 0);
x_121 = lean_ctor_get(x_8, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_8);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_leCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_array_get_size(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_free_object(x_9);
x_30 = l_Lean_sortExprs(x_22, x_29);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Int_Linear_Expr_applyPerm_go(x_33, x_25);
x_35 = l_Int_Linear_Expr_applyPerm_go(x_33, x_26);
lean_dec(x_33);
lean_ctor_set(x_30, 1, x_32);
lean_ctor_set(x_30, 0, x_35);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_19, 0, x_34);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = l_Int_Linear_Expr_applyPerm_go(x_37, x_25);
x_39 = l_Int_Linear_Expr_applyPerm_go(x_37, x_26);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_36);
lean_ctor_set(x_19, 1, x_40);
lean_ctor_set(x_19, 0, x_38);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_41 = lean_ctor_get(x_19, 0);
x_42 = lean_ctor_get(x_19, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_19);
x_43 = lean_array_get_size(x_22);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_9);
x_46 = l_Lean_sortExprs(x_22, x_45);
lean_dec(x_22);
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_49 = x_46;
} else {
 lean_dec_ref(x_46);
 x_49 = lean_box(0);
}
x_50 = l_Int_Linear_Expr_applyPerm_go(x_48, x_41);
x_51 = l_Int_Linear_Expr_applyPerm_go(x_48, x_42);
lean_dec(x_48);
if (lean_is_scalar(x_49)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_49;
}
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
lean_ctor_set(x_10, 0, x_53);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_54; 
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_42);
lean_ctor_set(x_54, 1, x_22);
lean_ctor_set(x_9, 1, x_54);
lean_ctor_set(x_9, 0, x_41);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_ctor_get(x_19, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_19, 1);
lean_inc(x_57);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_58 = x_19;
} else {
 lean_dec_ref(x_19);
 x_58 = lean_box(0);
}
x_59 = lean_array_get_size(x_55);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_dec_le(x_59, x_60);
lean_dec(x_59);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = l_Lean_sortExprs(x_55, x_61);
lean_dec(x_55);
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_65 = x_62;
} else {
 lean_dec_ref(x_62);
 x_65 = lean_box(0);
}
x_66 = l_Int_Linear_Expr_applyPerm_go(x_64, x_56);
x_67 = l_Int_Linear_Expr_applyPerm_go(x_64, x_57);
lean_dec(x_64);
if (lean_is_scalar(x_65)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_65;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
if (lean_is_scalar(x_58)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_58;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_10, 0, x_69);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_70; lean_object* x_71; 
if (lean_is_scalar(x_58)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_58;
}
lean_ctor_set(x_70, 0, x_57);
lean_ctor_set(x_70, 1, x_55);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_56);
lean_ctor_set(x_71, 1, x_70);
lean_ctor_set(x_10, 0, x_71);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_8, 1);
lean_inc(x_73);
lean_dec(x_8);
x_74 = lean_ctor_get(x_9, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_75 = x_9;
} else {
 lean_dec_ref(x_9);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get(x_72, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_78 = x_72;
} else {
 lean_dec_ref(x_72);
 x_78 = lean_box(0);
}
x_79 = lean_array_get_size(x_74);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_dec_le(x_79, x_80);
lean_dec(x_79);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_75);
x_82 = l_Lean_sortExprs(x_74, x_81);
lean_dec(x_74);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_85 = x_82;
} else {
 lean_dec_ref(x_82);
 x_85 = lean_box(0);
}
x_86 = l_Int_Linear_Expr_applyPerm_go(x_84, x_76);
x_87 = l_Int_Linear_Expr_applyPerm_go(x_84, x_77);
lean_dec(x_84);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_83);
if (lean_is_scalar(x_78)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_78;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_10, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_10);
lean_ctor_set(x_90, 1, x_73);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
if (lean_is_scalar(x_78)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_78;
}
lean_ctor_set(x_91, 0, x_77);
lean_ctor_set(x_91, 1, x_74);
if (lean_is_scalar(x_75)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_75;
}
lean_ctor_set(x_92, 0, x_76);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_10, 0, x_92);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_10);
lean_ctor_set(x_93, 1, x_73);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_94 = lean_ctor_get(x_10, 0);
lean_inc(x_94);
lean_dec(x_10);
x_95 = lean_ctor_get(x_8, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_96 = x_8;
} else {
 lean_dec_ref(x_8);
 x_96 = lean_box(0);
}
x_97 = lean_ctor_get(x_9, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_98 = x_9;
} else {
 lean_dec_ref(x_9);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_94, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_101 = x_94;
} else {
 lean_dec_ref(x_94);
 x_101 = lean_box(0);
}
x_102 = lean_array_get_size(x_97);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_dec_le(x_102, x_103);
lean_dec(x_102);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_dec(x_98);
x_105 = l_Lean_sortExprs(x_97, x_104);
lean_dec(x_97);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
x_109 = l_Int_Linear_Expr_applyPerm_go(x_107, x_99);
x_110 = l_Int_Linear_Expr_applyPerm_go(x_107, x_100);
lean_dec(x_107);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_106);
if (lean_is_scalar(x_101)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_101;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_113, 0, x_112);
if (lean_is_scalar(x_96)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_96;
}
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_95);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
if (lean_is_scalar(x_101)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_101;
}
lean_ctor_set(x_115, 0, x_100);
lean_ctor_set(x_115, 1, x_97);
if (lean_is_scalar(x_98)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_98;
}
lean_ctor_set(x_116, 0, x_99);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_117, 0, x_116);
if (lean_is_scalar(x_96)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_96;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_95);
return x_118;
}
}
}
}
else
{
uint8_t x_119; 
x_119 = !lean_is_exclusive(x_8);
if (x_119 == 0)
{
return x_8;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_8, 0);
x_121 = lean_ctor_get(x_8, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_8);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_ToLinear_dvdCnstr_x3f___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Int_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_9);
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_8, 1);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_8);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = !lean_is_exclusive(x_9);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_9, 1);
x_23 = lean_ctor_get(x_9, 0);
lean_dec(x_23);
x_24 = !lean_is_exclusive(x_19);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
x_27 = lean_array_get_size(x_22);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_dec_le(x_27, x_28);
lean_dec(x_27);
if (x_29 == 0)
{
lean_object* x_30; uint8_t x_31; 
lean_free_object(x_9);
x_30 = l_Lean_sortExprs(x_22, x_29);
lean_dec(x_22);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_30, 1);
x_34 = l_Int_Linear_Expr_applyPerm_go(x_33, x_26);
lean_dec(x_33);
lean_ctor_set(x_30, 1, x_32);
lean_ctor_set(x_30, 0, x_34);
lean_ctor_set(x_19, 1, x_30);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_30, 0);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_30);
x_37 = l_Int_Linear_Expr_applyPerm_go(x_36, x_26);
lean_dec(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
lean_ctor_set(x_19, 1, x_38);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_19, 1, x_22);
lean_ctor_set(x_19, 0, x_26);
lean_ctor_set(x_9, 1, x_19);
lean_ctor_set(x_9, 0, x_25);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_39 = lean_ctor_get(x_19, 0);
x_40 = lean_ctor_get(x_19, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_19);
x_41 = lean_array_get_size(x_22);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_9);
x_44 = l_Lean_sortExprs(x_22, x_43);
lean_dec(x_22);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_47 = x_44;
} else {
 lean_dec_ref(x_44);
 x_47 = lean_box(0);
}
x_48 = l_Int_Linear_Expr_applyPerm_go(x_46, x_40);
lean_dec(x_46);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_39);
lean_ctor_set(x_50, 1, x_49);
lean_ctor_set(x_10, 0, x_50);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_51; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_40);
lean_ctor_set(x_51, 1, x_22);
lean_ctor_set(x_9, 1, x_51);
lean_ctor_set(x_9, 0, x_39);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_19, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_55 = x_19;
} else {
 lean_dec_ref(x_19);
 x_55 = lean_box(0);
}
x_56 = lean_array_get_size(x_52);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_dec_le(x_56, x_57);
lean_dec(x_56);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = l_Lean_sortExprs(x_52, x_58);
lean_dec(x_52);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_62 = x_59;
} else {
 lean_dec_ref(x_59);
 x_62 = lean_box(0);
}
x_63 = l_Int_Linear_Expr_applyPerm_go(x_61, x_54);
lean_dec(x_61);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
if (lean_is_scalar(x_55)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_55;
}
lean_ctor_set(x_65, 0, x_53);
lean_ctor_set(x_65, 1, x_64);
lean_ctor_set(x_10, 0, x_65);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_66; lean_object* x_67; 
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_54);
lean_ctor_set(x_66, 1, x_52);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set(x_10, 0, x_67);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_68 = lean_ctor_get(x_10, 0);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_dec(x_8);
x_70 = lean_ctor_get(x_9, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_71 = x_9;
} else {
 lean_dec_ref(x_9);
 x_71 = lean_box(0);
}
x_72 = lean_ctor_get(x_68, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_74 = x_68;
} else {
 lean_dec_ref(x_68);
 x_74 = lean_box(0);
}
x_75 = lean_array_get_size(x_70);
x_76 = lean_unsigned_to_nat(1u);
x_77 = lean_nat_dec_le(x_75, x_76);
lean_dec(x_75);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_71);
x_78 = l_Lean_sortExprs(x_70, x_77);
lean_dec(x_70);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_81 = x_78;
} else {
 lean_dec_ref(x_78);
 x_81 = lean_box(0);
}
x_82 = l_Int_Linear_Expr_applyPerm_go(x_80, x_73);
lean_dec(x_80);
if (lean_is_scalar(x_81)) {
 x_83 = lean_alloc_ctor(0, 2, 0);
} else {
 x_83 = x_81;
}
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_79);
if (lean_is_scalar(x_74)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_74;
}
lean_ctor_set(x_84, 0, x_72);
lean_ctor_set(x_84, 1, x_83);
lean_ctor_set(x_10, 0, x_84);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_10);
lean_ctor_set(x_85, 1, x_69);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
if (lean_is_scalar(x_74)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_74;
}
lean_ctor_set(x_86, 0, x_73);
lean_ctor_set(x_86, 1, x_70);
if (lean_is_scalar(x_71)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_71;
}
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set(x_10, 0, x_87);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_10);
lean_ctor_set(x_88, 1, x_69);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_89 = lean_ctor_get(x_10, 0);
lean_inc(x_89);
lean_dec(x_10);
x_90 = lean_ctor_get(x_8, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_91 = x_8;
} else {
 lean_dec_ref(x_8);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_9, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_93 = x_9;
} else {
 lean_dec_ref(x_9);
 x_93 = lean_box(0);
}
x_94 = lean_ctor_get(x_89, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_96 = x_89;
} else {
 lean_dec_ref(x_89);
 x_96 = lean_box(0);
}
x_97 = lean_array_get_size(x_92);
x_98 = lean_unsigned_to_nat(1u);
x_99 = lean_nat_dec_le(x_97, x_98);
lean_dec(x_97);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_93);
x_100 = l_Lean_sortExprs(x_92, x_99);
lean_dec(x_92);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = l_Int_Linear_Expr_applyPerm_go(x_102, x_95);
lean_dec(x_102);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_103;
}
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_101);
if (lean_is_scalar(x_96)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_96;
}
lean_ctor_set(x_106, 0, x_94);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
if (lean_is_scalar(x_91)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_91;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_90);
return x_108;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
if (lean_is_scalar(x_96)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_96;
}
lean_ctor_set(x_109, 0, x_95);
lean_ctor_set(x_109, 1, x_92);
if (lean_is_scalar(x_93)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_93;
}
lean_ctor_set(x_110, 0, x_94);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_111, 0, x_110);
if (lean_is_scalar(x_91)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_91;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_90);
return x_112;
}
}
}
}
else
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_8);
if (x_113 == 0)
{
return x_8;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_8, 0);
x_115 = lean_ctor_get(x_8, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_8);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed), 1, 0);
x_11 = lean_mk_string_unchecked("Int", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_12, x_13);
x_15 = lean_nat_to_int(x_7);
x_16 = l_Lean_mkIntLit(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = l_Lean_RArray_toExpr___redArg(x_14, x_10, x_17, x_2, x_3, x_4, x_5, x_6);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed), 1, 0);
x_20 = lean_mk_string_unchecked("Int", 3, 3);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = lean_box(0);
x_23 = l_Lean_Expr_const___override(x_21, x_22);
x_24 = l_Lean_RArray_ofArray(lean_box(0), x_1, lean_box(0));
x_25 = l_Lean_RArray_toExpr___redArg(x_23, x_19, x_24, x_2, x_3, x_4, x_5, x_6);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Int_toContextExpr___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Int_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_IntInstTesters(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_SortExprs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_IntInstTesters(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KExprMap(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Int_Linear_instReprPoly__lean = _init_l_Int_Linear_instReprPoly__lean();
lean_mark_persistent(l_Int_Linear_instReprPoly__lean);
l_Int_Linear_instReprExpr__lean = _init_l_Int_Linear_instReprExpr__lean();
lean_mark_persistent(l_Int_Linear_instReprExpr__lean);
l_Lean_Meta_Simp_Arith_Int_instToExprPoly = _init_l_Lean_Meta_Simp_Arith_Int_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprPoly);
l_Lean_Meta_Simp_Arith_Int_instToExprExpr = _init_l_Lean_Meta_Simp_Arith_Int_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Int_instToExprExpr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
