// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Nat.Basic
// Imports: Lean.Util.SortExprs Lean.Meta.Check Lean.Meta.Offset Lean.Meta.AppBuilder Lean.Meta.KExprMap Lean.Data.RArray
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
lean_object* l_Lean_Meta_isInstHAddNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(lean_object*);
lean_object* l_Lean_Meta_isInstOfNatNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___lam__0(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_Meta_evalNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RArray_toExpr___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatAdd(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr;
lean_object* l_Lean_sortExprs(lean_object*, uint8_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm(lean_object*, lean_object*);
lean_object* l_Lean_Meta_KExprMap_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_KExprMap_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLE(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLENat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm___boxed(lean_object*, lean_object*);
lean_object* l_Lean_RArray_ofArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstLTNat___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_mkNatMul(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169____boxed(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean;
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object*);
lean_object* l_Lean_Meta_isInstMulNat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_Linear_Expr_inc(lean_object*);
lean_object* l_Lean_mkNatEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go(lean_object* x_1, lean_object* x_2) {
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
x_22 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_3, x_21);
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
x_31 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_29);
x_32 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_30);
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
x_35 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_33);
x_36 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_34);
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
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_2, 1);
x_40 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_39);
lean_ctor_set(x_2, 1, x_40);
return x_2;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_2, 0);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_2);
x_43 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_42);
x_44 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
default: 
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_2, 0);
x_47 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_46);
lean_ctor_set(x_2, 0, x_47);
return x_2;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_2, 0);
x_49 = lean_ctor_get(x_2, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_2);
x_50 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_48);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Nat_Linear_Expr_applyPerm_go_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_Expr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_Expr_applyPerm(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_4);
x_7 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_5);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_2);
x_11 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_9);
x_12 = l_Nat_Linear_Expr_applyPerm_go(x_1, x_10);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Nat_Linear_ExprCnstr_applyPerm___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Nat_Linear_ExprCnstr_applyPerm(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_19; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_19 = lean_unsigned_to_nat(1024u);
x_20 = lean_nat_dec_le(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_to_int(x_21);
x_5 = x_22;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_to_int(x_23);
x_5 = x_24;
goto block_18;
}
block_18:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Nat.Linear.Expr.num", 19, 19);
if (lean_is_scalar(x_4)) {
 x_7 = lean_alloc_ctor(3, 1, 0);
} else {
 x_7 = x_4;
 lean_ctor_set_tag(x_7, 3);
}
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_41; uint8_t x_42; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_26 = x_1;
} else {
 lean_dec_ref(x_1);
 x_26 = lean_box(0);
}
x_41 = lean_unsigned_to_nat(1024u);
x_42 = lean_nat_dec_le(x_41, x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_to_int(x_43);
x_27 = x_44;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_to_int(x_45);
x_27 = x_46;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_28 = lean_mk_string_unchecked("Nat.Linear.Expr.var", 19, 19);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(3, 1, 0);
} else {
 x_29 = x_26;
 lean_ctor_set_tag(x_29, 3);
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = l_Repr_addAppParen(x_37, x_2);
return x_39;
}
}
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_67; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_49 = x_1;
} else {
 lean_dec_ref(x_1);
 x_49 = lean_box(0);
}
x_50 = lean_unsigned_to_nat(1024u);
x_67 = lean_nat_dec_le(x_50, x_2);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_unsigned_to_nat(2u);
x_69 = lean_nat_to_int(x_68);
x_51 = x_69;
goto block_66;
}
else
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_unsigned_to_nat(1u);
x_71 = lean_nat_to_int(x_70);
x_51 = x_71;
goto block_66;
}
block_66:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_52 = lean_mk_string_unchecked("Nat.Linear.Expr.add", 19, 19);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_box(1);
if (lean_is_scalar(x_49)) {
 x_55 = lean_alloc_ctor(5, 2, 0);
} else {
 x_55 = x_49;
 lean_ctor_set_tag(x_55, 5);
}
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_47, x_50);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_54);
x_59 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_48, x_50);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_64);
x_65 = l_Repr_addAppParen(x_63, x_2);
return x_65;
}
}
case 3:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_93; 
x_72 = lean_ctor_get(x_1, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_74 = x_1;
} else {
 lean_dec_ref(x_1);
 x_74 = lean_box(0);
}
x_75 = lean_unsigned_to_nat(1024u);
x_93 = lean_nat_dec_le(x_75, x_2);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_unsigned_to_nat(2u);
x_95 = lean_nat_to_int(x_94);
x_76 = x_95;
goto block_92;
}
else
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_nat_to_int(x_96);
x_76 = x_97;
goto block_92;
}
block_92:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_77 = lean_mk_string_unchecked("Nat.Linear.Expr.mulL", 20, 20);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_box(1);
if (lean_is_scalar(x_74)) {
 x_80 = lean_alloc_ctor(5, 2, 0);
} else {
 x_80 = x_74;
 lean_ctor_set_tag(x_80, 5);
}
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = l___private_Init_Data_Repr_0__Nat_reprFast(x_72);
x_82 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_82, 0, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_79);
x_85 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_73, x_75);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_76);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = l_Repr_addAppParen(x_89, x_2);
return x_91;
}
}
default: 
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_119; 
x_98 = lean_ctor_get(x_1, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_1, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_100 = x_1;
} else {
 lean_dec_ref(x_1);
 x_100 = lean_box(0);
}
x_101 = lean_unsigned_to_nat(1024u);
x_119 = lean_nat_dec_le(x_101, x_2);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_unsigned_to_nat(2u);
x_121 = lean_nat_to_int(x_120);
x_102 = x_121;
goto block_118;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_to_int(x_122);
x_102 = x_123;
goto block_118;
}
block_118:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; lean_object* x_117; 
x_103 = lean_mk_string_unchecked("Nat.Linear.Expr.mulR", 20, 20);
x_104 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_104, 0, x_103);
x_105 = lean_box(1);
if (lean_is_scalar(x_100)) {
 x_106 = lean_alloc_ctor(5, 2, 0);
} else {
 x_106 = x_100;
 lean_ctor_set_tag(x_106, 5);
}
lean_ctor_set(x_106, 0, x_104);
lean_ctor_set(x_106, 1, x_105);
x_107 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_98, x_101);
x_108 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_105);
x_110 = l___private_Init_Data_Repr_0__Nat_reprFast(x_99);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_113, 0, x_102);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_box(0);
x_115 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_115, 0, x_113);
x_116 = lean_unbox(x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*1, x_116);
x_117 = l_Repr_addAppParen(x_115, x_2);
return x_117;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_59; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("eq", 2, 2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = lean_nat_to_int(x_10);
x_59 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_mk_string_unchecked("false", 5, 5);
x_61 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_12 = x_61;
goto block_58;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_mk_string_unchecked("true", 4, 4);
x_63 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_63, 0, x_62);
x_12 = x_63;
goto block_58;
}
block_58:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_mk_string_unchecked(",", 1, 1);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("lhs", 3, 3);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_8);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
x_27 = lean_unsigned_to_nat(7u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_unsigned_to_nat(0u);
x_31 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_29, x_30);
lean_inc(x_28);
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_unbox(x_14);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_33);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_19);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_21);
x_38 = lean_mk_string_unchecked("rhs", 3, 3);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
x_42 = lean_ctor_get(x_1, 1);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExpr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_169_(x_42, x_30);
x_44 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_44, 0, x_28);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_unbox(x_14);
lean_ctor_set_uint8(x_45, sizeof(void*)*1, x_46);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_41);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_mk_string_unchecked(" }", 2, 2);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_nat_to_int(x_49);
x_51 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_51, 0, x_2);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_47);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_48);
x_54 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_55, 0, x_50);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_unbox(x_14);
lean_ctor_set_uint8(x_56, sizeof(void*)*1, x_57);
return x_56;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprExprCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_444____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_mk_string_unchecked("(", 1, 1);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(0);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_7);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_1);
x_12 = l_List_reverse___redArg(x_11);
x_13 = lean_mk_string_unchecked(",", 1, 1);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box(1);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_12, x_16);
x_18 = lean_mk_string_unchecked(")", 1, 1);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_to_int(x_19);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_5);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_17);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_18);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_27, 0, x_25);
x_28 = lean_unbox(x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_28);
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_1);
x_31 = lean_mk_string_unchecked("(", 1, 1);
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_29);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l___private_Init_Data_Repr_0__Nat_reprFast(x_30);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
x_39 = l_List_reverse___redArg(x_38);
x_40 = lean_mk_string_unchecked(",", 1, 1);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_box(1);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = l_Std_Format_joinSep___at___Lean_Syntax_formatStxAux_spec__1(x_39, x_43);
x_45 = lean_mk_string_unchecked(")", 1, 1);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_nat_to_int(x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_31);
x_49 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_44);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_45);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_54, 0, x_52);
x_55 = lean_unbox(x_53);
lean_ctor_set_uint8(x_54, sizeof(void*)*1, x_55);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("[]", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_4 = lean_alloc_closure((void*)(l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg___lam__0), 1, 0);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked(",", 1, 1);
x_7 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_1);
x_10 = l_Std_Format_joinSep(lean_box(0), x_4, x_1, x_9);
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_12 = lean_ctor_get(x_1, 1);
lean_dec(x_12);
x_13 = lean_ctor_get(x_1, 0);
lean_dec(x_13);
x_14 = lean_mk_string_unchecked("]", 1, 1);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_to_int(x_15);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_5);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
lean_ctor_set(x_1, 0, x_17);
x_18 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_18, 0, x_14);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_20, 0, x_16);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_22, 0, x_20);
x_23 = lean_unbox(x_21);
lean_ctor_set_uint8(x_22, sizeof(void*)*1, x_23);
return x_22;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("]", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_27 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_27, 0, x_5);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_24);
x_30 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_26);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_31);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_58; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("eq", 2, 2);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(6u);
x_11 = lean_nat_to_int(x_10);
x_58 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_mk_string_unchecked("false", 5, 5);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_12 = x_60;
goto block_57;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_mk_string_unchecked("true", 4, 4);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_12 = x_62;
goto block_57;
}
block_57:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_mk_string_unchecked(",", 1, 1);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_19);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(1);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("lhs", 3, 3);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_8);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_8);
x_27 = lean_unsigned_to_nat(7u);
x_28 = lean_nat_to_int(x_27);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(x_29);
lean_inc(x_28);
x_31 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unbox(x_14);
lean_ctor_set_uint8(x_32, sizeof(void*)*1, x_33);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_19);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
x_37 = lean_mk_string_unchecked("rhs", 3, 3);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_8);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_dec(x_1);
x_42 = l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___redArg(x_41);
x_43 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_unbox(x_14);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_44);
x_47 = lean_mk_string_unchecked(" }", 2, 2);
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_to_int(x_48);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_2);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_46);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_47);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_54, 0, x_49);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_unbox(x_14);
lean_ctor_set_uint8(x_55, sizeof(void*)*1, x_56);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr___redArg____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Prod_repr___at___List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0_spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_repr___at_____private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_Arith_Nat_Basic_0__Lean_Meta_Simp_Arith_Nat_reprPolyCnstr____x40_Lean_Meta_Tactic_Simp_Arith_Nat_Basic___hyg_523____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("Nat", 3, 3);
x_4 = lean_mk_string_unchecked("Linear", 6, 6);
x_5 = lean_mk_string_unchecked("Expr", 4, 4);
x_6 = lean_mk_string_unchecked("num", 3, 3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
x_10 = l_Lean_mkNatLit(x_2);
x_11 = l_Lean_Expr_app___override(x_9, x_10);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_mk_string_unchecked("Nat", 3, 3);
x_14 = lean_mk_string_unchecked("Linear", 6, 6);
x_15 = lean_mk_string_unchecked("Expr", 4, 4);
x_16 = lean_mk_string_unchecked("var", 3, 3);
x_17 = l_Lean_Name_mkStr4(x_13, x_14, x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_const___override(x_17, x_18);
x_20 = l_Lean_mkNatLit(x_12);
x_21 = l_Lean_Expr_app___override(x_19, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_mk_string_unchecked("Nat", 3, 3);
x_25 = lean_mk_string_unchecked("Linear", 6, 6);
x_26 = lean_mk_string_unchecked("Expr", 4, 4);
x_27 = lean_mk_string_unchecked("add", 3, 3);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_28, x_29);
x_31 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_22);
x_32 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_23);
x_33 = l_Lean_mkAppB(x_30, x_31, x_32);
return x_33;
}
case 3:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("Nat", 3, 3);
x_37 = lean_mk_string_unchecked("Linear", 6, 6);
x_38 = lean_mk_string_unchecked("Expr", 4, 4);
x_39 = lean_mk_string_unchecked("mulL", 4, 4);
x_40 = l_Lean_Name_mkStr4(x_36, x_37, x_38, x_39);
x_41 = lean_box(0);
x_42 = l_Lean_Expr_const___override(x_40, x_41);
x_43 = l_Lean_mkNatLit(x_34);
x_44 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_35);
x_45 = l_Lean_mkAppB(x_42, x_43, x_44);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_mk_string_unchecked("Nat", 3, 3);
x_49 = lean_mk_string_unchecked("Linear", 6, 6);
x_50 = lean_mk_string_unchecked("Expr", 4, 4);
x_51 = lean_mk_string_unchecked("mulR", 4, 4);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_55 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_46);
x_56 = l_Lean_mkNatLit(x_47);
x_57 = l_Lean_mkAppB(x_54, x_55, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_16; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("Linear", 6, 6);
x_4 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_5 = lean_mk_string_unchecked("mk", 2, 2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_mk_string_unchecked("Bool", 4, 4);
x_18 = lean_mk_string_unchecked("false", 5, 5);
x_19 = l_Lean_Name_mkStr2(x_17, x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_7);
x_9 = x_20;
goto block_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_mk_string_unchecked("Bool", 4, 4);
x_22 = lean_mk_string_unchecked("true", 4, 4);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = l_Lean_Expr_const___override(x_23, x_7);
x_9 = x_24;
goto block_15;
}
block_15:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toExpr(x_12);
x_14 = l_Lean_mkApp3(x_8, x_9, x_11, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toExpr(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = lean_mk_string_unchecked("Linear", 6, 6);
x_4 = lean_mk_string_unchecked("ExprCnstr", 9, 9);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_mkNatLit(x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_instInhabitedExpr;
x_9 = lean_array_get(x_8, x_1, x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_3);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_11, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_12, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = l_Lean_mkNatAdd(x_14, x_18);
lean_ctor_set(x_16, 0, x_19);
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = l_Lean_mkNatAdd(x_14, x_20);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
case 3:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_25, x_3);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = l_Lean_mkNatLit(x_24);
x_30 = l_Lean_mkNatMul(x_29, x_28);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_26, 0);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_26);
x_33 = l_Lean_mkNatLit(x_24);
x_34 = l_Lean_mkNatMul(x_33, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
}
default: 
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_36, x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = l_Lean_mkNatLit(x_37);
x_42 = l_Lean_mkNatMul(x_40, x_41);
lean_ctor_set(x_38, 0, x_42);
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = l_Lean_mkNatLit(x_37);
x_46 = l_Lean_mkNatMul(x_43, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_5, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_9, x_8);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = l_Lean_mkNatLE(x_7, x_12);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_10, 0);
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_10);
x_16 = l_Lean_mkNatLE(x_7, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_ctor_get(x_2, 0);
lean_inc(x_18);
x_19 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_18, x_3);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_Meta_Simp_Arith_Nat_LinearExpr_toArith___redArg(x_1, x_22, x_21);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = l_Lean_mkNatEq(x_20, x_25);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_23, 0);
x_28 = lean_ctor_get(x_23, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_23);
x_29 = l_Lean_mkNatEq(x_20, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___redArg(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_LinearCnstr_toArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_14 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_17 = lean_mk_string_unchecked("Nat", 3, 3);
x_18 = lean_mk_string_unchecked("succ", 4, 4);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_11);
x_22 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
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
x_71 = lean_mk_string_unchecked("add", 3, 3);
lean_inc(x_71);
x_72 = l_Lean_Name_mkStr2(x_17, x_71);
x_73 = l_Lean_Expr_isConstOf(x_67, x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Expr_isApp(x_67);
if (x_74 == 0)
{
lean_object* x_75; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_75 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_75;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
lean_inc(x_67);
x_76 = l_Lean_Expr_appFnCleanup___redArg(x_67);
x_77 = lean_mk_string_unchecked("OfNat", 5, 5);
x_78 = lean_mk_string_unchecked("ofNat", 5, 5);
x_79 = l_Lean_Name_mkStr2(x_77, x_78);
x_80 = l_Lean_Expr_isConstOf(x_76, x_79);
lean_dec(x_79);
if (x_80 == 0)
{
uint8_t x_81; 
x_81 = l_Lean_Expr_isApp(x_76);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_76);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_82 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_83 = lean_ctor_get(x_67, 1);
lean_inc(x_83);
lean_dec(x_67);
x_84 = l_Lean_Expr_appFnCleanup___redArg(x_76);
x_85 = lean_mk_string_unchecked("Mul", 3, 3);
x_86 = l_Lean_Name_mkStr2(x_85, x_68);
x_87 = l_Lean_Expr_isConstOf(x_84, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_mk_string_unchecked("Add", 3, 3);
x_89 = l_Lean_Name_mkStr2(x_88, x_71);
x_90 = l_Lean_Expr_isConstOf(x_84, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
uint8_t x_91; 
x_91 = l_Lean_Expr_isApp(x_84);
if (x_91 == 0)
{
lean_object* x_92; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_92 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_92;
}
else
{
lean_object* x_93; uint8_t x_94; 
x_93 = l_Lean_Expr_appFnCleanup___redArg(x_84);
x_94 = l_Lean_Expr_isApp(x_93);
if (x_94 == 0)
{
lean_object* x_95; 
lean_dec(x_93);
lean_dec(x_83);
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_95 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_96 = l_Lean_Expr_appFnCleanup___redArg(x_93);
x_97 = lean_mk_string_unchecked("HMul", 4, 4);
x_98 = lean_mk_string_unchecked("hMul", 4, 4);
x_99 = l_Lean_Name_mkStr2(x_97, x_98);
x_100 = l_Lean_Expr_isConstOf(x_96, x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_11);
x_101 = lean_mk_string_unchecked("HAdd", 4, 4);
x_102 = lean_mk_string_unchecked("hAdd", 4, 4);
x_103 = l_Lean_Name_mkStr2(x_101, x_102);
x_104 = l_Lean_Expr_isConstOf(x_96, x_103);
lean_dec(x_103);
lean_dec(x_96);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_83);
lean_dec(x_23);
lean_dec(x_15);
x_105 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_105;
}
else
{
lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_106 = l_Lean_Meta_isInstHAddNat(x_83, x_3, x_4, x_5, x_6, x_10);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_unbox(x_107);
lean_dec(x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_23);
lean_dec(x_15);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
lean_dec(x_106);
x_110 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_109);
lean_dec(x_3);
lean_dec(x_2);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_1);
x_111 = lean_ctor_get(x_106, 1);
lean_inc(x_111);
lean_dec(x_106);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_112 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_111);
if (lean_obj_tag(x_112) == 0)
{
uint8_t x_113; 
x_113 = !lean_is_exclusive(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_112, 0);
x_115 = lean_ctor_get(x_112, 1);
x_116 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_115);
if (lean_obj_tag(x_116) == 0)
{
uint8_t x_117; 
x_117 = !lean_is_exclusive(x_116);
if (x_117 == 0)
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_116, 0);
lean_ctor_set_tag(x_112, 2);
lean_ctor_set(x_112, 1, x_118);
lean_ctor_set(x_116, 0, x_112);
return x_116;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_116, 0);
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_116);
lean_ctor_set_tag(x_112, 2);
lean_ctor_set(x_112, 1, x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_112);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
else
{
lean_free_object(x_112);
lean_dec(x_114);
return x_116;
}
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_112, 0);
x_123 = lean_ctor_get(x_112, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_112);
x_124 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_123);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_124)) {
 lean_ctor_release(x_124, 0);
 lean_ctor_release(x_124, 1);
 x_127 = x_124;
} else {
 lean_dec_ref(x_124);
 x_127 = lean_box(0);
}
x_128 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_128, 0, x_122);
lean_ctor_set(x_128, 1, x_125);
if (lean_is_scalar(x_127)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_127;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_126);
return x_129;
}
else
{
lean_dec(x_122);
return x_124;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_112;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_96);
x_130 = l_Lean_Meta_isInstHMulNat___redArg(x_83, x_4, x_10);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_133);
lean_dec(x_3);
lean_dec(x_2);
return x_134;
}
else
{
lean_object* x_135; 
x_135 = lean_ctor_get(x_130, 1);
lean_inc(x_135);
lean_dec(x_130);
x_24 = x_15;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_135;
goto block_66;
}
}
}
}
}
else
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; 
lean_dec(x_84);
lean_dec(x_11);
x_136 = l_Lean_Meta_isInstAddNat___redArg(x_83, x_4, x_10);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; 
lean_dec(x_23);
lean_dec(x_15);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_139);
lean_dec(x_3);
lean_dec(x_2);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_1);
x_141 = lean_ctor_get(x_136, 1);
lean_inc(x_141);
lean_dec(x_136);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_142 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_141);
if (lean_obj_tag(x_142) == 0)
{
uint8_t x_143; 
x_143 = !lean_is_exclusive(x_142);
if (x_143 == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_142, 0);
x_145 = lean_ctor_get(x_142, 1);
x_146 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_145);
if (lean_obj_tag(x_146) == 0)
{
uint8_t x_147; 
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
lean_object* x_148; 
x_148 = lean_ctor_get(x_146, 0);
lean_ctor_set_tag(x_142, 2);
lean_ctor_set(x_142, 1, x_148);
lean_ctor_set(x_146, 0, x_142);
return x_146;
}
else
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_146, 0);
x_150 = lean_ctor_get(x_146, 1);
lean_inc(x_150);
lean_inc(x_149);
lean_dec(x_146);
lean_ctor_set_tag(x_142, 2);
lean_ctor_set(x_142, 1, x_149);
x_151 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_151, 0, x_142);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
}
else
{
lean_free_object(x_142);
lean_dec(x_144);
return x_146;
}
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_142, 0);
x_153 = lean_ctor_get(x_142, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_142);
x_154 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_153);
if (lean_obj_tag(x_154) == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
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
x_158 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_155);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_156);
return x_159;
}
else
{
lean_dec(x_152);
return x_154;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_142;
}
}
}
}
else
{
lean_object* x_160; lean_object* x_161; uint8_t x_162; 
lean_dec(x_84);
lean_dec(x_71);
x_160 = l_Lean_Meta_isInstMulNat(x_83, x_3, x_4, x_5, x_6, x_10);
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_unbox(x_161);
lean_dec(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_23);
lean_dec(x_15);
lean_dec(x_11);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_dec(x_160);
x_164 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_163);
lean_dec(x_3);
lean_dec(x_2);
return x_164;
}
else
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_dec(x_160);
x_24 = x_15;
x_25 = x_2;
x_26 = x_3;
x_27 = x_4;
x_28 = x_5;
x_29 = x_6;
x_30 = x_165;
goto block_66;
}
}
}
}
else
{
lean_object* x_166; lean_object* x_167; uint8_t x_168; 
lean_dec(x_76);
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_11);
x_166 = l_Lean_Meta_isInstOfNatNat(x_15, x_3, x_4, x_5, x_6, x_10);
x_167 = lean_ctor_get(x_166, 0);
lean_inc(x_167);
x_168 = lean_unbox(x_167);
lean_dec(x_167);
if (x_168 == 0)
{
lean_object* x_169; lean_object* x_170; 
lean_dec(x_23);
x_169 = lean_ctor_get(x_166, 1);
lean_inc(x_169);
lean_dec(x_166);
x_170 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_169);
lean_dec(x_3);
lean_dec(x_2);
return x_170;
}
else
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_1);
x_171 = lean_ctor_get(x_166, 1);
lean_inc(x_171);
lean_dec(x_166);
x_172 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_171);
return x_172;
}
}
}
}
else
{
lean_object* x_173; 
lean_dec(x_71);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_11);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_173 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_23, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = lean_ctor_get(x_173, 1);
x_177 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_176);
if (lean_obj_tag(x_177) == 0)
{
uint8_t x_178; 
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_177, 0);
lean_ctor_set_tag(x_173, 2);
lean_ctor_set(x_173, 1, x_179);
lean_ctor_set(x_177, 0, x_173);
return x_177;
}
else
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_177, 0);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_inc(x_180);
lean_dec(x_177);
lean_ctor_set_tag(x_173, 2);
lean_ctor_set(x_173, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_173);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
else
{
lean_free_object(x_173);
lean_dec(x_175);
return x_177;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_173, 0);
x_184 = lean_ctor_get(x_173, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_173);
x_185 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_184);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_185)) {
 lean_ctor_release(x_185, 0);
 lean_ctor_release(x_185, 1);
 x_188 = x_185;
} else {
 lean_dec_ref(x_185);
 x_188 = lean_box(0);
}
x_189 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_189, 0, x_183);
lean_ctor_set(x_189, 1, x_186);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
else
{
lean_dec(x_183);
return x_185;
}
}
}
else
{
lean_dec(x_15);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_173;
}
}
}
else
{
lean_dec(x_68);
lean_dec(x_67);
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
lean_inc(x_26);
lean_inc(x_23);
x_31 = l_Lean_Meta_evalNat(x_23, x_26, x_27, x_28, x_29, x_30);
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
lean_inc(x_26);
x_34 = l_Lean_Meta_evalNat(x_24, x_26, x_27, x_28, x_29, x_33);
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
x_37 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_25, x_26, x_27, x_28, x_29, x_36);
lean_dec(x_26);
lean_dec(x_25);
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
x_40 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_23, x_25, x_26, x_27, x_28, x_29, x_38);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_40, 0);
if (lean_is_scalar(x_11)) {
 x_43 = lean_alloc_ctor(4, 2, 0);
} else {
 x_43 = x_11;
 lean_ctor_set_tag(x_43, 4);
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
 x_46 = lean_alloc_ctor(4, 2, 0);
} else {
 x_46 = x_11;
 lean_ctor_set_tag(x_46, 4);
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
lean_dec(x_26);
lean_dec(x_25);
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
x_54 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_24, x_25, x_26, x_27, x_28, x_29, x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
if (lean_is_scalar(x_11)) {
 x_57 = lean_alloc_ctor(3, 2, 0);
} else {
 x_57 = x_11;
 lean_ctor_set_tag(x_57, 3);
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
 x_60 = lean_alloc_ctor(3, 2, 0);
} else {
 x_60 = x_11;
 lean_ctor_set_tag(x_60, 3);
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
lean_dec(x_26);
lean_dec(x_25);
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
lean_object* x_191; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_1);
x_191 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_15, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_191) == 0)
{
uint8_t x_192; 
x_192 = !lean_is_exclusive(x_191);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
x_193 = lean_ctor_get(x_191, 0);
x_194 = l_Nat_Linear_Expr_inc(x_193);
lean_ctor_set(x_191, 0, x_194);
return x_191;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_195 = lean_ctor_get(x_191, 0);
x_196 = lean_ctor_get(x_191, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_191);
x_197 = l_Nat_Linear_Expr_inc(x_195);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_197);
lean_ctor_set(x_198, 1, x_196);
return x_198;
}
}
else
{
return x_191;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 4:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 1)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__0___boxed), 7, 1);
lean_closure_set(x_18, 0, x_1);
x_19 = lean_mk_string_unchecked("Nat", 3, 3);
x_20 = lean_string_dec_eq(x_13, x_19);
lean_dec(x_19);
lean_dec(x_13);
if (x_20 == 0)
{
lean_dec(x_11);
x_14 = x_18;
goto block_17;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_mk_string_unchecked("zero", 4, 4);
x_22 = lean_string_dec_eq(x_11, x_21);
lean_dec(x_21);
lean_dec(x_11);
if (x_22 == 0)
{
x_14 = x_18;
goto block_17;
}
else
{
lean_object* x_23; 
lean_dec(x_18);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__1___boxed), 6, 0);
x_14 = x_23;
goto block_17;
}
}
block_17:
{
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_15; 
lean_dec(x_1);
x_15 = lean_apply_6(x_14, x_2, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_12);
x_16 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_10);
lean_dec(x_9);
x_24 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_9);
x_25 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_25;
}
}
case 5:
{
lean_object* x_26; 
x_26 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_26;
}
case 9:
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
lean_dec(x_27);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_7);
return x_32;
}
}
else
{
lean_object* x_33; 
lean_dec(x_27);
x_33 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
}
case 10:
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
lean_dec(x_1);
x_1 = x_34;
goto _start;
}
default: 
{
lean_object* x_36; 
x_36 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_addAsVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_3);
lean_dec(x_2);
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
x_22 = lean_mk_string_unchecked("Nat", 3, 3);
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
lean_inc(x_22);
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
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_32 = lean_mk_string_unchecked("Eq", 2, 2);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Lean_Expr_isConstOf(x_31, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_22);
x_35 = l_Lean_Expr_isApp(x_31);
if (x_35 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_37 = lean_mk_string_unchecked("GT", 2, 2);
x_38 = lean_mk_string_unchecked("gt", 2, 2);
x_39 = l_Lean_Name_mkStr2(x_37, x_38);
x_40 = l_Lean_Expr_isConstOf(x_36, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_mk_string_unchecked("GE", 2, 2);
x_42 = lean_mk_string_unchecked("ge", 2, 2);
x_43 = l_Lean_Name_mkStr2(x_41, x_42);
x_44 = l_Lean_Expr_isConstOf(x_36, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_mk_string_unchecked("LT", 2, 2);
x_46 = l_Lean_Name_mkStr2(x_45, x_23);
x_47 = l_Lean_Expr_isConstOf(x_36, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_mk_string_unchecked("LE", 2, 2);
x_49 = l_Lean_Name_mkStr2(x_48, x_26);
x_50 = l_Lean_Expr_isConstOf(x_36, x_49);
lean_dec(x_49);
lean_dec(x_36);
if (x_50 == 0)
{
lean_dec(x_30);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_14;
}
else
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_11);
x_51 = l_Lean_Meta_isInstLENat___redArg(x_30, x_4, x_10);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
uint8_t x_54; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_51);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_51, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_51, 0, x_56);
return x_51;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_dec(x_51);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_61 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_60);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_63);
if (lean_obj_tag(x_64) == 0)
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_62);
lean_ctor_set(x_67, 1, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_47);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_64, 0, x_68);
return x_64;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_69 = lean_ctor_get(x_64, 0);
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_64);
x_71 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_71, 0, x_62);
lean_ctor_set(x_71, 1, x_69);
lean_ctor_set_uint8(x_71, sizeof(void*)*2, x_47);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
else
{
uint8_t x_74; 
lean_dec(x_62);
x_74 = !lean_is_exclusive(x_64);
if (x_74 == 0)
{
return x_64;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_64, 0);
x_76 = lean_ctor_get(x_64, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_64);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_61);
if (x_78 == 0)
{
return x_61;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_61, 0);
x_80 = lean_ctor_get(x_61, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_61);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_11);
x_82 = l_Lean_Meta_isInstLTNat___redArg(x_30, x_4, x_10);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_unbox(x_83);
lean_dec(x_83);
if (x_84 == 0)
{
uint8_t x_85; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_85 = !lean_is_exclusive(x_82);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_82, 0);
lean_dec(x_86);
x_87 = lean_box(0);
lean_ctor_set(x_82, 0, x_87);
return x_82;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_82, 1);
lean_inc(x_88);
lean_dec(x_82);
x_89 = lean_box(0);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
else
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_82, 1);
lean_inc(x_91);
lean_dec(x_82);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_92 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
lean_dec(x_92);
x_95 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_94);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = l_Nat_Linear_Expr_inc(x_93);
x_99 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_97);
lean_ctor_set_uint8(x_99, sizeof(void*)*2, x_44);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_95, 0, x_100);
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = l_Nat_Linear_Expr_inc(x_93);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_44);
x_105 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
return x_106;
}
}
else
{
uint8_t x_107; 
lean_dec(x_93);
x_107 = !lean_is_exclusive(x_95);
if (x_107 == 0)
{
return x_95;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_ctor_get(x_95, 0);
x_109 = lean_ctor_get(x_95, 1);
lean_inc(x_109);
lean_inc(x_108);
lean_dec(x_95);
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
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_111 = !lean_is_exclusive(x_92);
if (x_111 == 0)
{
return x_92;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_92, 0);
x_113 = lean_ctor_get(x_92, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_92);
x_114 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
return x_114;
}
}
}
}
}
else
{
lean_object* x_115; lean_object* x_116; uint8_t x_117; 
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_11);
x_115 = l_Lean_Meta_isInstLENat___redArg(x_30, x_4, x_10);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
uint8_t x_118; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_118 = !lean_is_exclusive(x_115);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_115, 0);
lean_dec(x_119);
x_120 = lean_box(0);
lean_ctor_set(x_115, 0, x_120);
return x_115;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
lean_dec(x_115);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_115, 1);
lean_inc(x_124);
lean_dec(x_115);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_125 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_124);
if (lean_obj_tag(x_125) == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
lean_dec(x_125);
x_128 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_127);
if (lean_obj_tag(x_128) == 0)
{
uint8_t x_129; 
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_128, 0);
x_131 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_131, 0, x_126);
lean_ctor_set(x_131, 1, x_130);
lean_ctor_set_uint8(x_131, sizeof(void*)*2, x_40);
x_132 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_128, 0, x_132);
return x_128;
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_133 = lean_ctor_get(x_128, 0);
x_134 = lean_ctor_get(x_128, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_128);
x_135 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_135, 0, x_126);
lean_ctor_set(x_135, 1, x_133);
lean_ctor_set_uint8(x_135, sizeof(void*)*2, x_40);
x_136 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_126);
x_138 = !lean_is_exclusive(x_128);
if (x_138 == 0)
{
return x_128;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_128, 0);
x_140 = lean_ctor_get(x_128, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_128);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_125);
if (x_142 == 0)
{
return x_125;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_125, 0);
x_144 = lean_ctor_get(x_125, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_125);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_36);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_11);
x_146 = l_Lean_Meta_isInstLTNat___redArg(x_30, x_4, x_10);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_unbox(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
uint8_t x_149; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_149 = !lean_is_exclusive(x_146);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; 
x_150 = lean_ctor_get(x_146, 0);
lean_dec(x_150);
x_151 = lean_box(0);
lean_ctor_set(x_146, 0, x_151);
return x_146;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_146, 1);
lean_inc(x_152);
lean_dec(x_146);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_152);
return x_154;
}
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_146, 1);
lean_inc(x_155);
lean_dec(x_146);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_156 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_155);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_158);
if (lean_obj_tag(x_159) == 0)
{
uint8_t x_160; 
x_160 = !lean_is_exclusive(x_159);
if (x_160 == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_ctor_get(x_159, 0);
x_162 = l_Nat_Linear_Expr_inc(x_157);
x_163 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_161);
lean_ctor_set_uint8(x_163, sizeof(void*)*2, x_34);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_159, 0, x_164);
return x_159;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_165 = lean_ctor_get(x_159, 0);
x_166 = lean_ctor_get(x_159, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_159);
x_167 = l_Nat_Linear_Expr_inc(x_157);
x_168 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_168, 0, x_167);
lean_ctor_set(x_168, 1, x_165);
lean_ctor_set_uint8(x_168, sizeof(void*)*2, x_34);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_166);
return x_170;
}
}
else
{
uint8_t x_171; 
lean_dec(x_157);
x_171 = !lean_is_exclusive(x_159);
if (x_171 == 0)
{
return x_159;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_159, 0);
x_173 = lean_ctor_get(x_159, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_159);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_156);
if (x_175 == 0)
{
return x_156;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_156, 0);
x_177 = lean_ctor_get(x_156, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_156);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
}
}
}
else
{
lean_object* x_179; uint8_t x_180; 
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_11);
x_179 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_30, x_4, x_10);
x_180 = !lean_is_exclusive(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_181 = lean_ctor_get(x_179, 0);
x_182 = lean_ctor_get(x_179, 1);
x_183 = l_Lean_Expr_cleanupAnnotations(x_181);
x_184 = l_Lean_Name_mkStr1(x_22);
x_185 = l_Lean_Expr_isConstOf(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_186 = lean_box(0);
lean_ctor_set(x_179, 0, x_186);
return x_179;
}
else
{
lean_object* x_187; 
lean_free_object(x_179);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_187 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_182);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_189);
if (lean_obj_tag(x_190) == 0)
{
uint8_t x_191; 
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_193, 0, x_188);
lean_ctor_set(x_193, 1, x_192);
lean_ctor_set_uint8(x_193, sizeof(void*)*2, x_185);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_190, 0, x_194);
return x_190;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_195 = lean_ctor_get(x_190, 0);
x_196 = lean_ctor_get(x_190, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_190);
x_197 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_197, 0, x_188);
lean_ctor_set(x_197, 1, x_195);
lean_ctor_set_uint8(x_197, sizeof(void*)*2, x_185);
x_198 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_198, 0, x_197);
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_196);
return x_199;
}
}
else
{
uint8_t x_200; 
lean_dec(x_188);
x_200 = !lean_is_exclusive(x_190);
if (x_200 == 0)
{
return x_190;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
x_201 = lean_ctor_get(x_190, 0);
x_202 = lean_ctor_get(x_190, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_190);
x_203 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_203, 0, x_201);
lean_ctor_set(x_203, 1, x_202);
return x_203;
}
}
}
else
{
uint8_t x_204; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_204 = !lean_is_exclusive(x_187);
if (x_204 == 0)
{
return x_187;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_187, 0);
x_206 = lean_ctor_get(x_187, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_187);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_208 = lean_ctor_get(x_179, 0);
x_209 = lean_ctor_get(x_179, 1);
lean_inc(x_209);
lean_inc(x_208);
lean_dec(x_179);
x_210 = l_Lean_Expr_cleanupAnnotations(x_208);
x_211 = l_Lean_Name_mkStr1(x_22);
x_212 = l_Lean_Expr_isConstOf(x_210, x_211);
lean_dec(x_211);
lean_dec(x_210);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_213 = lean_box(0);
x_214 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_214, 0, x_213);
lean_ctor_set(x_214, 1, x_209);
return x_214;
}
else
{
lean_object* x_215; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_215 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_209);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_218, 1);
lean_inc(x_220);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_221 = x_218;
} else {
 lean_dec_ref(x_218);
 x_221 = lean_box(0);
}
x_222 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_222, 0, x_216);
lean_ctor_set(x_222, 1, x_219);
lean_ctor_set_uint8(x_222, sizeof(void*)*2, x_212);
x_223 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_223, 0, x_222);
if (lean_is_scalar(x_221)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_221;
}
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_220);
return x_224;
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_216);
x_225 = lean_ctor_get(x_218, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_218, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_227 = x_218;
} else {
 lean_dec_ref(x_218);
 x_227 = lean_box(0);
}
if (lean_is_scalar(x_227)) {
 x_228 = lean_alloc_ctor(1, 2, 0);
} else {
 x_228 = x_227;
}
lean_ctor_set(x_228, 0, x_225);
lean_ctor_set(x_228, 1, x_226);
return x_228;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_229 = lean_ctor_get(x_215, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_215, 1);
lean_inc(x_230);
if (lean_is_exclusive(x_215)) {
 lean_ctor_release(x_215, 0);
 lean_ctor_release(x_215, 1);
 x_231 = x_215;
} else {
 lean_dec_ref(x_215);
 x_231 = lean_box(0);
}
if (lean_is_scalar(x_231)) {
 x_232 = lean_alloc_ctor(1, 2, 0);
} else {
 x_232 = x_231;
}
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
return x_232;
}
}
}
}
}
}
else
{
lean_object* x_233; 
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_233 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_233) == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_234 = lean_ctor_get(x_233, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_233, 1);
lean_inc(x_235);
lean_dec(x_233);
x_236 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_235);
if (lean_obj_tag(x_236) == 0)
{
uint8_t x_237; 
x_237 = !lean_is_exclusive(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_238 = lean_ctor_get(x_236, 0);
x_239 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_239, 0, x_234);
lean_ctor_set(x_239, 1, x_238);
lean_ctor_set_uint8(x_239, sizeof(void*)*2, x_25);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_236, 0, x_240);
return x_236;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_236, 0);
x_242 = lean_ctor_get(x_236, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_236);
x_243 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_243, 0, x_234);
lean_ctor_set(x_243, 1, x_241);
lean_ctor_set_uint8(x_243, sizeof(void*)*2, x_25);
x_244 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_244, 0, x_243);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_242);
return x_245;
}
}
else
{
uint8_t x_246; 
lean_dec(x_234);
x_246 = !lean_is_exclusive(x_236);
if (x_246 == 0)
{
return x_236;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_236, 0);
x_248 = lean_ctor_get(x_236, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_236);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_250 = !lean_is_exclusive(x_233);
if (x_250 == 0)
{
return x_233;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_233, 0);
x_252 = lean_ctor_get(x_233, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_233);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
}
else
{
lean_object* x_254; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_11);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_254 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_20, x_2, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr(x_19, x_2, x_3, x_4, x_5, x_6, x_256);
if (lean_obj_tag(x_257) == 0)
{
uint8_t x_258; 
x_258 = !lean_is_exclusive(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; 
x_259 = lean_ctor_get(x_257, 0);
x_260 = lean_box(0);
x_261 = l_Nat_Linear_Expr_inc(x_255);
x_262 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_259);
x_263 = lean_unbox(x_260);
lean_ctor_set_uint8(x_262, sizeof(void*)*2, x_263);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_257, 0, x_264);
return x_257;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; lean_object* x_271; lean_object* x_272; 
x_265 = lean_ctor_get(x_257, 0);
x_266 = lean_ctor_get(x_257, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_257);
x_267 = lean_box(0);
x_268 = l_Nat_Linear_Expr_inc(x_255);
x_269 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_269, 0, x_268);
lean_ctor_set(x_269, 1, x_265);
x_270 = lean_unbox(x_267);
lean_ctor_set_uint8(x_269, sizeof(void*)*2, x_270);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_269);
x_272 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_272, 0, x_271);
lean_ctor_set(x_272, 1, x_266);
return x_272;
}
}
else
{
uint8_t x_273; 
lean_dec(x_255);
x_273 = !lean_is_exclusive(x_257);
if (x_273 == 0)
{
return x_257;
}
else
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; 
x_274 = lean_ctor_get(x_257, 0);
x_275 = lean_ctor_get(x_257, 1);
lean_inc(x_275);
lean_inc(x_274);
lean_dec(x_257);
x_276 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_276, 0, x_274);
lean_ctor_set(x_276, 1, x_275);
return x_276;
}
}
}
else
{
uint8_t x_277; 
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_277 = !lean_is_exclusive(x_254);
if (x_277 == 0)
{
return x_254;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_278 = lean_ctor_get(x_254, 0);
x_279 = lean_ctor_get(x_254, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_254);
x_280 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
return x_280;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_ToLinear_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearExpr), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; 
x_17 = lean_ctor_get(x_8, 1);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_sortExprs(x_12, x_20);
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Nat_Linear_Expr_applyPerm_go(x_24, x_11);
lean_dec(x_24);
lean_ctor_set(x_21, 1, x_23);
lean_ctor_set(x_21, 0, x_25);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = l_Nat_Linear_Expr_applyPerm_go(x_27, x_11);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_8, 0, x_29);
return x_8;
}
}
else
{
lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
x_30 = lean_box(1);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_sortExprs(x_12, x_31);
lean_dec(x_12);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_35 = x_32;
} else {
 lean_dec_ref(x_32);
 x_35 = lean_box(0);
}
x_36 = l_Nat_Linear_Expr_applyPerm_go(x_34, x_11);
lean_dec(x_34);
if (lean_is_scalar(x_35)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_35;
}
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_10);
return x_38;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toLinearCnstr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_ToLinear_toLinearCnstr_x3f), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_Meta_Simp_Arith_Nat_ToLinear_run___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
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
x_17 = !lean_is_exclusive(x_8);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_8, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_9);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_9, 1);
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_10);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_10, 0);
x_24 = lean_array_get_size(x_20);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_dec_le(x_24, x_25);
lean_dec(x_24);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; 
lean_free_object(x_9);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
x_29 = l_Lean_sortExprs(x_20, x_28);
lean_dec(x_20);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = l_Nat_Linear_ExprCnstr_applyPerm(x_32, x_23);
lean_dec(x_32);
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_33);
lean_ctor_set(x_10, 0, x_29);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 0);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_29);
x_36 = l_Nat_Linear_ExprCnstr_applyPerm(x_35, x_23);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_34);
lean_ctor_set(x_10, 0, x_37);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_ctor_set(x_9, 0, x_23);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_8, 0, x_10);
return x_8;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_array_get_size(x_20);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_dec_le(x_39, x_40);
lean_dec(x_39);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_free_object(x_9);
x_42 = lean_box(1);
x_43 = lean_unbox(x_42);
x_44 = l_Lean_sortExprs(x_20, x_43);
lean_dec(x_20);
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
x_48 = l_Nat_Linear_ExprCnstr_applyPerm(x_46, x_38);
lean_dec(x_46);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_8, 0, x_50);
return x_8;
}
else
{
lean_object* x_51; 
lean_ctor_set(x_9, 0, x_38);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_9);
lean_ctor_set(x_8, 0, x_51);
return x_8;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_52 = lean_ctor_get(x_9, 1);
lean_inc(x_52);
lean_dec(x_9);
x_53 = lean_ctor_get(x_10, 0);
lean_inc(x_53);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_54 = x_10;
} else {
 lean_dec_ref(x_10);
 x_54 = lean_box(0);
}
x_55 = lean_array_get_size(x_52);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_dec_le(x_55, x_56);
lean_dec(x_55);
if (x_57 == 0)
{
lean_object* x_58; uint8_t x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_box(1);
x_59 = lean_unbox(x_58);
x_60 = l_Lean_sortExprs(x_52, x_59);
lean_dec(x_52);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = l_Nat_Linear_ExprCnstr_applyPerm(x_62, x_53);
lean_dec(x_62);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_61);
if (lean_is_scalar(x_54)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_54;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_8, 0, x_66);
return x_8;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_53);
lean_ctor_set(x_67, 1, x_52);
if (lean_is_scalar(x_54)) {
 x_68 = lean_alloc_ctor(1, 1, 0);
} else {
 x_68 = x_54;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_8, 0, x_68);
return x_8;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
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
x_72 = lean_ctor_get(x_10, 0);
lean_inc(x_72);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_73 = x_10;
} else {
 lean_dec_ref(x_10);
 x_73 = lean_box(0);
}
x_74 = lean_array_get_size(x_70);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_71);
x_77 = lean_box(1);
x_78 = lean_unbox(x_77);
x_79 = l_Lean_sortExprs(x_70, x_78);
lean_dec(x_70);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
x_83 = l_Nat_Linear_ExprCnstr_applyPerm(x_81, x_72);
lean_dec(x_81);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_80);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(1, 1, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_69);
return x_86;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
if (lean_is_scalar(x_71)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_71;
}
lean_ctor_set(x_87, 0, x_72);
lean_ctor_set(x_87, 1, x_70);
if (lean_is_scalar(x_73)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_73;
}
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_69);
return x_89;
}
}
}
}
else
{
uint8_t x_90; 
x_90 = !lean_is_exclusive(x_8);
if (x_90 == 0)
{
return x_8;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_8, 0);
x_92 = lean_ctor_get(x_8, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_8);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed), 1, 0);
x_11 = lean_mk_string_unchecked("Nat", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(0);
x_14 = l_Lean_Expr_const___override(x_12, x_13);
x_15 = l_Lean_mkNatLit(x_7);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_RArray_toExpr___redArg(x_14, x_10, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed), 1, 0);
x_19 = lean_mk_string_unchecked("Nat", 3, 3);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Expr_const___override(x_20, x_21);
x_23 = l_Lean_RArray_ofArray(lean_box(0), x_1, lean_box(0));
x_24 = l_Lean_RArray_toExpr___redArg(x_22, x_18, x_23, x_2, x_3, x_4, x_5, x_6);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_Arith_Nat_toContextExpr___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lean_Util_SortExprs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KExprMap(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_RArray(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Nat_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_SortExprs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Offset(builtin, lean_io_mk_world());
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
l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExpr__lean);
l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprExprCnstr__lean);
l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean = _init_l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instReprPolyCnstr__lean);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearExpr);
l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr = _init_l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr();
lean_mark_persistent(l_Lean_Meta_Simp_Arith_Nat_instToExprLinearCnstr);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
