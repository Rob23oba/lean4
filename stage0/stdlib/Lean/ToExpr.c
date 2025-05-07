// Lean compiler output
// Module: Lean.ToExpr
// Imports: Lean.Expr Lean.ToLevel Init.Data.BitVec.Basic Init.Data.SInt.Basic
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
lean_object* l_Lean_mkNatLit(lean_object*);
uint32_t lean_int32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprBool;
uint8_t lean_int16_dec_le(uint16_t, uint16_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel(lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0(uint16_t);
LEAN_EXPORT lean_object* l_Lean_instToExprFin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lam__0(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* lean_int64_to_int_sint(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprString;
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0(uint16_t);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt8;
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0(uint64_t);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath___lam__0(lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0___boxed(lean_object*);
size_t lean_isize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkStrLit(lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* lean_int8_to_int(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64;
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprChar;
LEAN_EXPORT lean_object* l_Lean_instToExprName;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt32_mkNat(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved;
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0___boxed(lean_object*);
lean_object* l_BitVec_toNat(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
lean_object* lean_int32_to_int(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0(lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt64;
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0___boxed(lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprNat;
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0___boxed(lean_object*);
uint8_t lean_int64_dec_le(uint64_t, uint64_t);
uint8_t lean_int32_dec_le(uint32_t, uint32_t);
uint16_t lean_int16_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0___boxed(lean_object*);
uint8_t lean_isize_dec_le(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral;
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt32;
LEAN_EXPORT lean_object* l_Lean_instToExprInt64_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_toCtorIfLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0(size_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt16;
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16;
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprISize;
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0(uint64_t);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_int16_to_int(uint16_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0(uint32_t);
lean_object* l_Lean_mkRawNatLit(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUnit;
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___redArg(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
lean_object* lean_uint16_to_nat(uint16_t);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Expr_toCtorIfLit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32;
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_int8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprISize_mkNat(lean_object*);
uint64_t lean_int64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Expr_toCtorIfLit_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_int8_dec_le(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId;
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt8_mkNat(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprInt16_mkNat(lean_object*);
lean_object* lean_isize_to_int(size_t);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprFin(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath;
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lean_instToExprUSize;
static lean_object* _init_l_Lean_instToExprNat() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkNatLit), 1, 0);
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = lean_mk_string_unchecked("Int", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
x_14 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_8);
lean_inc(x_2);
x_17 = l_Lean_Expr_app___override(x_16, x_2);
x_18 = l_Lean_mkApp3(x_10, x_13, x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_int_dec_le(x_3, x_1);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_mk_string_unchecked("Neg", 3, 3);
x_6 = lean_mk_string_unchecked("neg", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = l_Lean_Level_ofNat(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_7, x_10);
x_12 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
x_18 = lean_int_neg(x_1);
x_19 = l_Int_toNat(x_18);
lean_dec(x_18);
x_20 = l_Lean_instToExprInt_mkNat(x_19);
x_21 = l_Lean_mkApp3(x_11, x_14, x_17, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Int_toNat(x_1);
x_23 = l_Lean_instToExprInt_mkNat(x_22);
return x_23;
}
}
}
static lean_object* _init_l_Lean_instToExprInt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprInt___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToExprInt___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Level_ofNat(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_6, x_10);
x_12 = lean_mk_string_unchecked("Fin", 3, 3);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
lean_inc(x_1);
x_15 = l_Lean_mkNatLit(x_1);
lean_inc(x_15);
x_16 = l_Lean_Expr_app___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_18 = l_Lean_Name_mkStr2(x_12, x_17);
x_19 = l_Lean_Expr_const___override(x_18, x_9);
x_20 = lean_mk_string_unchecked("Nat", 3, 3);
x_21 = lean_mk_string_unchecked("instNeZeroSucc", 14, 14);
x_22 = l_Lean_Name_mkStr2(x_20, x_21);
x_23 = l_Lean_Expr_const___override(x_22, x_9);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_1, x_24);
lean_dec(x_1);
x_26 = l_Lean_mkNatLit(x_25);
x_27 = l_Lean_Expr_app___override(x_23, x_26);
lean_inc(x_3);
x_28 = l_Lean_mkApp3(x_19, x_15, x_27, x_3);
x_29 = l_Lean_mkApp3(x_11, x_16, x_3, x_28);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFin(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprFin___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_mk_string_unchecked("Fin", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkNatLit(x_1);
x_8 = l_Lean_Expr_app___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_mk_string_unchecked("BitVec", 6, 6);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
lean_inc(x_1);
x_8 = l_Lean_mkNatLit(x_1);
x_9 = l_BitVec_toNat(x_1, x_2);
lean_dec(x_1);
x_10 = l_Lean_mkNatLit(x_9);
x_11 = l_Lean_mkAppB(x_7, x_8, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprBitVec___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_mk_string_unchecked("BitVec", 6, 6);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = l_Lean_mkNatLit(x_1);
x_8 = l_Lean_Expr_app___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBitVec___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_instToExprBitVec___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_uint8_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Level_ofNat(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_6, x_10);
x_12 = lean_mk_string_unchecked("UInt8", 5, 5);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
lean_inc(x_3);
x_18 = l_Lean_Expr_app___override(x_17, x_3);
x_19 = l_Lean_mkApp3(x_11, x_14, x_3, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_instToExprUInt8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprUInt8___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("UInt8", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt8___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprUInt8___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_uint16_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Level_ofNat(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_6, x_10);
x_12 = lean_mk_string_unchecked("UInt16", 6, 6);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
lean_inc(x_3);
x_18 = l_Lean_Expr_app___override(x_17, x_3);
x_19 = l_Lean_mkApp3(x_11, x_14, x_3, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_instToExprUInt16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprUInt16___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("UInt16", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt16___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprUInt16___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Level_ofNat(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_6, x_10);
x_12 = lean_mk_string_unchecked("UInt32", 6, 6);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
lean_inc(x_3);
x_18 = l_Lean_Expr_app___override(x_17, x_3);
x_19 = l_Lean_mkApp3(x_11, x_14, x_3, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_instToExprUInt32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprUInt32___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("UInt32", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt32___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprUInt32___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Level_ofNat(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_6, x_10);
x_12 = lean_mk_string_unchecked("UInt64", 6, 6);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
lean_inc(x_3);
x_18 = l_Lean_Expr_app___override(x_17, x_3);
x_19 = l_Lean_mkApp3(x_11, x_14, x_3, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_instToExprUInt64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprUInt64___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("UInt64", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprUInt64___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_2 = lean_usize_to_nat(x_1);
x_3 = l_Lean_mkRawNatLit(x_2);
x_4 = lean_mk_string_unchecked("OfNat", 5, 5);
x_5 = lean_mk_string_unchecked("ofNat", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_Lean_Level_ofNat(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_6, x_10);
x_12 = lean_mk_string_unchecked("USize", 5, 5);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
lean_inc(x_3);
x_18 = l_Lean_Expr_app___override(x_17, x_3);
x_19 = l_Lean_mkApp3(x_11, x_14, x_3, x_18);
return x_19;
}
}
static lean_object* _init_l_Lean_instToExprUSize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprUSize___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("USize", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUSize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprUSize___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = lean_mk_string_unchecked("Int8", 4, 4);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
x_14 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_15 = l_Lean_Name_mkStr2(x_11, x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_8);
lean_inc(x_2);
x_17 = l_Lean_Expr_app___override(x_16, x_2);
x_18 = l_Lean_mkApp3(x_10, x_13, x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0(uint8_t x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_int8_of_nat(x_2);
x_4 = lean_int8_dec_le(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_mk_string_unchecked("Neg", 3, 3);
x_6 = lean_mk_string_unchecked("neg", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = l_Lean_Level_ofNat(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_7, x_10);
x_12 = lean_mk_string_unchecked("Int8", 4, 4);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instNeg", 7, 7);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
x_18 = lean_int8_to_int(x_1);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = l_Int_toNat(x_19);
lean_dec(x_19);
x_21 = l_Lean_instToExprInt8_mkNat(x_20);
x_22 = l_Lean_mkApp3(x_11, x_14, x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_int8_to_int(x_1);
x_24 = l_Int_toNat(x_23);
lean_dec(x_23);
x_25 = l_Lean_instToExprInt8_mkNat(x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lean_instToExprInt8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprInt8___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Int8", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt8___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprInt8___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = lean_mk_string_unchecked("Int16", 5, 5);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
x_14 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_15 = l_Lean_Name_mkStr2(x_11, x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_8);
lean_inc(x_2);
x_17 = l_Lean_Expr_app___override(x_16, x_2);
x_18 = l_Lean_mkApp3(x_10, x_13, x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0(uint16_t x_1) {
_start:
{
lean_object* x_2; uint16_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_int16_of_nat(x_2);
x_4 = lean_int16_dec_le(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_mk_string_unchecked("Neg", 3, 3);
x_6 = lean_mk_string_unchecked("neg", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = l_Lean_Level_ofNat(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_7, x_10);
x_12 = lean_mk_string_unchecked("Int16", 5, 5);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instNeg", 7, 7);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
x_18 = lean_int16_to_int(x_1);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = l_Int_toNat(x_19);
lean_dec(x_19);
x_21 = l_Lean_instToExprInt16_mkNat(x_20);
x_22 = l_Lean_mkApp3(x_11, x_14, x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_int16_to_int(x_1);
x_24 = l_Int_toNat(x_23);
lean_dec(x_23);
x_25 = l_Lean_instToExprInt16_mkNat(x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lean_instToExprInt16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprInt16___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Int16", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt16___lam__0___boxed(lean_object* x_1) {
_start:
{
uint16_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprInt16___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = lean_mk_string_unchecked("Int32", 5, 5);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
x_14 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_15 = l_Lean_Name_mkStr2(x_11, x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_8);
lean_inc(x_2);
x_17 = l_Lean_Expr_app___override(x_16, x_2);
x_18 = l_Lean_mkApp3(x_10, x_13, x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_int32_of_nat(x_2);
x_4 = lean_int32_dec_le(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_mk_string_unchecked("Neg", 3, 3);
x_6 = lean_mk_string_unchecked("neg", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = l_Lean_Level_ofNat(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_7, x_10);
x_12 = lean_mk_string_unchecked("Int32", 5, 5);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instNeg", 7, 7);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
x_18 = lean_int32_to_int(x_1);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = l_Int_toNat(x_19);
lean_dec(x_19);
x_21 = l_Lean_instToExprInt32_mkNat(x_20);
x_22 = l_Lean_mkApp3(x_11, x_14, x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_int32_to_int(x_1);
x_24 = l_Int_toNat(x_23);
lean_dec(x_23);
x_25 = l_Lean_instToExprInt32_mkNat(x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lean_instToExprInt32() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprInt32___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Int32", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt32___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprInt32___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = lean_mk_string_unchecked("Int64", 5, 5);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
x_14 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_15 = l_Lean_Name_mkStr2(x_11, x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_8);
lean_inc(x_2);
x_17 = l_Lean_Expr_app___override(x_16, x_2);
x_18 = l_Lean_mkApp3(x_10, x_13, x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_int64_of_nat(x_2);
x_4 = lean_int64_dec_le(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_mk_string_unchecked("Neg", 3, 3);
x_6 = lean_mk_string_unchecked("neg", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = l_Lean_Level_ofNat(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_7, x_10);
x_12 = lean_mk_string_unchecked("Int64", 5, 5);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instNeg", 7, 7);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
x_18 = lean_int64_to_int_sint(x_1);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = l_Int_toNat(x_19);
lean_dec(x_19);
x_21 = l_Lean_instToExprInt64_mkNat(x_20);
x_22 = l_Lean_mkApp3(x_11, x_14, x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_int64_to_int_sint(x_1);
x_24 = l_Int_toNat(x_23);
lean_dec(x_23);
x_25 = l_Lean_instToExprInt64_mkNat(x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lean_instToExprInt64() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprInt64___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Int64", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprInt64___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprInt64___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize_mkNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_2 = l_Lean_mkRawNatLit(x_1);
x_3 = lean_mk_string_unchecked("OfNat", 5, 5);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_Lean_Level_ofNat(x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_5, x_9);
x_11 = lean_mk_string_unchecked("ISize", 5, 5);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
x_14 = lean_mk_string_unchecked("instOfNat", 9, 9);
x_15 = l_Lean_Name_mkStr2(x_11, x_14);
x_16 = l_Lean_Expr_const___override(x_15, x_8);
lean_inc(x_2);
x_17 = l_Lean_Expr_app___override(x_16, x_2);
x_18 = l_Lean_mkApp3(x_10, x_13, x_2, x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0(size_t x_1) {
_start:
{
lean_object* x_2; size_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_isize_of_nat(x_2);
x_4 = lean_isize_dec_le(x_3, x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_5 = lean_mk_string_unchecked("Neg", 3, 3);
x_6 = lean_mk_string_unchecked("neg", 3, 3);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = l_Lean_Level_ofNat(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Expr_const___override(x_7, x_10);
x_12 = lean_mk_string_unchecked("ISize", 5, 5);
lean_inc(x_12);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_9);
x_15 = lean_mk_string_unchecked("instNeg", 7, 7);
x_16 = l_Lean_Name_mkStr2(x_12, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
x_18 = lean_isize_to_int(x_1);
x_19 = lean_int_neg(x_18);
lean_dec(x_18);
x_20 = l_Int_toNat(x_19);
lean_dec(x_19);
x_21 = l_Lean_instToExprISize_mkNat(x_20);
x_22 = l_Lean_mkApp3(x_11, x_14, x_17, x_21);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_isize_to_int(x_1);
x_24 = l_Int_toNat(x_23);
lean_dec(x_23);
x_25 = l_Lean_instToExprISize_mkNat(x_24);
return x_25;
}
}
}
static lean_object* _init_l_Lean_instToExprISize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprISize___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("ISize", 5, 5);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprISize___lam__0___boxed(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; 
x_2 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprISize___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = lean_mk_string_unchecked("false", 5, 5);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_mk_string_unchecked("Bool", 4, 4);
x_8 = lean_mk_string_unchecked("true", 4, 4);
x_9 = l_Lean_Name_mkStr2(x_7, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_const___override(x_9, x_10);
return x_11;
}
}
}
static lean_object* _init_l_Lean_instToExprBool() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprBool___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Bool", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprBool___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprBool___lam__0(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = lean_mk_string_unchecked("ofNat", 5, 5);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_uint32_to_nat(x_1);
x_8 = l_Lean_mkRawNatLit(x_7);
x_9 = l_Lean_Expr_app___override(x_6, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_instToExprChar() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprChar___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Char", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprChar___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lean_instToExprChar___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToExprString() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_mkStrLit), 1, 0);
x_2 = lean_mk_string_unchecked("String", 6, 6);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("Unit", 4, 4);
x_3 = lean_mk_string_unchecked("unit", 4, 4);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instToExprUnit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprUnit___lam__0___boxed), 1, 0);
x_2 = lean_mk_string_unchecked("Unit", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprUnit___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_instToExprUnit___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("System", 6, 6);
x_3 = lean_mk_string_unchecked("FilePath", 8, 8);
x_4 = lean_mk_string_unchecked("mk", 2, 2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = l_Lean_mkStrLit(x_1);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_instToExprFilePath() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprFilePath___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("System", 6, 6);
x_3 = lean_mk_string_unchecked("FilePath", 8, 8);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_lt(x_11, x_2);
if (x_12 == 0)
{
x_3 = x_12;
goto block_10;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(8u);
x_14 = lean_nat_dec_le(x_2, x_13);
x_3 = x_14;
goto block_10;
}
block_10:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_dec(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_2);
x_1 = x_4;
x_2 = x_6;
goto _start;
}
default: 
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Name", 4, 4);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_mk_string_unchecked("mkStr", 5, 5);
lean_inc(x_2);
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = l_Lean_Name_str___override(x_6, x_9);
x_11 = lean_box(0);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = l_Lean_Expr_const___override(x_10, x_11);
x_13 = l_Array_reverse(lean_box(0), x_3);
x_14 = l_Lean_mkAppN(x_12, x_13);
lean_dec(x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_10);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_add(x_2, x_17);
lean_dec(x_2);
x_19 = l_Lean_mkStrLit(x_16);
x_20 = lean_array_push(x_3, x_19);
x_1 = x_15;
x_2 = x_18;
x_3 = x_20;
goto _start;
}
default: 
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_mk_string_unchecked("Lean.ToExpr", 11, 11);
x_23 = lean_mk_string_unchecked("_private.Lean.ToExpr.0.Lean.Name.toExprAux.mkStr", 48, 48);
x_24 = lean_unsigned_to_nat(202u);
x_25 = lean_unsigned_to_nat(11u);
x_26 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_27 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_22, x_23, x_24, x_25, x_26);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_28 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Name", 4, 4);
x_4 = lean_mk_string_unchecked("anonymous", 9, 9);
x_5 = lean_box(0);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_6; lean_object* x_7; 
x_6 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_7 = l_Lean_Expr_const___override(x_6, x_5);
return x_7;
}
case 1:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("str", 3, 3);
x_11 = l_Lean_Name_mkStr3(x_2, x_3, x_10);
x_12 = l_Lean_Expr_const___override(x_11, x_5);
x_13 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_8);
x_14 = l_Lean_mkStrLit(x_9);
x_15 = l_Lean_mkAppB(x_12, x_13, x_14);
return x_15;
}
default: 
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
lean_dec(x_1);
x_18 = lean_mk_string_unchecked("num", 3, 3);
x_19 = l_Lean_Name_mkStr3(x_2, x_3, x_18);
x_20 = l_Lean_Expr_const___override(x_19, x_5);
x_21 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_16);
x_22 = l_Lean_mkNatLit(x_17);
x_23 = l_Lean_mkAppB(x_20, x_21, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_isSimple(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_go(x_1);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_mk_empty_array_with_capacity(x_2);
x_6 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux_mkStr(x_1, x_2, x_5);
return x_6;
}
}
}
static lean_object* _init_l_Lean_instToExprName() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_ToExpr_0__Lean_Name_toExprAux), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Name", 4, 4);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_3);
x_5 = lean_mk_string_unchecked("Option", 6, 6);
x_6 = lean_mk_string_unchecked("none", 4, 4);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_Expr_const___override(x_7, x_9);
x_11 = l_Lean_Expr_app___override(x_10, x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
lean_dec(x_4);
x_13 = lean_mk_string_unchecked("Option", 6, 6);
x_14 = lean_mk_string_unchecked("some", 4, 4);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_Expr_const___override(x_15, x_17);
x_19 = lean_ctor_get(x_3, 0);
lean_inc(x_19);
lean_dec(x_3);
x_20 = lean_apply_1(x_19, x_12);
x_21 = l_Lean_mkAppB(x_18, x_2, x_20);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_instToExprOptionOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_mk_string_unchecked("Option", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Expr_const___override(x_6, x_8);
x_10 = l_Lean_Expr_app___override(x_9, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprOptionOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instToExprOptionOfToLevel___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_apply_1(x_7, x_5);
lean_inc(x_3);
x_9 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_2, x_3, x_6);
x_10 = l_Lean_mkAppB(x_3, x_8, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_ToExpr_0__Lean_List_toExprAux(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
x_4 = lean_mk_string_unchecked("List", 4, 4);
x_5 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_4);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_inc(x_8);
x_9 = l_Lean_Expr_const___override(x_6, x_8);
lean_inc(x_3);
x_10 = l_Lean_Expr_app___override(x_9, x_3);
x_11 = lean_mk_string_unchecked("cons", 4, 4);
lean_inc(x_4);
x_12 = l_Lean_Name_mkStr2(x_4, x_11);
lean_inc(x_8);
x_13 = l_Lean_Expr_const___override(x_12, x_8);
lean_inc(x_3);
x_14 = l_Lean_Expr_app___override(x_13, x_3);
x_15 = lean_alloc_closure((void*)(l___private_Lean_ToExpr_0__Lean_List_toExprAux___boxed), 5, 4);
lean_closure_set(x_15, 0, lean_box(0));
lean_closure_set(x_15, 1, x_2);
lean_closure_set(x_15, 2, x_10);
lean_closure_set(x_15, 3, x_14);
x_16 = l_Lean_Name_mkStr1(x_4);
x_17 = l_Lean_Expr_const___override(x_16, x_8);
x_18 = l_Lean_Expr_app___override(x_17, x_3);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprListOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instToExprListOfToLevel___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_5 = lean_mk_string_unchecked("List", 4, 4);
x_6 = lean_mk_string_unchecked("toArray", 7, 7);
lean_inc(x_5);
x_7 = l_Lean_Name_mkStr2(x_5, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
lean_inc(x_9);
x_10 = l_Lean_Expr_const___override(x_7, x_9);
x_11 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_5);
x_12 = l_Lean_Name_mkStr2(x_5, x_11);
lean_inc(x_9);
x_13 = l_Lean_Expr_const___override(x_12, x_9);
lean_inc(x_2);
x_14 = l_Lean_Expr_app___override(x_13, x_2);
x_15 = lean_mk_string_unchecked("cons", 4, 4);
x_16 = l_Lean_Name_mkStr2(x_5, x_15);
x_17 = l_Lean_Expr_const___override(x_16, x_9);
lean_inc(x_2);
x_18 = l_Lean_Expr_app___override(x_17, x_2);
x_19 = lean_array_to_list(x_4);
x_20 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_3, x_14, x_18, x_19);
lean_dec(x_14);
x_21 = l_Lean_mkAppB(x_10, x_2, x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_inc(x_3);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lean_instToExprArrayOfToLevel___redArg___lam__0), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_3);
lean_closure_set(x_4, 2, x_2);
x_5 = lean_mk_string_unchecked("Array", 5, 5);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Expr_const___override(x_6, x_8);
x_10 = l_Lean_Expr_app___override(x_9, x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprArrayOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instToExprArrayOfToLevel___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_mk_string_unchecked("Prod", 4, 4);
x_12 = lean_mk_string_unchecked("mk", 2, 2);
x_13 = l_Lean_Name_mkStr2(x_11, x_12);
x_14 = lean_box(0);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 1, x_14);
lean_ctor_set(x_7, 0, x_1);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_7);
x_16 = l_Lean_Expr_const___override(x_13, x_15);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
lean_dec(x_3);
x_18 = lean_apply_1(x_17, x_9);
x_19 = lean_ctor_get(x_4, 0);
lean_inc(x_19);
lean_dec(x_4);
x_20 = lean_apply_1(x_19, x_10);
x_21 = l_Lean_mkApp4(x_16, x_5, x_6, x_18, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = lean_mk_string_unchecked("Prod", 4, 4);
x_25 = lean_mk_string_unchecked("mk", 2, 2);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_Lean_Expr_const___override(x_26, x_29);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_apply_1(x_31, x_22);
x_33 = lean_ctor_get(x_4, 0);
lean_inc(x_33);
lean_dec(x_4);
x_34 = lean_apply_1(x_33, x_23);
x_35 = l_Lean_mkApp4(x_30, x_5, x_6, x_32, x_34);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
lean_inc(x_2);
x_7 = lean_alloc_closure((void*)(l_Lean_instToExprProdOfToLevel___redArg___lam__0), 7, 6);
lean_closure_set(x_7, 0, x_2);
lean_closure_set(x_7, 1, x_1);
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
lean_closure_set(x_7, 4, x_5);
lean_closure_set(x_7, 5, x_6);
x_8 = lean_mk_string_unchecked("Prod", 4, 4);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_Expr_const___override(x_9, x_12);
x_14 = l_Lean_mkAppB(x_13, x_5, x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprProdOfToLevel(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_instToExprProdOfToLevel___redArg(x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprLiteral___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Literal", 7, 7);
x_4 = lean_mk_string_unchecked("natVal", 6, 6);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = l_Lean_Expr_lit___override(x_1);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
x_11 = lean_mk_string_unchecked("Literal", 7, 7);
x_12 = lean_mk_string_unchecked("strVal", 6, 6);
x_13 = l_Lean_Name_mkStr3(x_10, x_11, x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_13, x_14);
x_16 = l_Lean_Expr_lit___override(x_1);
x_17 = l_Lean_Expr_app___override(x_15, x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lean_instToExprLiteral() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprLiteral___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Literal", 7, 7);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprFVarId___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("FVarId", 6, 6);
x_4 = lean_mk_string_unchecked("mk", 2, 2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = l_Lean_Expr_const___override(x_5, x_6);
x_8 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_1);
x_9 = l_Lean_Expr_app___override(x_7, x_8);
return x_9;
}
}
static lean_object* _init_l_Lean_instToExprFVarId() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToExprFVarId___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("FVarId", 6, 6);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_instToExprPreresolved___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Syntax", 6, 6);
x_6 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_7 = lean_mk_string_unchecked("namespace", 9, 9);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_8, x_9);
x_11 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_3);
x_12 = l_Lean_Expr_app___override(x_10, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_mk_string_unchecked("Lean", 4, 4);
x_17 = lean_mk_string_unchecked("Syntax", 6, 6);
x_18 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_19 = lean_mk_string_unchecked("decl", 4, 4);
x_20 = l_Lean_Name_mkStr4(x_16, x_17, x_18, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Expr_const___override(x_20, x_21);
x_23 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_14);
x_24 = lean_mk_string_unchecked("String", 6, 6);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Expr_const___override(x_25, x_21);
x_27 = lean_mk_string_unchecked("List", 4, 4);
x_28 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_27);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
x_30 = lean_box(0);
lean_ctor_set(x_2, 1, x_21);
lean_ctor_set(x_2, 0, x_30);
lean_inc(x_2);
x_31 = l_Lean_Expr_const___override(x_29, x_2);
lean_inc(x_26);
x_32 = l_Lean_Expr_app___override(x_31, x_26);
x_33 = lean_mk_string_unchecked("cons", 4, 4);
x_34 = l_Lean_Name_mkStr2(x_27, x_33);
x_35 = l_Lean_Expr_const___override(x_34, x_2);
x_36 = l_Lean_Expr_app___override(x_35, x_26);
x_37 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_32, x_36, x_15);
lean_dec(x_32);
x_38 = l_Lean_mkAppB(x_22, x_23, x_37);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_2);
x_41 = lean_mk_string_unchecked("Lean", 4, 4);
x_42 = lean_mk_string_unchecked("Syntax", 6, 6);
x_43 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_44 = lean_mk_string_unchecked("decl", 4, 4);
x_45 = l_Lean_Name_mkStr4(x_41, x_42, x_43, x_44);
x_46 = lean_box(0);
x_47 = l_Lean_Expr_const___override(x_45, x_46);
x_48 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_39);
x_49 = lean_mk_string_unchecked("String", 6, 6);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = l_Lean_Expr_const___override(x_50, x_46);
x_52 = lean_mk_string_unchecked("List", 4, 4);
x_53 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_52);
x_54 = l_Lean_Name_mkStr2(x_52, x_53);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_46);
lean_inc(x_56);
x_57 = l_Lean_Expr_const___override(x_54, x_56);
lean_inc(x_51);
x_58 = l_Lean_Expr_app___override(x_57, x_51);
x_59 = lean_mk_string_unchecked("cons", 4, 4);
x_60 = l_Lean_Name_mkStr2(x_52, x_59);
x_61 = l_Lean_Expr_const___override(x_60, x_56);
x_62 = l_Lean_Expr_app___override(x_61, x_51);
x_63 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___redArg(x_1, x_58, x_62, x_40);
lean_dec(x_58);
x_64 = l_Lean_mkAppB(x_47, x_48, x_63);
return x_64;
}
}
}
}
static lean_object* _init_l_Lean_instToExprPreresolved() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = l_Lean_instToExprString;
x_2 = lean_alloc_closure((void*)(l_Lean_instToExprPreresolved___lam__0), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Syntax", 6, 6);
x_5 = lean_mk_string_unchecked("Preresolved", 11, 11);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Expr_toCtorIfLit_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_mk_string_unchecked("Char", 4, 4);
x_7 = lean_mk_string_unchecked("ofNat", 5, 5);
x_8 = l_Lean_Name_mkStr2(x_6, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_8, x_9);
x_11 = lean_unbox_uint32(x_4);
lean_dec(x_4);
x_12 = lean_uint32_to_nat(x_11);
x_13 = l_Lean_mkRawNatLit(x_12);
x_14 = l_Lean_Expr_app___override(x_10, x_13);
lean_inc(x_2);
x_15 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Expr_toCtorIfLit_spec__0(x_1, x_2, x_5);
x_16 = l_Lean_mkAppB(x_2, x_14, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toCtorIfLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 9)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_mk_string_unchecked("Nat", 3, 3);
x_7 = lean_mk_string_unchecked("succ", 4, 4);
x_8 = l_Lean_Name_mkStr2(x_6, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_3, x_11);
lean_dec(x_3);
x_13 = l_Lean_mkRawNatLit(x_12);
x_14 = l_Lean_Expr_app___override(x_10, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
x_15 = lean_mk_string_unchecked("Nat", 3, 3);
x_16 = lean_mk_string_unchecked("zero", 4, 4);
x_17 = l_Lean_Name_mkStr2(x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_const___override(x_17, x_18);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_20 = lean_ctor_get(x_2, 0);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_mk_string_unchecked("String", 6, 6);
x_22 = lean_mk_string_unchecked("mk", 2, 2);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = lean_box(0);
x_25 = l_Lean_Expr_const___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("Char", 4, 4);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = l_Lean_Expr_const___override(x_27, x_24);
x_29 = lean_mk_string_unchecked("List", 4, 4);
x_30 = lean_mk_string_unchecked("nil", 3, 3);
lean_inc(x_29);
x_31 = l_Lean_Name_mkStr2(x_29, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_24);
lean_inc(x_33);
x_34 = l_Lean_Expr_const___override(x_31, x_33);
lean_inc(x_28);
x_35 = l_Lean_Expr_app___override(x_34, x_28);
x_36 = lean_mk_string_unchecked("cons", 4, 4);
x_37 = l_Lean_Name_mkStr2(x_29, x_36);
x_38 = l_Lean_Expr_const___override(x_37, x_33);
x_39 = l_Lean_Expr_app___override(x_38, x_28);
x_40 = lean_string_data(x_20);
x_41 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Expr_toCtorIfLit_spec__0(x_35, x_39, x_40);
lean_dec(x_35);
x_42 = l_Lean_Expr_app___override(x_25, x_41);
return x_42;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Expr_toCtorIfLit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_ToExpr_0__Lean_List_toExprAux___at___Lean_Expr_toCtorIfLit_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ToLevel(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instToExprNat = _init_l_Lean_instToExprNat();
lean_mark_persistent(l_Lean_instToExprNat);
l_Lean_instToExprInt = _init_l_Lean_instToExprInt();
lean_mark_persistent(l_Lean_instToExprInt);
l_Lean_instToExprUInt8 = _init_l_Lean_instToExprUInt8();
lean_mark_persistent(l_Lean_instToExprUInt8);
l_Lean_instToExprUInt16 = _init_l_Lean_instToExprUInt16();
lean_mark_persistent(l_Lean_instToExprUInt16);
l_Lean_instToExprUInt32 = _init_l_Lean_instToExprUInt32();
lean_mark_persistent(l_Lean_instToExprUInt32);
l_Lean_instToExprUInt64 = _init_l_Lean_instToExprUInt64();
lean_mark_persistent(l_Lean_instToExprUInt64);
l_Lean_instToExprUSize = _init_l_Lean_instToExprUSize();
lean_mark_persistent(l_Lean_instToExprUSize);
l_Lean_instToExprInt8 = _init_l_Lean_instToExprInt8();
lean_mark_persistent(l_Lean_instToExprInt8);
l_Lean_instToExprInt16 = _init_l_Lean_instToExprInt16();
lean_mark_persistent(l_Lean_instToExprInt16);
l_Lean_instToExprInt32 = _init_l_Lean_instToExprInt32();
lean_mark_persistent(l_Lean_instToExprInt32);
l_Lean_instToExprInt64 = _init_l_Lean_instToExprInt64();
lean_mark_persistent(l_Lean_instToExprInt64);
l_Lean_instToExprISize = _init_l_Lean_instToExprISize();
lean_mark_persistent(l_Lean_instToExprISize);
l_Lean_instToExprBool = _init_l_Lean_instToExprBool();
lean_mark_persistent(l_Lean_instToExprBool);
l_Lean_instToExprChar = _init_l_Lean_instToExprChar();
lean_mark_persistent(l_Lean_instToExprChar);
l_Lean_instToExprString = _init_l_Lean_instToExprString();
lean_mark_persistent(l_Lean_instToExprString);
l_Lean_instToExprUnit = _init_l_Lean_instToExprUnit();
lean_mark_persistent(l_Lean_instToExprUnit);
l_Lean_instToExprFilePath = _init_l_Lean_instToExprFilePath();
lean_mark_persistent(l_Lean_instToExprFilePath);
l_Lean_instToExprName = _init_l_Lean_instToExprName();
lean_mark_persistent(l_Lean_instToExprName);
l_Lean_instToExprLiteral = _init_l_Lean_instToExprLiteral();
lean_mark_persistent(l_Lean_instToExprLiteral);
l_Lean_instToExprFVarId = _init_l_Lean_instToExprFVarId();
lean_mark_persistent(l_Lean_instToExprFVarId);
l_Lean_instToExprPreresolved = _init_l_Lean_instToExprPreresolved();
lean_mark_persistent(l_Lean_instToExprPreresolved);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
