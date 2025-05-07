// Lean compiler output
// Module: Lean.Compiler.ConstFolding
// Imports: Lean.Expr
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
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___redArg(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_boolFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_uintBinFoldFns_spec__1_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsTrue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLe(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_natFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___redArg(lean_object*, lean_object*);
lean_object* l_Nat_div___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_foldNatDecLt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_uintBinFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr___boxed(lean_object*, lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_fold_bin_op(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinOp(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_preUIntBinFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_uintFoldToNatFns_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd(uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_numScalarTypes;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr(uint8_t, lean_object*, uint8_t);
extern lean_object* l_System_Platform_numBits;
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt(uint8_t, lean_object*, lean_object*);
lean_object* l_Nat_mul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_fold_un_op(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_uintFoldToNatFns;
LEAN_EXPORT lean_object* lean_get_num_lit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_add___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinBoolPred(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinOp___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_natPowThreshold;
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_binFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn___boxed(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_foldNatDecLe___lam__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___boxed(lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_uintBinFoldFns_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___redArg(lean_object*, lean_object*);
lean_object* l_Lean_mkDecIsFalse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_levelOne;
lean_object* lean_nat_mul(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat(uint8_t, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUnOp___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_foldNatDecEq___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_uintBinFoldFns_spec__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_unFoldFns;
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___redArg(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntTypeName(lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_mod___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lam__0(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_mkLcProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("lcProof", 7, 7);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = l_Lean_Expr_app___override(x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntTypeName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("UInt", 4, 4);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_4 = lean_string_append(x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Name_str___override(x_5, x_4);
return x_6;
}
}
static lean_object* _init_l_Lean_Compiler_numScalarTypes() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = l_Lean_Compiler_mkUIntTypeName(x_1);
x_3 = lean_mk_string_unchecked("ofNat", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_str___override(x_2, x_3);
x_5 = lean_mk_string_unchecked("toNat", 5, 5);
lean_inc(x_5);
lean_inc(x_2);
x_6 = l_Lean_Name_str___override(x_2, x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_pow(x_7, x_1);
x_9 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set(x_9, 2, x_4);
lean_ctor_set(x_9, 3, x_6);
lean_ctor_set(x_9, 4, x_8);
x_10 = lean_unsigned_to_nat(16u);
x_11 = l_Lean_Compiler_mkUIntTypeName(x_10);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Name_str___override(x_11, x_3);
lean_inc(x_5);
lean_inc(x_11);
x_13 = l_Lean_Name_str___override(x_11, x_5);
x_14 = lean_nat_pow(x_7, x_10);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_12);
lean_ctor_set(x_15, 3, x_13);
lean_ctor_set(x_15, 4, x_14);
x_16 = lean_unsigned_to_nat(32u);
x_17 = l_Lean_Compiler_mkUIntTypeName(x_16);
lean_inc(x_3);
lean_inc(x_17);
x_18 = l_Lean_Name_str___override(x_17, x_3);
lean_inc(x_5);
lean_inc(x_17);
x_19 = l_Lean_Name_str___override(x_17, x_5);
x_20 = lean_nat_pow(x_7, x_16);
x_21 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_21, 0, x_16);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_18);
lean_ctor_set(x_21, 3, x_19);
lean_ctor_set(x_21, 4, x_20);
x_22 = lean_unsigned_to_nat(64u);
x_23 = l_Lean_Compiler_mkUIntTypeName(x_22);
lean_inc(x_3);
lean_inc(x_23);
x_24 = l_Lean_Name_str___override(x_23, x_3);
lean_inc(x_5);
lean_inc(x_23);
x_25 = l_Lean_Name_str___override(x_23, x_5);
x_26 = lean_nat_pow(x_7, x_22);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_24);
lean_ctor_set(x_27, 3, x_25);
lean_ctor_set(x_27, 4, x_26);
x_28 = l_System_Platform_numBits;
x_29 = lean_mk_string_unchecked("USize", 5, 5);
x_30 = l_Lean_Name_mkStr1(x_29);
lean_inc(x_30);
x_31 = l_Lean_Name_str___override(x_30, x_3);
lean_inc(x_30);
x_32 = l_Lean_Name_str___override(x_30, x_5);
x_33 = lean_nat_pow(x_7, x_28);
x_34 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_34, 0, x_28);
lean_ctor_set(x_34, 1, x_30);
lean_ctor_set(x_34, 2, x_31);
lean_ctor_set(x_34, 3, x_32);
lean_ctor_set(x_34, 4, x_33);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_27);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_21);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_15);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_9);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isOfNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_isOfNat___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Compiler_numScalarTypes;
x_4 = l_List_any___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_isOfNat___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isOfNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isOfNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 3);
x_4 = lean_name_eq(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_isToNat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_isToNat___lam__0___boxed), 2, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = l_Lean_Compiler_numScalarTypes;
x_4 = l_List_any___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_isToNat___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_isToNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_isToNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn(lean_object* x_1, lean_object* x_2) {
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
x_6 = lean_ctor_get(x_4, 2);
x_7 = lean_name_eq(x_6, x_1);
if (x_7 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_4);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getInfoFromFn(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_Compiler_numScalarTypes;
x_5 = l_Lean_Compiler_getInfoFromFn(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
}
else
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getInfoFromVal___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_getInfoFromVal(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_get_num_lit(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Compiler_isOfNat(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
x_1 = x_3;
goto _start;
}
}
else
{
lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
}
case 9:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_ctor_set_tag(x_9, 1);
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
else
{
lean_object* x_13; 
lean_dec(x_9);
x_13 = lean_box(0);
return x_13;
}
}
default: 
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_ctor_get(x_1, 4);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_nat_mod(x_2, x_6);
lean_dec(x_6);
x_8 = l_Lean_mkRawNatLit(x_7);
x_9 = l_Lean_Expr_app___override(x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUIntLit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_mkUIntLit(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_2 = lean_unsigned_to_nat(32u);
x_3 = l_Lean_Compiler_mkUIntTypeName(x_2);
x_4 = lean_mk_string_unchecked("ofNat", 5, 5);
lean_inc(x_3);
x_5 = l_Lean_Name_str___override(x_3, x_4);
x_6 = lean_mk_string_unchecked("toNat", 5, 5);
lean_inc(x_3);
x_7 = l_Lean_Name_str___override(x_3, x_6);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_pow(x_8, x_2);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_9);
x_11 = l_Lean_Compiler_mkUIntLit(x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkUInt32Lit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_mkUInt32Lit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_inc(x_3);
x_5 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_get_num_lit(x_4);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_Compiler_getInfoFromVal(x_3);
lean_dec(x_3);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_box(x_2);
lean_inc(x_14);
x_16 = lean_apply_4(x_1, x_14, x_15, x_7, x_10);
x_17 = l_Lean_Compiler_mkUIntLit(x_14, x_16);
lean_dec(x_16);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_box(x_2);
lean_inc(x_18);
x_20 = lean_apply_4(x_1, x_18, x_19, x_7, x_10);
x_21 = l_Lean_Compiler_mkUIntLit(x_18, x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinUInt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldBinUInt(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_add(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntAdd___lam__0___boxed), 4, 0);
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntAdd___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntAdd(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mul(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMul___lam__0___boxed), 4, 0);
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntMul___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntMul(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_div(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntDiv___lam__0___boxed), 4, 0);
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntDiv___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntDiv(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_nat_mod(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMod___lam__0___boxed), 4, 0);
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntMod___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntMod(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 4);
x_6 = lean_nat_sub(x_5, x_4);
x_7 = lean_nat_add(x_3, x_6);
lean_dec(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntSub___lam__0___boxed), 4, 0);
x_5 = l_Lean_Compiler_foldBinUInt(x_4, x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Compiler_foldUIntSub___lam__0(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUIntSub___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldUIntSub(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_preUIntBinFoldFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_1 = lean_mk_string_unchecked("add", 3, 3);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntAdd___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_mk_string_unchecked("mul", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMul___boxed), 3, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_mk_string_unchecked("div", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntDiv___boxed), 3, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("mod", 3, 3);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntMod___boxed), 3, 0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("sub", 3, 3);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_closure((void*)(l_Lean_Compiler_foldUIntSub___boxed), 3, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_uintBinFoldFns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = l_Lean_Name_append(x_10, x_9);
lean_ctor_set(x_6, 0, x_11);
lean_ctor_set(x_2, 1, x_3);
{
lean_object* _tmp_1 = x_8;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_6);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
x_17 = l_Lean_Name_append(x_16, x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_18);
{
lean_object* _tmp_1 = x_13;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_24 = x_20;
} else {
 lean_dec_ref(x_20);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
x_26 = l_Lean_Name_append(x_25, x_22);
if (lean_is_scalar(x_24)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_24;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_23);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_3);
x_2 = x_21;
x_3 = x_28;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___List_foldl___at___Lean_Compiler_uintBinFoldFns_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Compiler_preUIntBinFoldFns;
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at___Lean_Compiler_uintBinFoldFns_spec__0(x_3, x_5, x_6);
x_8 = l_List_appendTR(lean_box(0), x_1, x_7);
x_1 = x_8;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_uintBinFoldFns_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Compiler_preUIntBinFoldFns;
x_6 = lean_box(0);
x_7 = l_List_mapTR_loop___at___Lean_Compiler_uintBinFoldFns_spec__0(x_3, x_5, x_6);
x_8 = l_List_appendTR(lean_box(0), x_1, x_7);
x_9 = l_List_foldl___at___List_foldl___at___Lean_Compiler_uintBinFoldFns_spec__1_spec__1(x_8, x_4);
return x_9;
}
}
}
static lean_object* _init_l_Lean_Compiler_uintBinFoldFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes;
x_3 = l_List_foldl___at___Lean_Compiler_uintBinFoldFns_spec__1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinOp(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = l_Lean_mkRawNatLit(x_11);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_apply_2(x_1, x_6, x_13);
x_15 = l_Lean_mkRawNatLit(x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Nat_add___boxed), 2, 0);
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatAdd___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatAdd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatAdd(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Nat_mul___boxed), 2, 0);
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatMul___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMul___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatMul(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Nat_div___boxed), 2, 0);
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatDiv___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDiv___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDiv(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Nat_mod___boxed), 2, 0);
x_4 = l_Lean_Compiler_foldNatBinOp(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatMod___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatMod___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatMod(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_natPowThreshold() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(256u);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_unsigned_to_nat(256u);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_free_object(x_6);
lean_dec(x_9);
lean_dec(x_5);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_nat_pow(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
x_14 = l_Lean_mkRawNatLit(x_13);
lean_ctor_set(x_6, 0, x_14);
return x_6;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_unsigned_to_nat(256u);
x_17 = lean_nat_dec_lt(x_15, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_5);
x_18 = lean_box(0);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_nat_pow(x_5, x_15);
lean_dec(x_15);
lean_dec(x_5);
x_20 = l_Lean_mkRawNatLit(x_19);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatPow___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatPow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatPow(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatEq(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_mk_string_unchecked("Eq", 2, 2);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = l_Lean_levelOne;
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_4, x_7);
x_9 = lean_mk_string_unchecked("Nat", 3, 3);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Expr_const___override(x_10, x_6);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_array_push(x_13, x_11);
x_15 = lean_array_push(x_14, x_1);
x_16 = lean_array_push(x_15, x_2);
x_17 = l_Lean_mkAppN(x_8, x_16);
lean_dec(x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_mk_string_unchecked("LT", 2, 2);
x_4 = lean_mk_string_unchecked("lt", 2, 2);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Expr_const___override(x_5, x_8);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Expr_const___override(x_11, x_7);
x_13 = l_Lean_Name_mkStr2(x_10, x_4);
x_14 = l_Lean_Expr_const___override(x_13, x_7);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_14);
x_19 = lean_array_push(x_18, x_1);
x_20 = lean_array_push(x_19, x_2);
x_21 = l_Lean_mkAppN(x_9, x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_mkNatLe(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_3 = lean_mk_string_unchecked("LE", 2, 2);
x_4 = lean_mk_string_unchecked("le", 2, 2);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr2(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = l_Lean_Expr_const___override(x_5, x_8);
x_10 = lean_mk_string_unchecked("Nat", 3, 3);
lean_inc(x_10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = l_Lean_Expr_const___override(x_11, x_7);
x_13 = l_Lean_Name_mkStr2(x_10, x_4);
x_14 = l_Lean_Expr_const___override(x_13, x_7);
x_15 = lean_unsigned_to_nat(4u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_array_push(x_16, x_12);
x_18 = lean_array_push(x_17, x_14);
x_19 = lean_array_push(x_18, x_1);
x_20 = lean_array_push(x_19, x_2);
x_21 = l_Lean_mkAppN(x_9, x_20);
lean_dec(x_20);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr(uint8_t x_1, lean_object* x_2, uint8_t x_3) {
_start:
{
if (x_1 == 0)
{
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_mk_string_unchecked("Bool", 4, 4);
x_5 = lean_mk_string_unchecked("false", 5, 5);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_mk_string_unchecked("Bool", 4, 4);
x_10 = lean_mk_string_unchecked("true", 4, 4);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = lean_box(0);
x_13 = l_Lean_Expr_const___override(x_11, x_12);
return x_13;
}
}
else
{
if (x_3 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_inc(x_2);
x_14 = l_Lean_Compiler_mkLcProof(x_2);
x_15 = l_Lean_mkDecIsFalse(x_2, x_14);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_2);
x_16 = l_Lean_Compiler_mkLcProof(x_2);
x_17 = l_Lean_mkDecIsTrue(x_2, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_toDecidableExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Lean_Compiler_toDecidableExpr(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = lean_get_num_lit(x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_5);
x_9 = lean_get_num_lit(x_5);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_10 = lean_box(0);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_apply_2(x_1, x_4, x_5);
x_14 = lean_apply_2(x_2, x_8, x_12);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
x_16 = l_Lean_Compiler_toDecidableExpr(x_3, x_13, x_15);
lean_ctor_set(x_9, 0, x_16);
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_9, 0);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_apply_2(x_1, x_4, x_5);
x_19 = lean_apply_2(x_2, x_8, x_17);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
x_21 = l_Lean_Compiler_toDecidableExpr(x_3, x_18, x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
return x_22;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinPred___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Compiler_foldNatBinPred(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_foldNatDecEq___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecEq___lam__0___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatEq), 2, 0);
x_6 = l_Lean_Compiler_foldNatBinPred(x_5, x_4, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatDecEq___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecEq(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_foldNatDecLt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLt___lam__0___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatLt), 2, 0);
x_6 = l_Lean_Compiler_foldNatBinPred(x_5, x_4, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatDecLt___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecLt(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_foldNatDecLe___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_nat_dec_le(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLe___lam__0___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_mkNatLe), 2, 0);
x_6 = l_Lean_Compiler_foldNatBinPred(x_5, x_4, x_1, x_2, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_foldNatDecLe___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatDecLe___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatDecLe(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBinBoolPred(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_get_num_lit(x_3);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_1);
x_8 = lean_box(0);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_apply_2(x_1, x_6, x_10);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_mk_string_unchecked("Bool", 4, 4);
x_14 = lean_mk_string_unchecked("false", 5, 5);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = lean_box(0);
x_17 = l_Lean_Expr_const___override(x_15, x_16);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_mk_string_unchecked("Bool", 4, 4);
x_19 = lean_mk_string_unchecked("true", 4, 4);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Expr_const___override(x_20, x_21);
lean_ctor_set(x_7, 0, x_22);
return x_7;
}
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_apply_2(x_1, x_6, x_23);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_mk_string_unchecked("Bool", 4, 4);
x_27 = lean_mk_string_unchecked("false", 5, 5);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_28, x_29);
x_31 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_mk_string_unchecked("Bool", 4, 4);
x_33 = lean_mk_string_unchecked("true", 4, 4);
x_34 = l_Lean_Name_mkStr2(x_32, x_33);
x_35 = lean_box(0);
x_36 = l_Lean_Expr_const___override(x_34, x_35);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecEq___lam__0___boxed), 2, 0);
x_4 = l_Lean_Compiler_foldNatBinBoolPred(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatBeq___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatBeq(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLt___lam__0___boxed), 2, 0);
x_4 = l_Lean_Compiler_foldNatBinBoolPred(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatBlt___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBlt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatBlt(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLe___lam__0___boxed), 2, 0);
x_4 = l_Lean_Compiler_foldNatBinBoolPred(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldNatBle___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatBle___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldNatBle(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_natFoldFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
x_2 = lean_mk_string_unchecked("add", 3, 3);
lean_inc(x_1);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatAdd___boxed), 3, 0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_mk_string_unchecked("mul", 3, 3);
lean_inc(x_1);
x_7 = l_Lean_Name_mkStr2(x_1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMul___boxed), 3, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked("div", 3, 3);
lean_inc(x_1);
x_11 = l_Lean_Name_mkStr2(x_1, x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDiv___boxed), 3, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("mod", 3, 3);
lean_inc(x_1);
x_15 = l_Lean_Name_mkStr2(x_1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatMod___boxed), 3, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("pow", 3, 3);
lean_inc(x_1);
x_19 = l_Lean_Name_mkStr2(x_1, x_18);
x_20 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatPow___boxed), 3, 0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("decEq", 5, 5);
lean_inc(x_1);
x_23 = l_Lean_Name_mkStr2(x_1, x_22);
x_24 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecEq___boxed), 3, 0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("decLt", 5, 5);
lean_inc(x_1);
x_27 = l_Lean_Name_mkStr2(x_1, x_26);
x_28 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLt___boxed), 3, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("decLe", 5, 5);
lean_inc(x_1);
x_31 = l_Lean_Name_mkStr2(x_1, x_30);
x_32 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatDecLe___boxed), 3, 0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("beq", 3, 3);
lean_inc(x_1);
x_35 = l_Lean_Name_mkStr2(x_1, x_34);
x_36 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBeq___boxed), 3, 0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("blt", 3, 3);
lean_inc(x_1);
x_39 = l_Lean_Name_mkStr2(x_1, x_38);
x_40 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBlt___boxed), 3, 0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_mk_string_unchecked("ble", 3, 3);
x_43 = l_Lean_Name_mkStr2(x_1, x_42);
x_44 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatBle___boxed), 3, 0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_41);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_37);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_33);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_29);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_25);
lean_ctor_set(x_52, 1, x_51);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_17);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_13);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_9);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_5);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_box(0);
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 0);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_mk_string_unchecked("Bool", 4, 4);
x_9 = lean_string_dec_eq(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
return x_3;
}
else
{
return x_3;
}
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_mk_string_unchecked("true", 4, 4);
x_11 = lean_string_dec_eq(x_5, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_mk_string_unchecked("false", 5, 5);
x_13 = lean_string_dec_eq(x_5, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
return x_3;
}
else
{
return x_3;
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(x_11);
x_15 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
else
{
return x_3;
}
}
}
else
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(x_11);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
return x_3;
}
}
}
}
else
{
return x_3;
}
}
else
{
return x_3;
}
}
else
{
lean_object* x_18; 
x_18 = lean_box(0);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_getBoolLit___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_getBoolLit(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getBoolLit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_getBoolLit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_1);
return x_12;
}
}
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_1);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_2);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldStrictAnd___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictAnd___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldStrictAnd(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_getBoolLit(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_getBoolLit(x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(0);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_dec(x_2);
lean_ctor_set(x_4, 0, x_1);
return x_4;
}
else
{
lean_dec(x_1);
lean_ctor_set(x_4, 0, x_2);
return x_4;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_4, 0);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_1);
return x_11;
}
else
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
}
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_3);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_dec(x_1);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_dec(x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_3, 0);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_2);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldStrictOr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldStrictOr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Lean_Compiler_foldStrictOr(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_Compiler_boolFoldFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("strictOr", 8, 8);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictOr___boxed), 3, 0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_mk_string_unchecked("strictAnd", 9, 9);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_foldStrictAnd___boxed), 3, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Compiler_binFoldFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = l_Lean_Compiler_boolFoldFns;
x_2 = l_Lean_Compiler_uintBinFoldFns;
x_3 = l_List_appendTR(lean_box(0), x_1, x_2);
x_4 = l_Lean_Compiler_natFoldFns;
x_5 = l_List_appendTR(lean_box(0), x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_get_num_lit(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_5, x_6);
lean_dec(x_5);
x_8 = l_Lean_mkRawNatLit(x_7);
lean_ctor_set(x_2, 0, x_8);
return x_2;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_12 = l_Lean_mkRawNatLit(x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_foldNatSucc___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldNatSucc___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_foldNatSucc(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat(uint8_t x_1, lean_object* x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_7; 
x_7 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_box(0);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_14 = lean_uint32_of_nat(x_9);
x_15 = lean_unsigned_to_nat(55296u);
x_16 = lean_uint32_of_nat(x_15);
x_17 = lean_uint32_dec_lt(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(57343u);
x_19 = lean_uint32_of_nat(x_18);
x_20 = lean_uint32_dec_lt(x_19, x_14);
if (x_20 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
goto block_6;
}
else
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(1114112u);
x_22 = lean_uint32_of_nat(x_21);
x_23 = lean_uint32_dec_lt(x_14, x_22);
if (x_23 == 0)
{
lean_dec(x_10);
lean_dec(x_9);
goto block_6;
}
else
{
goto block_13;
}
}
}
else
{
goto block_13;
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_mkUInt32Lit(x_9);
lean_dec(x_9);
if (lean_is_scalar(x_10)) {
 x_12 = lean_alloc_ctor(1, 1, 0);
} else {
 x_12 = x_10;
}
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
else
{
lean_object* x_24; 
lean_dec(x_2);
x_24 = lean_box(0);
return x_24;
}
block_6:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_Lean_Compiler_mkUInt32Lit(x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldCharOfNat___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_foldCharOfNat(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_get_num_lit(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; 
x_4 = lean_box(0);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_nat_mod(x_6, x_1);
lean_dec(x_6);
x_8 = l_Lean_mkRawNatLit(x_7);
lean_ctor_set(x_3, 0, x_8);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_nat_mod(x_9, x_1);
lean_dec(x_9);
x_11 = l_Lean_mkRawNatLit(x_10);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_foldToNat___redArg(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_foldToNat___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldToNat___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Compiler_foldToNat(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Lean_Compiler_uintFoldToNatFns_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 4);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_foldToNat___boxed), 3, 1);
lean_closure_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 0, x_9);
x_1 = x_2;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_2);
x_13 = lean_ctor_get(x_11, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 4);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_foldToNat___boxed), 3, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_1);
x_1 = x_17;
x_2 = x_12;
goto _start;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_uintFoldToNatFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Compiler_numScalarTypes;
x_3 = l_List_foldl___at___Lean_Compiler_uintFoldToNatFns_spec__0(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_unFoldFns() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("Nat", 3, 3);
x_2 = lean_mk_string_unchecked("succ", 4, 4);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_foldNatSucc___boxed), 2, 0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_mk_string_unchecked("Char", 4, 4);
x_7 = lean_mk_string_unchecked("ofNat", 5, 5);
x_8 = l_Lean_Name_mkStr2(x_6, x_7);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_foldCharOfNat___boxed), 2, 0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = l_Lean_Compiler_uintFoldToNatFns;
x_15 = l_List_appendTR(lean_box(0), x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_name_eq(x_1, x_6);
if (x_8 == 0)
{
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_10; 
lean_inc(x_7);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_binFoldFns;
x_3 = l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findBinFoldFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_findBinFoldFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Compiler_unFoldFns;
x_3 = l_List_lookup___at___Lean_Compiler_findBinFoldFn_spec__0___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_findUnFoldFn___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_findUnFoldFn(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* lean_fold_bin_op(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Compiler_findBinFoldFn(x_5);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(x_1);
x_10 = lean_apply_3(x_8, x_9, x_3, x_4);
return x_10;
}
}
else
{
lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldBinOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_fold_bin_op(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* lean_fold_un_op(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_Compiler_findUnFoldFn(x_4);
lean_dec(x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(x_1);
x_9 = lean_apply_2(x_7, x_8, x_3);
return x_9;
}
}
else
{
lean_object* x_10; 
lean_dec(x_3);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_foldUnOp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = lean_fold_un_op(x_4, x_2, x_3);
return x_5;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_ConstFolding(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_numScalarTypes = _init_l_Lean_Compiler_numScalarTypes();
lean_mark_persistent(l_Lean_Compiler_numScalarTypes);
l_Lean_Compiler_preUIntBinFoldFns = _init_l_Lean_Compiler_preUIntBinFoldFns();
lean_mark_persistent(l_Lean_Compiler_preUIntBinFoldFns);
l_Lean_Compiler_uintBinFoldFns = _init_l_Lean_Compiler_uintBinFoldFns();
lean_mark_persistent(l_Lean_Compiler_uintBinFoldFns);
l_Lean_Compiler_natPowThreshold = _init_l_Lean_Compiler_natPowThreshold();
lean_mark_persistent(l_Lean_Compiler_natPowThreshold);
l_Lean_Compiler_natFoldFns = _init_l_Lean_Compiler_natFoldFns();
lean_mark_persistent(l_Lean_Compiler_natFoldFns);
l_Lean_Compiler_boolFoldFns = _init_l_Lean_Compiler_boolFoldFns();
lean_mark_persistent(l_Lean_Compiler_boolFoldFns);
l_Lean_Compiler_binFoldFns = _init_l_Lean_Compiler_binFoldFns();
lean_mark_persistent(l_Lean_Compiler_binFoldFns);
l_Lean_Compiler_uintFoldToNatFns = _init_l_Lean_Compiler_uintFoldToNatFns();
lean_mark_persistent(l_Lean_Compiler_uintFoldToNatFns);
l_Lean_Compiler_unFoldFns = _init_l_Lean_Compiler_unFoldFns();
lean_mark_persistent(l_Lean_Compiler_unFoldFns);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
