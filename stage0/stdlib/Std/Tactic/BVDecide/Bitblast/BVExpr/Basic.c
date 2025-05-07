// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Basic
// Imports: Init.Data.Hashable Init.Data.BitVec Init.Data.RArray Std.Tactic.BVDecide.Bitblast.BoolExpr.Basic
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object*, lean_object*);
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(uint8_t);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object*);
lean_object* l_BitVec_setWidth(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_replicate(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_extractLsb_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_BitVec_or(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_udiv(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object*);
lean_object* l_BitVec_append(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVUnOp;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_instToString;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RArray_getImpl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBinOp;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_shiftLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit___redArg____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object*);
uint64_t l_BitVec_hash(lean_object*, lean_object*);
uint8_t l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_not(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEq___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object*, lean_object*);
lean_object* l_BitVec_toNat(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object*);
lean_object* l_BitVec_sshiftRight_x27(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85____boxed(lean_object*, lean_object*);
lean_object* l_BitVec_ushiftRight(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_add(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(lean_object*, lean_object*);
lean_object* l_BitVec_sshiftRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object*, lean_object*);
lean_object* l_BitVec_umod(lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_rotateRight(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object*);
uint8_t l_Nat_testBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_BitVec_and(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instInhabitedBVBit;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(lean_object*, lean_object*);
lean_object* l_BitVec_rotateLeft(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instReprBVBit;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_instToString;
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_instToString;
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEq___redArg___boxed(lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEq(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35____boxed(lean_object*);
lean_object* l_BitVec_mul(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_BitVec_xor(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_BitVec_toHex(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEq___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instHashableBVBit;
uint8_t l_BitVec_ult(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit;
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_instToString;
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; uint64_t x_12; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_2);
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_uint64_of_nat(x_3);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_of_nat(x_4);
x_12 = lean_uint64_mix_hash(x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVBit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_35____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_eq(x_3, x_6);
if (x_9 == 0)
{
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_4, x_7);
if (x_10 == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_eq(x_5, x_8);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_85_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVBit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit___redArg____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("var", 3, 3);
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
x_10 = lean_unsigned_to_nat(7u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_11);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_11);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_mk_string_unchecked(",", 1, 1);
x_21 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
x_22 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_22, 0, x_19);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_box(1);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("w", 1, 1);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(5u);
x_30 = lean_nat_to_int(x_29);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_unbox(x_16);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_35);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_21);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_23);
x_40 = lean_mk_string_unchecked("idx", 3, 3);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
x_46 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_46, 0, x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unbox(x_16);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_mk_string_unchecked(" }", 2, 2);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_to_int(x_52);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_2);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_50);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_51);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_58, 0, x_53);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_unbox(x_16);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
return x_59;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit___redArg____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instReprBVBit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_reprBVBit____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_287____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instToStringBVBit___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("x", 1, 1);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec(x_4);
x_6 = lean_mk_string_unchecked("[", 1, 1);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("]", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instToStringBVBit() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_instToStringBVBit___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instInhabitedBVBit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_mod(x_1, x_2);
x_4 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Std_Tactic_BVDecide_BVBinOp_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_uint64_of_nat(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; uint64_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_uint64_of_nat(x_6);
return x_7;
}
case 3:
{
lean_object* x_8; uint64_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_uint64_of_nat(x_8);
return x_9;
}
case 4:
{
lean_object* x_10; uint64_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_uint64_of_nat(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; uint64_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_uint64_of_nat(x_12);
return x_13;
}
default: 
{
lean_object* x_14; uint64_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_uint64_of_nat(x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVBinOp() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinOp_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(3u);
x_3 = lean_nat_dec_le(x_2, x_1);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_1, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(2);
x_10 = lean_unbox(x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
return x_12;
}
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(5u);
x_14 = lean_nat_dec_le(x_13, x_1);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = lean_nat_dec_eq(x_1, x_2);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(4);
x_17 = lean_unbox(x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(3);
x_19 = lean_unbox(x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_eq(x_1, x_13);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(6);
x_22 = lean_unbox(x_21);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(5);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_BVBinOp_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(x_1);
x_4 = l_Std_Tactic_BVDecide_BVBinOp_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVBinOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("&&", 2, 2);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("||", 2, 2);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_mk_string_unchecked("^", 1, 1);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_mk_string_unchecked("+", 1, 1);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_mk_string_unchecked("*", 1, 1);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_mk_string_unchecked("/ᵤ", 4, 2);
return x_7;
}
default: 
{
lean_object* x_8; 
x_8 = lean_mk_string_unchecked("%ᵤ", 4, 2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinOp_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinOp_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinOp_toString___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (x_2) {
case 0:
{
lean_object* x_5; 
x_5 = l_BitVec_and(x_1, x_3, x_4);
return x_5;
}
case 1:
{
lean_object* x_6; 
x_6 = l_BitVec_or(x_1, x_3, x_4);
return x_6;
}
case 2:
{
lean_object* x_7; 
x_7 = l_BitVec_xor(x_1, x_3, x_4);
return x_7;
}
case 3:
{
lean_object* x_8; 
x_8 = l_BitVec_add(x_1, x_3, x_4);
return x_8;
}
case 4:
{
lean_object* x_9; 
x_9 = l_BitVec_mul(x_1, x_3, x_4);
return x_9;
}
case 5:
{
lean_object* x_10; 
x_10 = l_BitVec_udiv(x_1, x_3, x_4);
return x_10;
}
default: 
{
lean_object* x_11; 
x_11 = l_BitVec_umod(x_1, x_3, x_4);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinOp_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinOp_eval(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT uint64_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_4);
x_8 = lean_uint64_mix_hash(x_6, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_of_nat(x_9);
x_13 = lean_uint64_mix_hash(x_11, x_12);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_of_nat(x_14);
x_18 = lean_uint64_mix_hash(x_16, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_instHashableBVUnOp() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_box(1);
x_4 = lean_box(0);
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
x_5 = lean_unbox(x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = lean_unbox(x_4);
return x_6;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_unbox(x_4);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_3);
return x_11;
}
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_4);
return x_12;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
uint8_t x_16; 
x_16 = lean_unbox(x_4);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_unbox(x_3);
return x_17;
}
}
else
{
uint8_t x_18; 
x_18 = lean_unbox(x_4);
return x_18;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_nat_dec_eq(x_19, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_unbox(x_4);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_unbox(x_3);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = lean_unbox(x_4);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_instDecidableEqBVUnOp___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_instDecidableEqBVUnOp(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("~", 1, 1);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_mk_string_unchecked("rotL ", 5, 5);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("rotR ", 5, 5);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
default: 
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked(">>a ", 4, 4);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVUnOp_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVUnOp_toString), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; 
x_4 = l_BitVec_not(x_1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = l_BitVec_rotateLeft(x_1, x_3, x_5);
return x_6;
}
case 2:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_BitVec_rotateRight(x_1, x_3, x_7);
return x_8;
}
default: 
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 0);
x_10 = l_BitVec_sshiftRight(x_1, x_3, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVUnOp_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVUnOp_eval(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_apply_2(x_2, x_12, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_apply_2(x_3, x_15, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_4(x_4, x_18, x_19, x_20, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_26 = lean_ctor_get(x_1, 2);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_box(x_25);
x_28 = lean_apply_4(x_5, x_23, x_24, x_27, x_26);
return x_28;
}
case 4:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = lean_ctor_get(x_1, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 2);
lean_inc(x_31);
lean_dec(x_1);
x_32 = lean_apply_3(x_6, x_29, x_30, x_31);
return x_32;
}
case 5:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 4);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_apply_6(x_7, x_33, x_34, x_35, x_36, x_37, lean_box(0));
return x_38;
}
case 6:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 3);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_apply_5(x_8, x_39, x_40, x_41, x_42, lean_box(0));
return x_43;
}
case 7:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 3);
lean_inc(x_47);
lean_dec(x_1);
x_48 = lean_apply_4(x_9, x_44, x_45, x_46, x_47);
return x_48;
}
case 8:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_ctor_get(x_1, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 2);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 3);
lean_inc(x_52);
lean_dec(x_1);
x_53 = lean_apply_4(x_10, x_49, x_50, x_51, x_52);
return x_53;
}
default: 
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 3);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_apply_4(x_11, x_54, x_55, x_56, x_57);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_ctor_get(x_3, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_apply_2(x_4, x_14, x_15);
return x_16;
}
case 1:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_ctor_get(x_3, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 1);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_apply_2(x_5, x_17, x_18);
return x_19;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 3);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_apply_4(x_6, x_20, x_21, x_22, x_23);
return x_24;
}
case 3:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 1);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_28 = lean_ctor_get(x_3, 2);
lean_inc(x_28);
lean_dec(x_3);
x_29 = lean_box(x_27);
x_30 = lean_apply_4(x_7, x_25, x_26, x_29, x_28);
return x_30;
}
case 4:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_ctor_get(x_3, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_3, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_3, 2);
lean_inc(x_33);
lean_dec(x_3);
x_34 = lean_apply_3(x_8, x_31, x_32, x_33);
return x_34;
}
case 5:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = lean_ctor_get(x_3, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_3, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_3, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_3, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_3, 4);
lean_inc(x_39);
lean_dec(x_3);
x_40 = lean_apply_6(x_9, x_35, x_36, x_37, x_38, x_39, lean_box(0));
return x_40;
}
case 6:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_3, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_3, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_3, 3);
lean_inc(x_44);
lean_dec(x_3);
x_45 = lean_apply_5(x_10, x_41, x_42, x_43, x_44, lean_box(0));
return x_45;
}
case 7:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_ctor_get(x_3, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_3, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_3, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_3, 3);
lean_inc(x_49);
lean_dec(x_3);
x_50 = lean_apply_4(x_11, x_46, x_47, x_48, x_49);
return x_50;
}
case 8:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_51 = lean_ctor_get(x_3, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_3, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_3, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_3, 3);
lean_inc(x_54);
lean_dec(x_3);
x_55 = lean_apply_4(x_12, x_51, x_52, x_53, x_54);
return x_55;
}
default: 
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_56 = lean_ctor_get(x_3, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_3, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_3, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_3, 3);
lean_inc(x_59);
lean_dec(x_3);
x_60 = lean_apply_4(x_13, x_56, x_57, x_58, x_59);
return x_60;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_casesOn___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Tactic_BVDecide_BVExpr_casesOn___override(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_var___override(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_uint64_of_nat(x_3);
x_5 = lean_uint64_of_nat(x_1);
x_6 = lean_uint64_of_nat(x_2);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
x_9 = lean_alloc_ctor(0, 2, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_const___override(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(7u);
x_4 = lean_uint64_of_nat(x_3);
x_5 = lean_uint64_of_nat(x_1);
x_6 = l_BitVec_hash(x_1, x_2);
x_7 = lean_uint64_mix_hash(x_5, x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
x_9 = lean_alloc_ctor(1, 2, 8);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_2);
lean_ctor_set_uint64(x_9, sizeof(void*)*2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_extract___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_5 = lean_unsigned_to_nat(11u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_2);
x_8 = lean_uint64_of_nat(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_9 = x_15;
goto block_14;
}
case 1:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_9 = x_16;
goto block_14;
}
case 3:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_9 = x_17;
goto block_14;
}
case 4:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_9 = x_18;
goto block_14;
}
case 5:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_9 = x_19;
goto block_14;
}
default: 
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_9 = x_20;
goto block_14;
}
}
block_14:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_mix_hash(x_6, x_11);
x_13 = lean_alloc_ctor(2, 4, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint64(x_13, sizeof(void*)*4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_17; 
x_5 = lean_unsigned_to_nat(13u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_17 = x_26;
goto block_25;
}
case 1:
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_17 = x_27;
goto block_25;
}
case 3:
{
uint64_t x_28; 
x_28 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_17 = x_28;
goto block_25;
}
case 4:
{
uint64_t x_29; 
x_29 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_17 = x_29;
goto block_25;
}
case 5:
{
uint64_t x_30; 
x_30 = lean_ctor_get_uint64(x_2, sizeof(void*)*5);
x_17 = x_30;
goto block_25;
}
default: 
{
uint64_t x_31; 
x_31 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
x_17 = x_31;
goto block_25;
}
}
block_16:
{
uint64_t x_11; uint64_t x_12; uint64_t x_13; uint64_t x_14; lean_object* x_15; 
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_uint64_mix_hash(x_8, x_11);
x_13 = lean_uint64_mix_hash(x_7, x_12);
x_14 = lean_uint64_mix_hash(x_6, x_13);
x_15 = lean_alloc_ctor(3, 3, 9);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_4);
lean_ctor_set_uint64(x_15, sizeof(void*)*3, x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*3 + 8, x_3);
return x_15;
}
block_25:
{
uint64_t x_18; 
x_18 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVBinOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_417_(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_17;
x_9 = x_18;
x_10 = x_19;
goto block_16;
}
case 1:
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_17;
x_9 = x_18;
x_10 = x_20;
goto block_16;
}
case 3:
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_17;
x_9 = x_18;
x_10 = x_21;
goto block_16;
}
case 4:
{
uint64_t x_22; 
x_22 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_17;
x_9 = x_18;
x_10 = x_22;
goto block_16;
}
case 5:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_8 = x_17;
x_9 = x_18;
x_10 = x_23;
goto block_16;
}
default: 
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_8 = x_17;
x_9 = x_18;
x_10 = x_24;
goto block_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_un___override(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; 
x_4 = lean_unsigned_to_nat(17u);
x_5 = lean_uint64_of_nat(x_4);
x_6 = lean_uint64_of_nat(x_1);
x_7 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_hashBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1093_(x_2);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_14; 
x_14 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_8 = x_14;
goto block_13;
}
case 1:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_8 = x_15;
goto block_13;
}
case 3:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_8 = x_16;
goto block_13;
}
case 4:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_8 = x_17;
goto block_13;
}
case 5:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_8 = x_18;
goto block_13;
}
default: 
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_8 = x_19;
goto block_13;
}
}
block_13:
{
uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; 
x_9 = lean_uint64_mix_hash(x_7, x_8);
x_10 = lean_uint64_mix_hash(x_6, x_9);
x_11 = lean_uint64_mix_hash(x_5, x_10);
x_12 = lean_alloc_ctor(4, 3, 8);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_2);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set_uint64(x_12, sizeof(void*)*3, x_11);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_16; 
x_6 = lean_unsigned_to_nat(19u);
x_7 = lean_uint64_of_nat(x_6);
x_8 = lean_uint64_of_nat(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_16 = x_24;
goto block_23;
}
case 1:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_16 = x_25;
goto block_23;
}
case 3:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_16 = x_26;
goto block_23;
}
case 4:
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_16 = x_27;
goto block_23;
}
case 5:
{
uint64_t x_28; 
x_28 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_16 = x_28;
goto block_23;
}
default: 
{
uint64_t x_29; 
x_29 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_16 = x_29;
goto block_23;
}
}
block_15:
{
uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; 
x_11 = lean_uint64_mix_hash(x_9, x_10);
x_12 = lean_uint64_mix_hash(x_8, x_11);
x_13 = lean_uint64_mix_hash(x_7, x_12);
x_14 = lean_alloc_ctor(5, 5, 8);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_2);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_4);
lean_ctor_set(x_14, 4, x_5);
lean_ctor_set_uint64(x_14, sizeof(void*)*5, x_13);
return x_14;
}
block_23:
{
switch (lean_obj_tag(x_5)) {
case 0:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
x_9 = x_16;
x_10 = x_17;
goto block_15;
}
case 1:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_5, sizeof(void*)*2);
x_9 = x_16;
x_10 = x_18;
goto block_15;
}
case 3:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_9 = x_16;
x_10 = x_19;
goto block_15;
}
case 4:
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_5, sizeof(void*)*3);
x_9 = x_16;
x_10 = x_20;
goto block_15;
}
case 5:
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_5, sizeof(void*)*5);
x_9 = x_16;
x_10 = x_21;
goto block_15;
}
default: 
{
uint64_t x_22; 
x_22 = lean_ctor_get_uint64(x_5, sizeof(void*)*4);
x_9 = x_16;
x_10 = x_22;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_append___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Tactic_BVDecide_BVExpr_append___override___redArg(x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_5 = lean_unsigned_to_nat(23u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_2);
x_8 = lean_uint64_of_nat(x_3);
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_15; 
x_15 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_9 = x_15;
goto block_14;
}
case 1:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_9 = x_16;
goto block_14;
}
case 3:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_9 = x_17;
goto block_14;
}
case 4:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_9 = x_18;
goto block_14;
}
case 5:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_9 = x_19;
goto block_14;
}
default: 
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_9 = x_20;
goto block_14;
}
}
block_14:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_mix_hash(x_6, x_11);
x_13 = lean_alloc_ctor(6, 4, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint64(x_13, sizeof(void*)*4, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_replicate___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Std_Tactic_BVDecide_BVExpr_replicate___override___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftLeft___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_15; 
x_5 = lean_unsigned_to_nat(29u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_15 = x_23;
goto block_22;
}
case 1:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_15 = x_24;
goto block_22;
}
case 3:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_15 = x_25;
goto block_22;
}
case 4:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_15 = x_26;
goto block_22;
}
case 5:
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_15 = x_27;
goto block_22;
}
default: 
{
uint64_t x_28; 
x_28 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_15 = x_28;
goto block_22;
}
}
block_14:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_mix_hash(x_6, x_11);
x_13 = lean_alloc_ctor(7, 4, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint64(x_13, sizeof(void*)*4, x_12);
return x_13;
}
block_22:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_16;
goto block_14;
}
case 1:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_17;
goto block_14;
}
case 3:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_18;
goto block_14;
}
case 4:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_19;
goto block_14;
}
case 5:
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_8 = x_15;
x_9 = x_20;
goto block_14;
}
default: 
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_8 = x_15;
x_9 = x_21;
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_shiftRight___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_15; 
x_5 = lean_unsigned_to_nat(31u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_15 = x_23;
goto block_22;
}
case 1:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_15 = x_24;
goto block_22;
}
case 3:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_15 = x_25;
goto block_22;
}
case 4:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_15 = x_26;
goto block_22;
}
case 5:
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_15 = x_27;
goto block_22;
}
default: 
{
uint64_t x_28; 
x_28 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_15 = x_28;
goto block_22;
}
}
block_14:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_mix_hash(x_6, x_11);
x_13 = lean_alloc_ctor(8, 4, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint64(x_13, sizeof(void*)*4, x_12);
return x_13;
}
block_22:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_16;
goto block_14;
}
case 1:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_17;
goto block_14;
}
case 3:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_18;
goto block_14;
}
case 4:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_19;
goto block_14;
}
case 5:
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_8 = x_15;
x_9 = x_20;
goto block_14;
}
default: 
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_8 = x_15;
x_9 = x_21;
goto block_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_arithShiftRight___override(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_15; 
x_5 = lean_unsigned_to_nat(37u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_of_nat(x_1);
switch (lean_obj_tag(x_3)) {
case 0:
{
uint64_t x_23; 
x_23 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_15 = x_23;
goto block_22;
}
case 1:
{
uint64_t x_24; 
x_24 = lean_ctor_get_uint64(x_3, sizeof(void*)*2);
x_15 = x_24;
goto block_22;
}
case 3:
{
uint64_t x_25; 
x_25 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_15 = x_25;
goto block_22;
}
case 4:
{
uint64_t x_26; 
x_26 = lean_ctor_get_uint64(x_3, sizeof(void*)*3);
x_15 = x_26;
goto block_22;
}
case 5:
{
uint64_t x_27; 
x_27 = lean_ctor_get_uint64(x_3, sizeof(void*)*5);
x_15 = x_27;
goto block_22;
}
default: 
{
uint64_t x_28; 
x_28 = lean_ctor_get_uint64(x_3, sizeof(void*)*4);
x_15 = x_28;
goto block_22;
}
}
block_14:
{
uint64_t x_10; uint64_t x_11; uint64_t x_12; lean_object* x_13; 
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_uint64_mix_hash(x_7, x_10);
x_12 = lean_uint64_mix_hash(x_6, x_11);
x_13 = lean_alloc_ctor(9, 4, 8);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set(x_13, 2, x_3);
lean_ctor_set(x_13, 3, x_4);
lean_ctor_set_uint64(x_13, sizeof(void*)*4, x_12);
return x_13;
}
block_22:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
uint64_t x_16; 
x_16 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_16;
goto block_14;
}
case 1:
{
uint64_t x_17; 
x_17 = lean_ctor_get_uint64(x_4, sizeof(void*)*2);
x_8 = x_15;
x_9 = x_17;
goto block_14;
}
case 3:
{
uint64_t x_18; 
x_18 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_18;
goto block_14;
}
case 4:
{
uint64_t x_19; 
x_19 = lean_ctor_get_uint64(x_4, sizeof(void*)*3);
x_8 = x_15;
x_9 = x_19;
goto block_14;
}
case 5:
{
uint64_t x_20; 
x_20 = lean_ctor_get_uint64(x_4, sizeof(void*)*5);
x_8 = x_15;
x_9 = x_20;
goto block_14;
}
default: 
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_4, sizeof(void*)*4);
x_8 = x_15;
x_9 = x_21;
goto block_14;
}
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_3;
}
case 3:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_4;
}
case 4:
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_5;
}
case 5:
{
uint64_t x_6; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*5);
return x_6;
}
default: 
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
return x_7;
}
}
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_hashCode___override(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
return x_3;
}
case 1:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
return x_4;
}
case 3:
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
return x_5;
}
case 4:
{
uint64_t x_6; 
x_6 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
return x_6;
}
case 5:
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_2, sizeof(void*)*5);
return x_7;
}
default: 
{
uint64_t x_8; 
x_8 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_bin___override___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_Tactic_BVDecide_BVExpr_bin___override(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_hashCode___override___redArg(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_hashCode___override___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_hashCode___override(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_2; 
x_2 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_2;
}
case 1:
{
uint64_t x_3; 
x_3 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
return x_3;
}
case 3:
{
uint64_t x_4; 
x_4 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_4;
}
case 4:
{
uint64_t x_5; 
x_5 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
return x_5;
}
case 5:
{
uint64_t x_6; 
x_6 = lean_ctor_get_uint64(x_1, sizeof(void*)*5);
return x_6;
}
default: 
{
uint64_t x_7; 
x_7 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_instHashable___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instHashable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_BVExpr_instHashable(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; size_t x_4; uint8_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_89; 
x_3 = lean_ptr_addr(x_1);
x_4 = lean_ptr_addr(x_2);
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
uint64_t x_97; 
x_97 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_89 = x_97;
goto block_96;
}
case 1:
{
uint64_t x_98; 
x_98 = lean_ctor_get_uint64(x_1, sizeof(void*)*2);
x_89 = x_98;
goto block_96;
}
case 3:
{
uint64_t x_99; 
x_99 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_89 = x_99;
goto block_96;
}
case 4:
{
uint64_t x_100; 
x_100 = lean_ctor_get_uint64(x_1, sizeof(void*)*3);
x_89 = x_100;
goto block_96;
}
case 5:
{
uint64_t x_101; 
x_101 = lean_ctor_get_uint64(x_1, sizeof(void*)*5);
x_89 = x_101;
goto block_96;
}
default: 
{
uint64_t x_102; 
x_102 = lean_ctor_get_uint64(x_1, sizeof(void*)*4);
x_89 = x_102;
goto block_96;
}
}
}
else
{
return x_5;
}
block_88:
{
uint8_t x_8; uint8_t x_9; 
x_8 = lean_uint64_dec_eq(x_6, x_7);
x_9 = l_instDecidableNot___redArg(x_8);
if (x_9 == 0)
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_1, 1);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_nat_dec_eq(x_10, x_11);
return x_12;
}
else
{
return x_9;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_nat_dec_eq(x_13, x_14);
return x_15;
}
else
{
return x_9;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_16 = lean_ctor_get(x_1, 0);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_1, 3);
x_19 = lean_ctor_get(x_2, 0);
x_20 = lean_ctor_get(x_2, 1);
x_21 = lean_ctor_get(x_2, 3);
x_22 = lean_nat_dec_eq(x_16, x_19);
if (x_22 == 0)
{
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_17, x_20);
if (x_23 == 0)
{
return x_23;
}
else
{
x_1 = x_18;
x_2 = x_21;
goto _start;
}
}
}
else
{
return x_9;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; uint8_t x_31; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
x_27 = lean_ctor_get(x_1, 2);
x_28 = lean_ctor_get(x_2, 1);
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_30 = lean_ctor_get(x_2, 2);
x_31 = l_Std_Tactic_BVDecide_instDecidableEqBVBinOp(x_26, x_29);
if (x_31 == 0)
{
return x_31;
}
else
{
uint8_t x_32; 
x_32 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_25, x_28);
if (x_32 == 0)
{
return x_32;
}
else
{
x_1 = x_27;
x_2 = x_30;
goto _start;
}
}
}
else
{
return x_9;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_1, 1);
x_35 = lean_ctor_get(x_1, 2);
x_36 = lean_ctor_get(x_2, 1);
x_37 = lean_ctor_get(x_2, 2);
x_38 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_decEqBVUnOp____x40_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic___hyg_1156_(x_34, x_36);
if (x_38 == 0)
{
return x_38;
}
else
{
x_1 = x_35;
x_2 = x_37;
goto _start;
}
}
else
{
return x_9;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_40 = lean_ctor_get(x_1, 0);
x_41 = lean_ctor_get(x_1, 1);
x_42 = lean_ctor_get(x_1, 3);
x_43 = lean_ctor_get(x_1, 4);
x_44 = lean_ctor_get(x_2, 0);
x_45 = lean_ctor_get(x_2, 1);
x_46 = lean_ctor_get(x_2, 3);
x_47 = lean_ctor_get(x_2, 4);
x_48 = lean_nat_dec_eq(x_40, x_44);
if (x_48 == 0)
{
return x_48;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_eq(x_41, x_45);
if (x_49 == 0)
{
return x_49;
}
else
{
uint8_t x_50; 
x_50 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_42, x_46);
if (x_50 == 0)
{
return x_50;
}
else
{
x_1 = x_43;
x_2 = x_47;
goto _start;
}
}
}
}
else
{
return x_9;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 2);
x_54 = lean_ctor_get(x_1, 3);
x_55 = lean_ctor_get(x_2, 0);
x_56 = lean_ctor_get(x_2, 2);
x_57 = lean_ctor_get(x_2, 3);
x_58 = lean_nat_dec_eq(x_53, x_56);
if (x_58 == 0)
{
return x_58;
}
else
{
uint8_t x_59; 
x_59 = lean_nat_dec_eq(x_52, x_55);
if (x_59 == 0)
{
return x_59;
}
else
{
x_1 = x_54;
x_2 = x_57;
goto _start;
}
}
}
else
{
return x_9;
}
}
case 7:
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_61 = lean_ctor_get(x_1, 1);
x_62 = lean_ctor_get(x_1, 2);
x_63 = lean_ctor_get(x_1, 3);
x_64 = lean_ctor_get(x_2, 1);
x_65 = lean_ctor_get(x_2, 2);
x_66 = lean_ctor_get(x_2, 3);
x_67 = lean_nat_dec_eq(x_61, x_64);
if (x_67 == 0)
{
return x_67;
}
else
{
uint8_t x_68; 
x_68 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_62, x_65);
if (x_68 == 0)
{
return x_68;
}
else
{
x_1 = x_63;
x_2 = x_66;
goto _start;
}
}
}
else
{
return x_9;
}
}
case 8:
{
if (lean_obj_tag(x_2) == 8)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_70 = lean_ctor_get(x_1, 1);
x_71 = lean_ctor_get(x_1, 2);
x_72 = lean_ctor_get(x_1, 3);
x_73 = lean_ctor_get(x_2, 1);
x_74 = lean_ctor_get(x_2, 2);
x_75 = lean_ctor_get(x_2, 3);
x_76 = lean_nat_dec_eq(x_70, x_73);
if (x_76 == 0)
{
return x_76;
}
else
{
uint8_t x_77; 
x_77 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_71, x_74);
if (x_77 == 0)
{
return x_77;
}
else
{
x_1 = x_72;
x_2 = x_75;
goto _start;
}
}
}
else
{
return x_9;
}
}
default: 
{
if (lean_obj_tag(x_2) == 9)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_79 = lean_ctor_get(x_1, 1);
x_80 = lean_ctor_get(x_1, 2);
x_81 = lean_ctor_get(x_1, 3);
x_82 = lean_ctor_get(x_2, 1);
x_83 = lean_ctor_get(x_2, 2);
x_84 = lean_ctor_get(x_2, 3);
x_85 = lean_nat_dec_eq(x_79, x_82);
if (x_85 == 0)
{
return x_85;
}
else
{
uint8_t x_86; 
x_86 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_80, x_83);
if (x_86 == 0)
{
return x_86;
}
else
{
x_1 = x_81;
x_2 = x_84;
goto _start;
}
}
}
else
{
return x_9;
}
}
}
}
else
{
return x_5;
}
}
block_96:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint64_t x_90; 
x_90 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_6 = x_89;
x_7 = x_90;
goto block_88;
}
case 1:
{
uint64_t x_91; 
x_91 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_6 = x_89;
x_7 = x_91;
goto block_88;
}
case 3:
{
uint64_t x_92; 
x_92 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_6 = x_89;
x_7 = x_92;
goto block_88;
}
case 4:
{
uint64_t x_93; 
x_93 = lean_ctor_get_uint64(x_2, sizeof(void*)*3);
x_6 = x_89;
x_7 = x_93;
goto block_88;
}
case 5:
{
uint64_t x_94; 
x_94 = lean_ctor_get_uint64(x_2, sizeof(void*)*5);
x_6 = x_89;
x_7 = x_94;
goto block_88;
}
default: 
{
uint64_t x_95; 
x_95 = lean_ctor_get_uint64(x_2, sizeof(void*)*4);
x_6 = x_89;
x_7 = x_95;
goto block_88;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_decEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_decEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_decEq(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEq___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVExpr_instDecidableEq(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_decEq___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEq___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_instDecidableEq___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instDecidableEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_instDecidableEq(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_toString(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_mk_string_unchecked("var", 3, 3);
x_5 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_mk_string_unchecked("0x", 2, 2);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_BitVec_toHex(x_1, x_7);
lean_dec(x_7);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("#", 1, 1);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_unsigned_to_nat(120u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_format_pretty(x_18, x_19, x_20, x_20);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
lean_dec(x_2);
x_25 = l_Std_Tactic_BVDecide_BVExpr_toString(x_22, x_24);
x_26 = lean_mk_string_unchecked("[", 1, 1);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
x_28 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_30 = lean_mk_string_unchecked(", ", 2, 2);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("]", 1, 1);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
return x_35;
}
case 3:
{
lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
lean_dec(x_2);
x_39 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_1);
x_40 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_36);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = lean_mk_string_unchecked(" ", 1, 1);
x_43 = lean_string_append(x_41, x_42);
x_44 = l_Std_Tactic_BVDecide_BVBinOp_toString(x_37);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = lean_string_append(x_45, x_42);
lean_dec(x_42);
x_47 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_38);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked(")", 1, 1);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
return x_50;
}
case 4:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_51 = lean_ctor_get(x_2, 1);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 2);
lean_inc(x_52);
lean_dec(x_2);
x_53 = lean_mk_string_unchecked("(", 1, 1);
x_54 = l_Std_Tactic_BVDecide_BVUnOp_toString(x_51);
x_55 = lean_string_append(x_53, x_54);
lean_dec(x_54);
x_56 = lean_mk_string_unchecked(" ", 1, 1);
x_57 = lean_string_append(x_55, x_56);
lean_dec(x_56);
x_58 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_52);
x_59 = lean_string_append(x_57, x_58);
lean_dec(x_58);
x_60 = lean_mk_string_unchecked(")", 1, 1);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
return x_61;
}
case 5:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_1);
x_62 = lean_ctor_get(x_2, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_2, 3);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 4);
lean_inc(x_65);
lean_dec(x_2);
x_66 = lean_mk_string_unchecked("(", 1, 1);
x_67 = l_Std_Tactic_BVDecide_BVExpr_toString(x_62, x_64);
x_68 = lean_string_append(x_66, x_67);
lean_dec(x_67);
x_69 = lean_mk_string_unchecked(" ++ ", 4, 4);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = l_Std_Tactic_BVDecide_BVExpr_toString(x_63, x_65);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked(")", 1, 1);
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
return x_74;
}
case 6:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_75 = lean_ctor_get(x_2, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_2, 2);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 3);
lean_inc(x_77);
lean_dec(x_2);
x_78 = lean_mk_string_unchecked("(replicate ", 11, 11);
x_79 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
x_80 = lean_string_append(x_78, x_79);
lean_dec(x_79);
x_81 = lean_mk_string_unchecked(" ", 1, 1);
x_82 = lean_string_append(x_80, x_81);
lean_dec(x_81);
x_83 = l_Std_Tactic_BVDecide_BVExpr_toString(x_75, x_77);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_85 = lean_mk_string_unchecked(")", 1, 1);
x_86 = lean_string_append(x_84, x_85);
lean_dec(x_85);
return x_86;
}
case 7:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_87 = lean_ctor_get(x_2, 1);
lean_inc(x_87);
x_88 = lean_ctor_get(x_2, 2);
lean_inc(x_88);
x_89 = lean_ctor_get(x_2, 3);
lean_inc(x_89);
lean_dec(x_2);
x_90 = lean_mk_string_unchecked("(", 1, 1);
x_91 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_88);
x_92 = lean_string_append(x_90, x_91);
lean_dec(x_91);
x_93 = lean_mk_string_unchecked(" << ", 4, 4);
x_94 = lean_string_append(x_92, x_93);
lean_dec(x_93);
x_95 = l_Std_Tactic_BVDecide_BVExpr_toString(x_87, x_89);
x_96 = lean_string_append(x_94, x_95);
lean_dec(x_95);
x_97 = lean_mk_string_unchecked(")", 1, 1);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
return x_98;
}
case 8:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_99 = lean_ctor_get(x_2, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_2, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_2, 3);
lean_inc(x_101);
lean_dec(x_2);
x_102 = lean_mk_string_unchecked("(", 1, 1);
x_103 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_100);
x_104 = lean_string_append(x_102, x_103);
lean_dec(x_103);
x_105 = lean_mk_string_unchecked(" >> ", 4, 4);
x_106 = lean_string_append(x_104, x_105);
lean_dec(x_105);
x_107 = l_Std_Tactic_BVDecide_BVExpr_toString(x_99, x_101);
x_108 = lean_string_append(x_106, x_107);
lean_dec(x_107);
x_109 = lean_mk_string_unchecked(")", 1, 1);
x_110 = lean_string_append(x_108, x_109);
lean_dec(x_109);
return x_110;
}
default: 
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_111 = lean_ctor_get(x_2, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_2, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_2, 3);
lean_inc(x_113);
lean_dec(x_2);
x_114 = lean_mk_string_unchecked("(", 1, 1);
x_115 = l_Std_Tactic_BVDecide_BVExpr_toString(x_1, x_112);
x_116 = lean_string_append(x_114, x_115);
lean_dec(x_115);
x_117 = lean_mk_string_unchecked(" >>a ", 5, 5);
x_118 = lean_string_append(x_116, x_117);
lean_dec(x_117);
x_119 = l_Std_Tactic_BVDecide_BVExpr_toString(x_111, x_113);
x_120 = lean_string_append(x_118, x_119);
lean_dec(x_119);
x_121 = lean_mk_string_unchecked(")", 1, 1);
x_122 = lean_string_append(x_120, x_121);
lean_dec(x_121);
return x_122;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_instToString(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVExpr_toString), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RArray_getImpl___redArg(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_Assignment_get___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_BVExpr_Assignment_get(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 1);
x_5 = l_Lean_RArray_getImpl___redArg(x_2, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_nat_dec_eq(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_dec(x_5);
x_9 = l_BitVec_setWidth(x_6, x_1, x_8);
lean_dec(x_8);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
return x_10;
}
}
case 1:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
x_14 = lean_ctor_get(x_3, 3);
x_15 = l_Std_Tactic_BVDecide_BVExpr_eval(x_12, x_2, x_14);
x_16 = l_BitVec_extractLsb_x27(x_12, x_13, x_1, x_15);
lean_dec(x_15);
return x_16;
}
case 3:
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*3 + 8);
x_19 = lean_ctor_get(x_3, 2);
x_20 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_17);
x_21 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_19);
x_22 = l_Std_Tactic_BVDecide_BVBinOp_eval(x_1, x_18, x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
return x_22;
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_3, 1);
x_24 = lean_ctor_get(x_3, 2);
x_25 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_24);
x_26 = l_Std_Tactic_BVDecide_BVUnOp_eval(x_1, x_23, x_25);
lean_dec(x_25);
return x_26;
}
case 5:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
x_29 = lean_ctor_get(x_3, 3);
x_30 = lean_ctor_get(x_3, 4);
x_31 = l_Std_Tactic_BVDecide_BVExpr_eval(x_27, x_2, x_29);
x_32 = l_Std_Tactic_BVDecide_BVExpr_eval(x_28, x_2, x_30);
x_33 = l_BitVec_append(x_27, x_28, x_31, x_32);
lean_dec(x_32);
lean_dec(x_31);
return x_33;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_3, 0);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_ctor_get(x_3, 3);
x_37 = l_Std_Tactic_BVDecide_BVExpr_eval(x_34, x_2, x_36);
x_38 = l_BitVec_replicate(x_34, x_35, x_37);
lean_dec(x_37);
return x_38;
}
case 7:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_3, 1);
x_40 = lean_ctor_get(x_3, 2);
x_41 = lean_ctor_get(x_3, 3);
x_42 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_40);
x_43 = l_Std_Tactic_BVDecide_BVExpr_eval(x_39, x_2, x_41);
x_44 = l_BitVec_toNat(x_39, x_43);
lean_dec(x_43);
x_45 = l_BitVec_shiftLeft(x_1, x_42, x_44);
lean_dec(x_44);
lean_dec(x_42);
return x_45;
}
case 8:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_46 = lean_ctor_get(x_3, 1);
x_47 = lean_ctor_get(x_3, 2);
x_48 = lean_ctor_get(x_3, 3);
x_49 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_47);
x_50 = l_Std_Tactic_BVDecide_BVExpr_eval(x_46, x_2, x_48);
x_51 = l_BitVec_toNat(x_46, x_50);
lean_dec(x_50);
x_52 = l_BitVec_ushiftRight(x_1, x_49, x_51);
lean_dec(x_51);
lean_dec(x_49);
return x_52;
}
default: 
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_53 = lean_ctor_get(x_3, 1);
x_54 = lean_ctor_get(x_3, 2);
x_55 = lean_ctor_get(x_3, 3);
x_56 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_54);
x_57 = l_Std_Tactic_BVDecide_BVExpr_eval(x_53, x_2, x_55);
x_58 = l_BitVec_sshiftRight_x27(x_1, x_53, x_56, x_57);
lean_dec(x_57);
lean_dec(x_56);
return x_58;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVExpr_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_BVExpr_eval(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_apply_2(x_3, x_1, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
x_16 = lean_apply_2(x_4, x_1, x_15);
return x_16;
}
case 2:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 3);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_apply_4(x_5, x_1, x_17, x_18, x_19);
return x_20;
}
case 3:
{
lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
x_22 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_box(x_22);
x_25 = lean_apply_4(x_6, x_1, x_21, x_24, x_23);
return x_25;
}
case 4:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_apply_3(x_7, x_1, x_26, x_27);
return x_28;
}
case 5:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 4);
lean_inc(x_32);
lean_dec(x_2);
x_33 = lean_apply_6(x_8, x_1, x_29, x_30, x_31, x_32, lean_box(0));
return x_33;
}
case 6:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_34 = lean_ctor_get(x_2, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_2, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 3);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_apply_5(x_9, x_1, x_34, x_35, x_36, lean_box(0));
return x_37;
}
case 7:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_ctor_get(x_2, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 3);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_apply_4(x_10, x_1, x_38, x_39, x_40);
return x_41;
}
case 8:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_ctor_get(x_2, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 2);
lean_inc(x_43);
x_44 = lean_ctor_get(x_2, 3);
lean_inc(x_44);
lean_dec(x_2);
x_45 = lean_apply_4(x_11, x_1, x_42, x_43, x_44);
return x_45;
}
default: 
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_46 = lean_ctor_get(x_2, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 3);
lean_inc(x_48);
lean_dec(x_2);
x_49 = lean_apply_4(x_12, x_1, x_46, x_47, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic_0__Std_Tactic_BVDecide_BVExpr_toString_match__1_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinPred_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinOp_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_BVBinPred_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Std_Tactic_BVDecide_BVBinPred_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Std_Tactic_BVDecide_BVBinPred_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("==", 2, 2);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("<u", 2, 2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_toString___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Tactic_BVDecide_BVBinPred_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVBinPred_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVBinPred_toString___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVBinPred_eval(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (x_2 == 0)
{
uint8_t x_5; 
x_5 = lean_nat_dec_eq(x_3, x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = l_BitVec_ult(x_1, x_3, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVBinPred_eval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_BVBinPred_eval(x_1, x_5, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_toString(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_2);
x_7 = l_Std_Tactic_BVDecide_BVExpr_toString(x_2, x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked(" ", 1, 1);
x_10 = lean_string_append(x_8, x_9);
x_11 = l_Std_Tactic_BVDecide_BVBinPred_toString(x_4);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = lean_string_append(x_12, x_9);
lean_dec(x_9);
x_14 = l_Std_Tactic_BVDecide_BVExpr_toString(x_2, x_5);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked(")", 1, 1);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Std_Tactic_BVDecide_BVExpr_toString(x_18, x_19);
x_22 = lean_mk_string_unchecked("[", 1, 1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = l___private_Init_Data_Repr_0__Nat_reprFast(x_20);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("]", 1, 1);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
return x_27;
}
}
}
static lean_object* _init_l_Std_Tactic_BVDecide_BVPred_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVPred_toString), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVPred_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l_Std_Tactic_BVDecide_BVExpr_eval(x_3, x_1, x_4);
x_8 = l_Std_Tactic_BVDecide_BVExpr_eval(x_3, x_1, x_6);
x_9 = l_Std_Tactic_BVDecide_BVBinPred_eval(x_3, x_5, x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = l_Std_Tactic_BVDecide_BVExpr_eval(x_10, x_1, x_11);
x_14 = l_BitVec_toNat(x_10, x_13);
lean_dec(x_13);
x_15 = l_Nat_testBit(x_14, x_12);
lean_dec(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVPred_eval___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVPred_eval(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Std_Tactic_BVDecide_BVPred_eval(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Tactic_BVDecide_BVLogicalExpr_eval(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Std_Tactic_BVDecide_BoolExpr_eval___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVLogicalExpr_eval___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_eval___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Tactic_BVDecide_BVLogicalExpr_eval(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Hashable(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_BitVec(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_RArray(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Hashable(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_RArray(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Bitblast_BoolExpr_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Tactic_BVDecide_instHashableBVBit = _init_l_Std_Tactic_BVDecide_instHashableBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVBit);
l_Std_Tactic_BVDecide_instReprBVBit = _init_l_Std_Tactic_BVDecide_instReprBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instReprBVBit);
l_Std_Tactic_BVDecide_instToStringBVBit = _init_l_Std_Tactic_BVDecide_instToStringBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instToStringBVBit);
l_Std_Tactic_BVDecide_instInhabitedBVBit = _init_l_Std_Tactic_BVDecide_instInhabitedBVBit();
lean_mark_persistent(l_Std_Tactic_BVDecide_instInhabitedBVBit);
l_Std_Tactic_BVDecide_instHashableBVBinOp = _init_l_Std_Tactic_BVDecide_instHashableBVBinOp();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVBinOp);
l_Std_Tactic_BVDecide_BVBinOp_instToString = _init_l_Std_Tactic_BVDecide_BVBinOp_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinOp_instToString);
l_Std_Tactic_BVDecide_instHashableBVUnOp = _init_l_Std_Tactic_BVDecide_instHashableBVUnOp();
lean_mark_persistent(l_Std_Tactic_BVDecide_instHashableBVUnOp);
l_Std_Tactic_BVDecide_BVUnOp_instToString = _init_l_Std_Tactic_BVDecide_BVUnOp_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVUnOp_instToString);
l_Std_Tactic_BVDecide_BVBinPred_instToString = _init_l_Std_Tactic_BVDecide_BVBinPred_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVBinPred_instToString);
l_Std_Tactic_BVDecide_BVPred_instToString = _init_l_Std_Tactic_BVDecide_BVPred_instToString();
lean_mark_persistent(l_Std_Tactic_BVDecide_BVPred_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
