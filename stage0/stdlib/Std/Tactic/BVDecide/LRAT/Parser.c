// Lean compiler output
// Module: Std.Tactic.BVDecide.LRAT.Parser
// Imports: Init.System.IO Std.Tactic.BVDecide.LRAT.Actions Std.Internal.Parsec
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
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_to_uint8(uint32_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object*, lean_object*);
uint32_t l_Char_ofUInt8(uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object*);
uint8_t lean_uint8_lor(uint8_t, uint8_t);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object*, lean_object*);
extern lean_object* l_Int_instInhabited;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
lean_object* lean_mk_empty_byte_array(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object*, lean_object*);
uint8_t lean_uint64_dec_lt(uint64_t, uint64_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object*);
lean_object* l_Std_Internal_Parsec_ByteArray_skipBytes(lean_object*, lean_object*);
uint8_t lean_uint8_land(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0_spec__0(lean_object*, lean_object*);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_land(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object*);
lean_object* l_IO_FS_writeBinFile(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object*, lean_object*);
uint64_t lean_uint64_add(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object*, lean_object*);
uint8_t lean_uint64_to_uint8(uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t, uint64_t, lean_object*);
uint8_t lean_uint8_complement(uint8_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object*, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint8_t lean_uint8_of_nat(lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2_spec__2(lean_object*, lean_object*);
lean_object* l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object*);
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = l_Int_instInhabited;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get(x_2, x_1, x_3);
x_5 = lean_nat_to_int(x_3);
x_6 = lean_int_dec_lt(x_5, x_4);
lean_dec(x_5);
x_7 = lean_nat_abs(x_4);
lean_dec(x_4);
x_8 = lean_box(x_6);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_skipNewline(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_19; uint8_t x_20; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_19 = lean_byte_array_size(x_2);
x_20 = lean_nat_dec_lt(x_3, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_2);
x_21 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_4 = x_1;
x_5 = x_21;
goto block_18;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_22 = lean_unsigned_to_nat(10u);
x_23 = l_Char_ofNat(x_22);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_byte_array_fget(x_2, x_3);
x_26 = lean_uint8_dec_eq(x_25, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_27 = lean_mk_string_unchecked("expected: '", 11, 11);
x_28 = lean_uint8_to_nat(x_24);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_28);
x_30 = lean_string_append(x_27, x_29);
lean_dec(x_29);
x_31 = lean_mk_string_unchecked("'", 1, 1);
x_32 = lean_string_append(x_30, x_31);
lean_dec(x_31);
x_4 = x_1;
x_5 = x_32;
goto block_18;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_nat_add(x_3, x_36);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_37);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_add(x_3, x_40);
lean_dec(x_3);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
block_18:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_nat_dec_eq(x_3, x_6);
lean_dec(x_6);
lean_dec(x_3);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("\r\n", 2, 2);
x_10 = lean_string_to_utf8(x_9);
lean_dec(x_9);
x_11 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_10, x_4);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 1);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_11, 1, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
return x_11;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parsePos(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_unsigned_to_nat(48u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = lean_uint8_dec_le(x_14, x_11);
if (x_15 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(57u);
x_17 = l_Char_ofNat(x_16);
x_18 = lean_uint32_to_uint8(x_17);
x_19 = lean_uint8_dec_le(x_11, x_18);
if (x_19 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_6, x_23);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_24);
x_25 = l_Char_ofUInt8(x_11);
x_26 = lean_uint32_to_uint8(x_25);
x_27 = lean_uint8_sub(x_26, x_14);
x_28 = lean_uint8_to_nat(x_27);
x_29 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_1, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_31, x_33);
if (x_34 == 0)
{
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_35; 
lean_dec(x_31);
x_35 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 1, x_35);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
x_41 = lean_mk_string_unchecked("id was 0", 8, 8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_1);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_6, x_43);
lean_dec(x_6);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Char_ofUInt8(x_11);
x_47 = lean_uint32_to_uint8(x_46);
x_48 = lean_uint8_sub(x_47, x_14);
x_49 = lean_uint8_to_nat(x_48);
x_50 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_45, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_51, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
x_57 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_53)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_53;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("digit expected", 14, 14);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(45u);
x_9 = l_Char_ofNat(x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_uint8_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("expected: '", 11, 11);
x_14 = lean_uint8_to_nat(x_10);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
lean_inc(x_24);
lean_inc(x_2);
lean_ctor_set(x_1, 1, x_24);
x_28 = lean_nat_dec_lt(x_24, x_4);
lean_dec(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_2);
x_29 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; uint32_t x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_byte_array_fget(x_2, x_24);
x_32 = lean_unsigned_to_nat(48u);
x_33 = l_Char_ofNat(x_32);
x_34 = lean_uint32_to_uint8(x_33);
x_35 = lean_uint8_dec_le(x_34, x_31);
if (x_35 == 0)
{
lean_dec(x_24);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_36; uint32_t x_37; uint8_t x_38; uint8_t x_39; 
x_36 = lean_unsigned_to_nat(57u);
x_37 = l_Char_ofNat(x_36);
x_38 = lean_uint32_to_uint8(x_37);
x_39 = lean_uint8_dec_le(x_31, x_38);
if (x_39 == 0)
{
lean_dec(x_24);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_40; lean_object* x_41; uint32_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_1);
x_40 = lean_nat_add(x_24, x_23);
lean_dec(x_24);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Char_ofUInt8(x_31);
x_43 = lean_uint32_to_uint8(x_42);
x_44 = lean_uint8_sub(x_43, x_34);
x_45 = lean_uint8_to_nat(x_44);
x_46 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_41, x_45);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_48, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_nat_to_int(x_48);
x_53 = lean_int_neg(x_52);
lean_dec(x_52);
lean_ctor_set(x_46, 1, x_53);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
else
{
lean_object* x_54; 
lean_dec(x_48);
x_54 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_46, 1);
lean_ctor_set(x_46, 1, x_54);
lean_ctor_set(x_46, 0, x_49);
return x_46;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_55 = lean_ctor_get(x_46, 0);
x_56 = lean_ctor_get(x_46, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_46);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_dec_eq(x_55, x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_nat_to_int(x_55);
x_60 = lean_int_neg(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_56);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_55);
x_62 = lean_mk_string_unchecked("id was 0", 8, 8);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_mk_string_unchecked("digit expected", 14, 14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_70; 
lean_dec(x_1);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_3, x_64);
lean_dec(x_3);
lean_inc(x_65);
lean_inc(x_2);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_2);
lean_ctor_set(x_66, 1, x_65);
x_70 = lean_nat_dec_lt(x_65, x_4);
lean_dec(x_4);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_65);
lean_dec(x_2);
x_71 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_66);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
else
{
uint8_t x_73; lean_object* x_74; uint32_t x_75; uint8_t x_76; uint8_t x_77; 
x_73 = lean_byte_array_fget(x_2, x_65);
x_74 = lean_unsigned_to_nat(48u);
x_75 = l_Char_ofNat(x_74);
x_76 = lean_uint32_to_uint8(x_75);
x_77 = lean_uint8_dec_le(x_76, x_73);
if (x_77 == 0)
{
lean_dec(x_65);
lean_dec(x_2);
goto block_69;
}
else
{
lean_object* x_78; uint32_t x_79; uint8_t x_80; uint8_t x_81; 
x_78 = lean_unsigned_to_nat(57u);
x_79 = l_Char_ofNat(x_78);
x_80 = lean_uint32_to_uint8(x_79);
x_81 = lean_uint8_dec_le(x_73, x_80);
if (x_81 == 0)
{
lean_dec(x_65);
lean_dec(x_2);
goto block_69;
}
else
{
lean_object* x_82; lean_object* x_83; uint32_t x_84; uint8_t x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
lean_dec(x_66);
x_82 = lean_nat_add(x_65, x_64);
lean_dec(x_65);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_2);
lean_ctor_set(x_83, 1, x_82);
x_84 = l_Char_ofUInt8(x_73);
x_85 = lean_uint32_to_uint8(x_84);
x_86 = lean_uint8_sub(x_85, x_76);
x_87 = lean_uint8_to_nat(x_86);
x_88 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_83, x_87);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_91 = x_88;
} else {
 lean_dec_ref(x_88);
 x_91 = lean_box(0);
}
x_92 = lean_unsigned_to_nat(0u);
x_93 = lean_nat_dec_eq(x_89, x_92);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_nat_to_int(x_89);
x_95 = lean_int_neg(x_94);
lean_dec(x_94);
if (lean_is_scalar(x_91)) {
 x_96 = lean_alloc_ctor(0, 2, 0);
} else {
 x_96 = x_91;
}
lean_ctor_set(x_96, 0, x_90);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_89);
x_97 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_91;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_90);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
block_69:
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_mk_string_unchecked("digit expected", 14, 14);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseId(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_unsigned_to_nat(48u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = lean_uint8_dec_le(x_14, x_11);
if (x_15 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(57u);
x_17 = l_Char_ofNat(x_16);
x_18 = lean_uint32_to_uint8(x_17);
x_19 = lean_uint8_dec_le(x_11, x_18);
if (x_19 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_6, x_23);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_24);
x_25 = l_Char_ofUInt8(x_11);
x_26 = lean_uint32_to_uint8(x_25);
x_27 = lean_uint8_sub(x_26, x_14);
x_28 = lean_uint8_to_nat(x_27);
x_29 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_1, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_31, x_33);
if (x_34 == 0)
{
lean_ctor_set(x_29, 1, x_31);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_35; 
lean_dec(x_31);
x_35 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 1, x_35);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_dec_eq(x_36, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_36);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
x_41 = lean_mk_string_unchecked("id was 0", 8, 8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_37);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint32_t x_46; uint8_t x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_1);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_add(x_6, x_43);
lean_dec(x_6);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_5);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Char_ofUInt8(x_11);
x_47 = lean_uint32_to_uint8(x_46);
x_48 = lean_uint8_sub(x_47, x_14);
x_49 = lean_uint8_to_nat(x_48);
x_50 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_45, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_dec_eq(x_51, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_53;
}
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_51);
return x_56;
}
else
{
lean_object* x_57; lean_object* x_58; 
lean_dec(x_51);
x_57 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_53)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_53;
 lean_ctor_set_tag(x_58, 1);
}
lean_ctor_set(x_58, 0, x_52);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("digit expected", 14, 14);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseZero(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(48u);
x_9 = l_Char_ofNat(x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_uint8_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("expected: '", 11, 11);
x_14 = lean_uint8_to_nat(x_10);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_24);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_3, x_27);
lean_dec(x_3);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_2);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_idWs(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_unsigned_to_nat(48u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = lean_uint8_dec_le(x_14, x_11);
if (x_15 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(57u);
x_17 = l_Char_ofNat(x_16);
x_18 = lean_uint32_to_uint8(x_17);
x_19 = lean_uint8_dec_le(x_11, x_18);
if (x_19 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Char_ofUInt8(x_11);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_uint8_sub(x_24, x_14);
x_26 = lean_uint8_to_nat(x_25);
x_27 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_22, x_26);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_29, x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_1);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
x_35 = lean_byte_array_size(x_33);
x_36 = lean_nat_dec_lt(x_34, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
x_37 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_37);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_38; uint32_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; 
x_38 = lean_unsigned_to_nat(32u);
x_39 = l_Char_ofNat(x_38);
x_40 = lean_uint32_to_uint8(x_39);
x_41 = lean_byte_array_fget(x_33, x_34);
x_42 = lean_uint8_dec_eq(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_29);
x_43 = lean_mk_string_unchecked("expected: '", 11, 11);
x_44 = lean_uint8_to_nat(x_40);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
x_46 = lean_string_append(x_43, x_45);
lean_dec(x_45);
x_47 = lean_mk_string_unchecked("'", 1, 1);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_48);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_30);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_30, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_30, 0);
lean_dec(x_51);
x_52 = lean_nat_add(x_34, x_20);
lean_dec(x_34);
lean_ctor_set(x_30, 1, x_52);
lean_ctor_set(x_27, 1, x_29);
lean_ctor_set(x_27, 0, x_30);
return x_27;
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_30);
x_53 = lean_nat_add(x_34, x_20);
lean_dec(x_34);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_33);
lean_ctor_set(x_54, 1, x_53);
lean_ctor_set(x_27, 1, x_29);
lean_ctor_set(x_27, 0, x_54);
return x_27;
}
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_30);
lean_dec(x_29);
x_55 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_27, 1);
lean_ctor_set(x_27, 1, x_55);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_56 = lean_ctor_get(x_27, 0);
x_57 = lean_ctor_get(x_27, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_27);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_56, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_1);
x_60 = lean_ctor_get(x_57, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
x_62 = lean_byte_array_size(x_60);
x_63 = lean_nat_dec_lt(x_61, x_62);
lean_dec(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_56);
x_64 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_57);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; uint32_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; 
x_66 = lean_unsigned_to_nat(32u);
x_67 = l_Char_ofNat(x_66);
x_68 = lean_uint32_to_uint8(x_67);
x_69 = lean_byte_array_fget(x_60, x_61);
x_70 = lean_uint8_dec_eq(x_69, x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_56);
x_71 = lean_mk_string_unchecked("expected: '", 11, 11);
x_72 = lean_uint8_to_nat(x_68);
x_73 = l___private_Init_Data_Repr_0__Nat_reprFast(x_72);
x_74 = lean_string_append(x_71, x_73);
lean_dec(x_73);
x_75 = lean_mk_string_unchecked("'", 1, 1);
x_76 = lean_string_append(x_74, x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_57);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_78 = x_57;
} else {
 lean_dec_ref(x_57);
 x_78 = lean_box(0);
}
x_79 = lean_nat_add(x_61, x_20);
lean_dec(x_61);
if (lean_is_scalar(x_78)) {
 x_80 = lean_alloc_ctor(0, 2, 0);
} else {
 x_80 = x_78;
}
lean_ctor_set(x_80, 0, x_60);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_56);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_57);
lean_dec(x_56);
x_82 = lean_mk_string_unchecked("id was 0", 8, 8);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("digit expected", 14, 14);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_14; uint8_t x_15; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_14 = lean_byte_array_size(x_3);
x_15 = lean_nat_dec_lt(x_4, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_16;
goto block_11;
}
else
{
uint8_t x_17; lean_object* x_18; uint32_t x_19; uint8_t x_20; uint8_t x_21; 
x_17 = lean_byte_array_fget(x_3, x_4);
x_18 = lean_unsigned_to_nat(48u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_to_uint8(x_19);
x_21 = lean_uint8_dec_le(x_20, x_17);
if (x_21 == 0)
{
lean_dec(x_3);
goto block_13;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(57u);
x_23 = l_Char_ofNat(x_22);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_uint8_dec_le(x_17, x_24);
if (x_25 == 0)
{
lean_dec(x_3);
goto block_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint32_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_3);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Char_ofUInt8(x_17);
x_30 = lean_uint32_to_uint8(x_29);
x_31 = lean_uint8_sub(x_30, x_20);
x_32 = lean_uint8_to_nat(x_31);
x_33 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_28, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_dec_eq(x_34, x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_2);
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
x_40 = lean_byte_array_size(x_38);
x_41 = lean_nat_dec_lt(x_39, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
x_42 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_35;
x_6 = x_42;
goto block_11;
}
else
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; 
x_43 = lean_unsigned_to_nat(32u);
x_44 = l_Char_ofNat(x_43);
x_45 = lean_uint32_to_uint8(x_44);
x_46 = lean_byte_array_fget(x_38, x_39);
x_47 = lean_uint8_dec_eq(x_46, x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_34);
x_48 = lean_mk_string_unchecked("expected: '", 11, 11);
x_49 = lean_uint8_to_nat(x_45);
x_50 = l___private_Init_Data_Repr_0__Nat_reprFast(x_49);
x_51 = lean_string_append(x_48, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("'", 1, 1);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_5 = x_35;
x_6 = x_53;
goto block_11;
}
else
{
uint8_t x_54; 
lean_dec(x_4);
x_54 = !lean_is_exclusive(x_35);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_35, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_35, 0);
lean_dec(x_56);
x_57 = lean_nat_add(x_39, x_26);
lean_dec(x_39);
lean_ctor_set(x_35, 1, x_57);
x_58 = lean_array_push(x_1, x_34);
x_1 = x_58;
x_2 = x_35;
goto _start;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_35);
x_60 = lean_nat_add(x_39, x_26);
lean_dec(x_39);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_38);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_array_push(x_1, x_34);
x_1 = x_62;
x_2 = x_61;
goto _start;
}
}
}
}
else
{
lean_object* x_64; 
lean_dec(x_35);
lean_dec(x_34);
x_64 = lean_mk_string_unchecked("id was 0", 8, 8);
x_5 = x_2;
x_6 = x_64;
goto block_11;
}
}
}
}
block_11:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
}
block_13:
{
lean_object* x_12; 
x_12 = lean_mk_string_unchecked("digit expected", 14, 14);
x_5 = x_2;
x_6 = x_12;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList_spec__0(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(100u);
x_9 = l_Char_ofNat(x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_uint8_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("expected: '", 11, 11);
x_14 = lean_uint8_to_nat(x_10);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
lean_inc(x_24);
lean_inc(x_2);
lean_ctor_set(x_1, 1, x_24);
x_25 = lean_nat_dec_lt(x_24, x_4);
lean_dec(x_4);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_2);
x_26 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_1);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
else
{
lean_object* x_28; uint32_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; 
x_28 = lean_unsigned_to_nat(32u);
x_29 = l_Char_ofNat(x_28);
x_30 = lean_uint32_to_uint8(x_29);
x_31 = lean_byte_array_fget(x_2, x_24);
x_32 = lean_uint8_dec_eq(x_31, x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_24);
lean_dec(x_2);
x_33 = lean_mk_string_unchecked("expected: '", 11, 11);
x_34 = lean_uint8_to_nat(x_30);
x_35 = l___private_Init_Data_Repr_0__Nat_reprFast(x_34);
x_36 = lean_string_append(x_33, x_35);
lean_dec(x_35);
x_37 = lean_mk_string_unchecked("'", 1, 1);
x_38 = lean_string_append(x_36, x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_1);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_40 = lean_nat_add(x_24, x_23);
lean_dec(x_24);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_41);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_ctor_get(x_44, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = lean_byte_array_size(x_46);
x_49 = lean_nat_dec_lt(x_47, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_50 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_50);
return x_42;
}
else
{
lean_object* x_51; uint32_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; 
x_51 = lean_unsigned_to_nat(48u);
x_52 = l_Char_ofNat(x_51);
x_53 = lean_uint32_to_uint8(x_52);
x_54 = lean_byte_array_fget(x_46, x_47);
x_55 = lean_uint8_dec_eq(x_54, x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
x_56 = lean_mk_string_unchecked("expected: '", 11, 11);
x_57 = lean_uint8_to_nat(x_53);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_57);
x_59 = lean_string_append(x_56, x_58);
lean_dec(x_58);
x_60 = lean_mk_string_unchecked("'", 1, 1);
x_61 = lean_string_append(x_59, x_60);
lean_dec(x_60);
lean_ctor_set_tag(x_42, 1);
lean_ctor_set(x_42, 1, x_61);
return x_42;
}
else
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_44);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_44, 1);
lean_dec(x_63);
x_64 = lean_ctor_get(x_44, 0);
lean_dec(x_64);
x_65 = lean_nat_add(x_47, x_23);
lean_dec(x_47);
lean_ctor_set(x_44, 1, x_65);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_45);
lean_ctor_set(x_42, 1, x_66);
return x_42;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_44);
x_67 = lean_nat_add(x_47, x_23);
lean_dec(x_47);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_46);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_69, 0, x_45);
lean_ctor_set(x_42, 1, x_69);
lean_ctor_set(x_42, 0, x_68);
return x_42;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_70 = lean_ctor_get(x_42, 0);
x_71 = lean_ctor_get(x_42, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_42);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_70, 1);
lean_inc(x_73);
x_74 = lean_byte_array_size(x_72);
x_75 = lean_nat_dec_lt(x_73, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_76 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_70);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
else
{
lean_object* x_78; uint32_t x_79; uint8_t x_80; uint8_t x_81; uint8_t x_82; 
x_78 = lean_unsigned_to_nat(48u);
x_79 = l_Char_ofNat(x_78);
x_80 = lean_uint32_to_uint8(x_79);
x_81 = lean_byte_array_fget(x_72, x_73);
x_82 = lean_uint8_dec_eq(x_81, x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
x_83 = lean_mk_string_unchecked("expected: '", 11, 11);
x_84 = lean_uint8_to_nat(x_80);
x_85 = l___private_Init_Data_Repr_0__Nat_reprFast(x_84);
x_86 = lean_string_append(x_83, x_85);
lean_dec(x_85);
x_87 = lean_mk_string_unchecked("'", 1, 1);
x_88 = lean_string_append(x_86, x_87);
lean_dec(x_87);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_70);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_90 = x_70;
} else {
 lean_dec_ref(x_70);
 x_90 = lean_box(0);
}
x_91 = lean_nat_add(x_73, x_23);
lean_dec(x_73);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_72);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_71);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
else
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_42);
if (x_95 == 0)
{
return x_42;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_42, 0);
x_97 = lean_ctor_get(x_42, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_42);
x_98 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
return x_98;
}
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_1);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_nat_add(x_3, x_99);
lean_dec(x_3);
lean_inc(x_100);
lean_inc(x_2);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_2);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_nat_dec_lt(x_100, x_4);
lean_dec(x_4);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
lean_dec(x_100);
lean_dec(x_2);
x_103 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
else
{
lean_object* x_105; uint32_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; 
x_105 = lean_unsigned_to_nat(32u);
x_106 = l_Char_ofNat(x_105);
x_107 = lean_uint32_to_uint8(x_106);
x_108 = lean_byte_array_fget(x_2, x_100);
x_109 = lean_uint8_dec_eq(x_108, x_107);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
lean_dec(x_100);
lean_dec(x_2);
x_110 = lean_mk_string_unchecked("expected: '", 11, 11);
x_111 = lean_uint8_to_nat(x_107);
x_112 = l___private_Init_Data_Repr_0__Nat_reprFast(x_111);
x_113 = lean_string_append(x_110, x_112);
lean_dec(x_112);
x_114 = lean_mk_string_unchecked("'", 1, 1);
x_115 = lean_string_append(x_113, x_114);
lean_dec(x_114);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_101);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_101);
x_117 = lean_nat_add(x_100, x_99);
lean_dec(x_100);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_2);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_120, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_120, 1);
lean_inc(x_124);
x_125 = lean_byte_array_size(x_123);
x_126 = lean_nat_dec_lt(x_124, x_125);
lean_dec(x_125);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
x_127 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_122)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_122;
 lean_ctor_set_tag(x_128, 1);
}
lean_ctor_set(x_128, 0, x_120);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
else
{
lean_object* x_129; uint32_t x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; 
x_129 = lean_unsigned_to_nat(48u);
x_130 = l_Char_ofNat(x_129);
x_131 = lean_uint32_to_uint8(x_130);
x_132 = lean_byte_array_fget(x_123, x_124);
x_133 = lean_uint8_dec_eq(x_132, x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_121);
x_134 = lean_mk_string_unchecked("expected: '", 11, 11);
x_135 = lean_uint8_to_nat(x_131);
x_136 = l___private_Init_Data_Repr_0__Nat_reprFast(x_135);
x_137 = lean_string_append(x_134, x_136);
lean_dec(x_136);
x_138 = lean_mk_string_unchecked("'", 1, 1);
x_139 = lean_string_append(x_137, x_138);
lean_dec(x_138);
if (lean_is_scalar(x_122)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_122;
 lean_ctor_set_tag(x_140, 1);
}
lean_ctor_set(x_140, 0, x_120);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_141 = x_120;
} else {
 lean_dec_ref(x_120);
 x_141 = lean_box(0);
}
x_142 = lean_nat_add(x_124, x_99);
lean_dec(x_124);
if (lean_is_scalar(x_141)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_141;
}
lean_ctor_set(x_143, 0, x_123);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_144, 0, x_121);
if (lean_is_scalar(x_122)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_122;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_146 = lean_ctor_get(x_119, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_119, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_148 = x_119;
} else {
 lean_dec_ref(x_119);
 x_148 = lean_box(0);
}
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseLit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_unsigned_to_nat(45u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = lean_uint8_dec_eq(x_11, x_14);
if (x_15 == 0)
{
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(48u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_to_uint8(x_19);
x_21 = lean_uint8_dec_le(x_20, x_11);
if (x_21 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; 
x_22 = lean_unsigned_to_nat(57u);
x_23 = l_Char_ofNat(x_22);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_uint8_dec_le(x_11, x_24);
if (x_25 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_1);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint32_t x_31; uint8_t x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_27 = lean_ctor_get(x_1, 1);
lean_dec(x_27);
x_28 = lean_ctor_get(x_1, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_6, x_29);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_30);
x_31 = l_Char_ofUInt8(x_11);
x_32 = lean_uint32_to_uint8(x_31);
x_33 = lean_uint8_sub(x_32, x_20);
x_34 = lean_uint8_to_nat(x_33);
x_35 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_1, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_nat_dec_eq(x_37, x_39);
if (x_40 == 0)
{
lean_object* x_41; 
x_41 = lean_nat_to_int(x_37);
lean_ctor_set(x_35, 1, x_41);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_42; 
lean_dec(x_37);
x_42 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_42);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_35, 0);
x_44 = lean_ctor_get(x_35, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_35);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_nat_dec_eq(x_43, x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_nat_to_int(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_49 = lean_mk_string_unchecked("id was 0", 8, 8);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_44);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint32_t x_54; uint8_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_1);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_6, x_51);
lean_dec(x_6);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Char_ofUInt8(x_11);
x_55 = lean_uint32_to_uint8(x_54);
x_56 = lean_uint8_sub(x_55, x_20);
x_57 = lean_uint8_to_nat(x_56);
x_58 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_53, x_57);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_nat_dec_eq(x_59, x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_nat_to_int(x_59);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_60);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_59);
x_66 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_61)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_61;
 lean_ctor_set_tag(x_67, 1);
}
lean_ctor_set(x_67, 0, x_60);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
}
else
{
if (x_8 == 0)
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
if (x_15 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = lean_mk_string_unchecked("expected: '", 11, 11);
x_71 = lean_uint8_to_nat(x_14);
x_72 = l___private_Init_Data_Repr_0__Nat_reprFast(x_71);
x_73 = lean_string_append(x_70, x_72);
lean_dec(x_72);
x_74 = lean_mk_string_unchecked("'", 1, 1);
x_75 = lean_string_append(x_73, x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
uint8_t x_77; 
x_77 = !lean_is_exclusive(x_1);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_85; 
x_78 = lean_ctor_get(x_1, 1);
lean_dec(x_78);
x_79 = lean_ctor_get(x_1, 0);
lean_dec(x_79);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_6, x_80);
lean_dec(x_6);
lean_inc(x_81);
lean_inc(x_5);
lean_ctor_set(x_1, 1, x_81);
x_85 = lean_nat_dec_lt(x_81, x_7);
lean_dec(x_7);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_81);
lean_dec(x_5);
x_86 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_1);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
else
{
uint8_t x_88; lean_object* x_89; uint32_t x_90; uint8_t x_91; uint8_t x_92; 
x_88 = lean_byte_array_fget(x_5, x_81);
x_89 = lean_unsigned_to_nat(48u);
x_90 = l_Char_ofNat(x_89);
x_91 = lean_uint32_to_uint8(x_90);
x_92 = lean_uint8_dec_le(x_91, x_88);
if (x_92 == 0)
{
lean_dec(x_81);
lean_dec(x_5);
goto block_84;
}
else
{
lean_object* x_93; uint32_t x_94; uint8_t x_95; uint8_t x_96; 
x_93 = lean_unsigned_to_nat(57u);
x_94 = l_Char_ofNat(x_93);
x_95 = lean_uint32_to_uint8(x_94);
x_96 = lean_uint8_dec_le(x_88, x_95);
if (x_96 == 0)
{
lean_dec(x_81);
lean_dec(x_5);
goto block_84;
}
else
{
lean_object* x_97; lean_object* x_98; uint32_t x_99; uint8_t x_100; uint8_t x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
lean_dec(x_1);
x_97 = lean_nat_add(x_81, x_80);
lean_dec(x_81);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_5);
lean_ctor_set(x_98, 1, x_97);
x_99 = l_Char_ofUInt8(x_88);
x_100 = lean_uint32_to_uint8(x_99);
x_101 = lean_uint8_sub(x_100, x_91);
x_102 = lean_uint8_to_nat(x_101);
x_103 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_98, x_102);
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_ctor_get(x_103, 1);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_105, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_nat_to_int(x_105);
x_110 = lean_int_neg(x_109);
lean_dec(x_109);
lean_ctor_set(x_103, 1, x_110);
lean_ctor_set(x_103, 0, x_106);
return x_103;
}
else
{
lean_object* x_111; 
lean_dec(x_105);
x_111 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_103, 1);
lean_ctor_set(x_103, 1, x_111);
lean_ctor_set(x_103, 0, x_106);
return x_103;
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_103, 0);
x_113 = lean_ctor_get(x_103, 1);
lean_inc(x_113);
lean_inc(x_112);
lean_dec(x_103);
x_114 = lean_unsigned_to_nat(0u);
x_115 = lean_nat_dec_eq(x_112, x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_nat_to_int(x_112);
x_117 = lean_int_neg(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_113);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
else
{
lean_object* x_119; lean_object* x_120; 
lean_dec(x_112);
x_119 = lean_mk_string_unchecked("id was 0", 8, 8);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_113);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
}
}
block_84:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_mk_string_unchecked("digit expected", 14, 14);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_127; 
lean_dec(x_1);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_add(x_6, x_121);
lean_dec(x_6);
lean_inc(x_122);
lean_inc(x_5);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_5);
lean_ctor_set(x_123, 1, x_122);
x_127 = lean_nat_dec_lt(x_122, x_7);
lean_dec(x_7);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; 
lean_dec(x_122);
lean_dec(x_5);
x_128 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_123);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
else
{
uint8_t x_130; lean_object* x_131; uint32_t x_132; uint8_t x_133; uint8_t x_134; 
x_130 = lean_byte_array_fget(x_5, x_122);
x_131 = lean_unsigned_to_nat(48u);
x_132 = l_Char_ofNat(x_131);
x_133 = lean_uint32_to_uint8(x_132);
x_134 = lean_uint8_dec_le(x_133, x_130);
if (x_134 == 0)
{
lean_dec(x_122);
lean_dec(x_5);
goto block_126;
}
else
{
lean_object* x_135; uint32_t x_136; uint8_t x_137; uint8_t x_138; 
x_135 = lean_unsigned_to_nat(57u);
x_136 = l_Char_ofNat(x_135);
x_137 = lean_uint32_to_uint8(x_136);
x_138 = lean_uint8_dec_le(x_130, x_137);
if (x_138 == 0)
{
lean_dec(x_122);
lean_dec(x_5);
goto block_126;
}
else
{
lean_object* x_139; lean_object* x_140; uint32_t x_141; uint8_t x_142; uint8_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
lean_dec(x_123);
x_139 = lean_nat_add(x_122, x_121);
lean_dec(x_122);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_5);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Char_ofUInt8(x_130);
x_142 = lean_uint32_to_uint8(x_141);
x_143 = lean_uint8_sub(x_142, x_133);
x_144 = lean_uint8_to_nat(x_143);
x_145 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_140, x_144);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_unsigned_to_nat(0u);
x_150 = lean_nat_dec_eq(x_146, x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_nat_to_int(x_146);
x_152 = lean_int_neg(x_151);
lean_dec(x_151);
if (lean_is_scalar(x_148)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_148;
}
lean_ctor_set(x_153, 0, x_147);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; 
lean_dec(x_146);
x_154 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_148)) {
 x_155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_155 = x_148;
 lean_ctor_set_tag(x_155, 1);
}
lean_ctor_set(x_155, 0, x_147);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
block_126:
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_mk_string_unchecked("digit expected", 14, 14);
x_125 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
return x_125;
}
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("digit expected", 14, 14);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_litWs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
x_41 = lean_byte_array_size(x_39);
x_42 = lean_nat_dec_lt(x_40, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_43 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
else
{
uint8_t x_45; lean_object* x_46; uint32_t x_47; uint8_t x_48; uint8_t x_49; 
x_45 = lean_byte_array_fget(x_39, x_40);
x_46 = lean_unsigned_to_nat(45u);
x_47 = l_Char_ofNat(x_46);
x_48 = lean_uint32_to_uint8(x_47);
x_49 = lean_uint8_dec_eq(x_45, x_48);
if (x_49 == 0)
{
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_40);
lean_dec(x_39);
x_50 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_1);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
lean_object* x_52; uint32_t x_53; uint8_t x_54; uint8_t x_55; 
x_52 = lean_unsigned_to_nat(48u);
x_53 = l_Char_ofNat(x_52);
x_54 = lean_uint32_to_uint8(x_53);
x_55 = lean_uint8_dec_le(x_54, x_45);
if (x_55 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
goto block_35;
}
else
{
lean_object* x_56; uint32_t x_57; uint8_t x_58; uint8_t x_59; 
x_56 = lean_unsigned_to_nat(57u);
x_57 = l_Char_ofNat(x_56);
x_58 = lean_uint32_to_uint8(x_57);
x_59 = lean_uint8_dec_le(x_45, x_58);
if (x_59 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
goto block_35;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint32_t x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_40, x_60);
lean_dec(x_40);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_39);
lean_ctor_set(x_62, 1, x_61);
x_63 = l_Char_ofUInt8(x_45);
x_64 = lean_uint32_to_uint8(x_63);
x_65 = lean_uint8_sub(x_64, x_54);
x_66 = lean_uint8_to_nat(x_65);
x_67 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_62, x_66);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
x_71 = lean_unsigned_to_nat(0u);
x_72 = lean_nat_dec_eq(x_69, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
lean_free_object(x_67);
lean_dec(x_1);
x_73 = lean_nat_to_int(x_69);
x_2 = x_70;
x_3 = x_73;
goto block_32;
}
else
{
lean_object* x_74; 
lean_dec(x_70);
lean_dec(x_69);
x_74 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_67, 1);
lean_ctor_set(x_67, 1, x_74);
lean_ctor_set(x_67, 0, x_1);
return x_67;
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_75 = lean_ctor_get(x_67, 0);
x_76 = lean_ctor_get(x_67, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_67);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_nat_dec_eq(x_75, x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_1);
x_79 = lean_nat_to_int(x_75);
x_2 = x_76;
x_3 = x_79;
goto block_32;
}
else
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_76);
lean_dec(x_75);
x_80 = lean_mk_string_unchecked("id was 0", 8, 8);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_1);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
}
}
else
{
if (x_42 == 0)
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_82 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_1);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
else
{
if (x_49 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_84 = lean_mk_string_unchecked("expected: '", 11, 11);
x_85 = lean_uint8_to_nat(x_48);
x_86 = l___private_Init_Data_Repr_0__Nat_reprFast(x_85);
x_87 = lean_string_append(x_84, x_86);
lean_dec(x_86);
x_88 = lean_mk_string_unchecked("'", 1, 1);
x_89 = lean_string_append(x_87, x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_1);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_unsigned_to_nat(1u);
x_92 = lean_nat_add(x_40, x_91);
lean_dec(x_40);
x_93 = lean_nat_dec_lt(x_92, x_41);
lean_dec(x_41);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_92);
lean_dec(x_39);
x_94 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_1);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
else
{
uint8_t x_96; lean_object* x_97; uint32_t x_98; uint8_t x_99; uint8_t x_100; 
x_96 = lean_byte_array_fget(x_39, x_92);
x_97 = lean_unsigned_to_nat(48u);
x_98 = l_Char_ofNat(x_97);
x_99 = lean_uint32_to_uint8(x_98);
x_100 = lean_uint8_dec_le(x_99, x_96);
if (x_100 == 0)
{
lean_dec(x_92);
lean_dec(x_39);
goto block_38;
}
else
{
lean_object* x_101; uint32_t x_102; uint8_t x_103; uint8_t x_104; 
x_101 = lean_unsigned_to_nat(57u);
x_102 = l_Char_ofNat(x_101);
x_103 = lean_uint32_to_uint8(x_102);
x_104 = lean_uint8_dec_le(x_96, x_103);
if (x_104 == 0)
{
lean_dec(x_92);
lean_dec(x_39);
goto block_38;
}
else
{
lean_object* x_105; lean_object* x_106; uint32_t x_107; uint8_t x_108; uint8_t x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_105 = lean_nat_add(x_92, x_91);
lean_dec(x_92);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_39);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Char_ofUInt8(x_96);
x_108 = lean_uint32_to_uint8(x_107);
x_109 = lean_uint8_sub(x_108, x_99);
x_110 = lean_uint8_to_nat(x_109);
x_111 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_106, x_110);
x_112 = !lean_is_exclusive(x_111);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_113 = lean_ctor_get(x_111, 0);
x_114 = lean_ctor_get(x_111, 1);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_nat_dec_eq(x_113, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; 
lean_free_object(x_111);
lean_dec(x_1);
x_117 = lean_nat_to_int(x_113);
x_118 = lean_int_neg(x_117);
lean_dec(x_117);
x_2 = x_114;
x_3 = x_118;
goto block_32;
}
else
{
lean_object* x_119; 
lean_dec(x_114);
lean_dec(x_113);
x_119 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_111, 1);
lean_ctor_set(x_111, 1, x_119);
lean_ctor_set(x_111, 0, x_1);
return x_111;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_111, 0);
x_121 = lean_ctor_get(x_111, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_111);
x_122 = lean_unsigned_to_nat(0u);
x_123 = lean_nat_dec_eq(x_120, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_124 = lean_nat_to_int(x_120);
x_125 = lean_int_neg(x_124);
lean_dec(x_124);
x_2 = x_121;
x_3 = x_125;
goto block_32;
}
else
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_121);
lean_dec(x_120);
x_126 = lean_mk_string_unchecked("id was 0", 8, 8);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_1);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
}
}
}
}
}
}
}
}
block_32:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; uint32_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(32u);
x_11 = l_Char_ofNat(x_10);
x_12 = lean_uint32_to_uint8(x_11);
x_13 = lean_byte_array_fget(x_4, x_5);
x_14 = lean_uint8_dec_eq(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = lean_mk_string_unchecked("expected: '", 11, 11);
x_16 = lean_uint8_to_nat(x_12);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("'", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_2, 1);
lean_dec(x_23);
x_24 = lean_ctor_get(x_2, 0);
lean_dec(x_24);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_5, x_25);
lean_dec(x_5);
lean_ctor_set(x_2, 1, x_26);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_2);
lean_ctor_set(x_27, 1, x_3);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_add(x_5, x_28);
lean_dec(x_5);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_3);
return x_31;
}
}
}
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_mk_string_unchecked("digit expected", 14, 14);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
block_38:
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_mk_string_unchecked("digit expected", 14, 14);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_47; uint8_t x_48; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_47 = lean_byte_array_size(x_3);
x_48 = lean_nat_dec_lt(x_4, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_3);
x_49 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_49;
goto block_11;
}
else
{
uint8_t x_50; lean_object* x_51; uint32_t x_52; uint8_t x_53; uint8_t x_54; 
x_50 = lean_byte_array_fget(x_3, x_4);
x_51 = lean_unsigned_to_nat(45u);
x_52 = l_Char_ofNat(x_51);
x_53 = lean_uint32_to_uint8(x_52);
x_54 = lean_uint8_dec_eq(x_50, x_53);
if (x_54 == 0)
{
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_55; 
lean_dec(x_3);
x_55 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_55;
goto block_11;
}
else
{
lean_object* x_56; uint32_t x_57; uint8_t x_58; uint8_t x_59; 
x_56 = lean_unsigned_to_nat(48u);
x_57 = l_Char_ofNat(x_56);
x_58 = lean_uint32_to_uint8(x_57);
x_59 = lean_uint8_dec_le(x_58, x_50);
if (x_59 == 0)
{
lean_dec(x_3);
goto block_44;
}
else
{
lean_object* x_60; uint32_t x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_unsigned_to_nat(57u);
x_61 = l_Char_ofNat(x_60);
x_62 = lean_uint32_to_uint8(x_61);
x_63 = lean_uint8_dec_le(x_50, x_62);
if (x_63 == 0)
{
lean_dec(x_3);
goto block_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint32_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_4, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Char_ofUInt8(x_50);
x_68 = lean_uint32_to_uint8(x_67);
x_69 = lean_uint8_sub(x_68, x_58);
x_70 = lean_uint8_to_nat(x_69);
x_71 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_66, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_72, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_2);
x_76 = lean_nat_to_int(x_72);
x_12 = x_73;
x_13 = x_76;
goto block_42;
}
else
{
lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_72);
x_77 = lean_mk_string_unchecked("id was 0", 8, 8);
x_5 = x_2;
x_6 = x_77;
goto block_11;
}
}
}
}
}
else
{
if (x_48 == 0)
{
lean_object* x_78; 
lean_dec(x_47);
lean_dec(x_3);
x_78 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_78;
goto block_11;
}
else
{
if (x_54 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_47);
lean_dec(x_3);
x_79 = lean_mk_string_unchecked("expected: '", 11, 11);
x_80 = lean_uint8_to_nat(x_53);
x_81 = l___private_Init_Data_Repr_0__Nat_reprFast(x_80);
x_82 = lean_string_append(x_79, x_81);
lean_dec(x_81);
x_83 = lean_mk_string_unchecked("'", 1, 1);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_5 = x_2;
x_6 = x_84;
goto block_11;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_4, x_85);
x_87 = lean_nat_dec_lt(x_86, x_47);
lean_dec(x_47);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_86);
lean_dec(x_3);
x_88 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_88;
goto block_11;
}
else
{
uint8_t x_89; lean_object* x_90; uint32_t x_91; uint8_t x_92; uint8_t x_93; 
x_89 = lean_byte_array_fget(x_3, x_86);
x_90 = lean_unsigned_to_nat(48u);
x_91 = l_Char_ofNat(x_90);
x_92 = lean_uint32_to_uint8(x_91);
x_93 = lean_uint8_dec_le(x_92, x_89);
if (x_93 == 0)
{
lean_dec(x_86);
lean_dec(x_3);
goto block_46;
}
else
{
lean_object* x_94; uint32_t x_95; uint8_t x_96; uint8_t x_97; 
x_94 = lean_unsigned_to_nat(57u);
x_95 = l_Char_ofNat(x_94);
x_96 = lean_uint32_to_uint8(x_95);
x_97 = lean_uint8_dec_le(x_89, x_96);
if (x_97 == 0)
{
lean_dec(x_86);
lean_dec(x_3);
goto block_46;
}
else
{
lean_object* x_98; lean_object* x_99; uint32_t x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_98 = lean_nat_add(x_86, x_85);
lean_dec(x_86);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_3);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Char_ofUInt8(x_89);
x_101 = lean_uint32_to_uint8(x_100);
x_102 = lean_uint8_sub(x_101, x_92);
x_103 = lean_uint8_to_nat(x_102);
x_104 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_99, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_105, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_2);
x_109 = lean_nat_to_int(x_105);
x_110 = lean_int_neg(x_109);
lean_dec(x_109);
x_12 = x_106;
x_13 = x_110;
goto block_42;
}
else
{
lean_object* x_111; 
lean_dec(x_106);
lean_dec(x_105);
x_111 = lean_mk_string_unchecked("id was 0", 8, 8);
x_5 = x_2;
x_6 = x_111;
goto block_11;
}
}
}
}
}
}
}
}
block_11:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
}
block_42:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_byte_array_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_12;
x_6 = x_18;
goto block_11;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(32u);
x_20 = l_Char_ofNat(x_19);
x_21 = lean_uint32_to_uint8(x_20);
x_22 = lean_byte_array_fget(x_14, x_15);
x_23 = lean_uint8_dec_eq(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_24 = lean_mk_string_unchecked("expected: '", 11, 11);
x_25 = lean_uint8_to_nat(x_21);
x_26 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
x_27 = lean_string_append(x_24, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("'", 1, 1);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_5 = x_12;
x_6 = x_29;
goto block_11;
}
else
{
uint8_t x_30; 
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_12, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_15, x_33);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_34);
x_35 = lean_array_push(x_1, x_13);
x_1 = x_35;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_12);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_15, x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_push(x_1, x_13);
x_1 = x_40;
x_2 = x_39;
goto _start;
}
}
}
}
block_44:
{
lean_object* x_43; 
x_43 = lean_mk_string_unchecked("digit expected", 14, 14);
x_5 = x_2;
x_6 = x_43;
goto block_11;
}
block_46:
{
lean_object* x_45; 
x_45 = lean_mk_string_unchecked("digit expected", 14, 14);
x_5 = x_2;
x_6 = x_45;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_12; lean_object* x_13; lean_object* x_47; uint8_t x_48; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_47 = lean_byte_array_size(x_3);
x_48 = lean_nat_dec_lt(x_4, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_3);
x_49 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_49;
goto block_11;
}
else
{
uint8_t x_50; lean_object* x_51; uint32_t x_52; uint8_t x_53; uint8_t x_54; 
x_50 = lean_byte_array_fget(x_3, x_4);
x_51 = lean_unsigned_to_nat(45u);
x_52 = l_Char_ofNat(x_51);
x_53 = lean_uint32_to_uint8(x_52);
x_54 = lean_uint8_dec_eq(x_50, x_53);
if (x_54 == 0)
{
lean_dec(x_47);
if (x_48 == 0)
{
lean_object* x_55; 
lean_dec(x_3);
x_55 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_55;
goto block_11;
}
else
{
lean_object* x_56; uint32_t x_57; uint8_t x_58; uint8_t x_59; 
x_56 = lean_unsigned_to_nat(48u);
x_57 = l_Char_ofNat(x_56);
x_58 = lean_uint32_to_uint8(x_57);
x_59 = lean_uint8_dec_le(x_58, x_50);
if (x_59 == 0)
{
lean_dec(x_3);
goto block_44;
}
else
{
lean_object* x_60; uint32_t x_61; uint8_t x_62; uint8_t x_63; 
x_60 = lean_unsigned_to_nat(57u);
x_61 = l_Char_ofNat(x_60);
x_62 = lean_uint32_to_uint8(x_61);
x_63 = lean_uint8_dec_le(x_50, x_62);
if (x_63 == 0)
{
lean_dec(x_3);
goto block_44;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint32_t x_67; uint8_t x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_4, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Char_ofUInt8(x_50);
x_68 = lean_uint32_to_uint8(x_67);
x_69 = lean_uint8_sub(x_68, x_58);
x_70 = lean_uint8_to_nat(x_69);
x_71 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_66, x_70);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
lean_dec(x_71);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_dec_eq(x_72, x_74);
if (x_75 == 0)
{
lean_object* x_76; 
lean_dec(x_2);
x_76 = lean_nat_to_int(x_72);
x_12 = x_73;
x_13 = x_76;
goto block_42;
}
else
{
lean_object* x_77; 
lean_dec(x_73);
lean_dec(x_72);
x_77 = lean_mk_string_unchecked("id was 0", 8, 8);
x_5 = x_2;
x_6 = x_77;
goto block_11;
}
}
}
}
}
else
{
if (x_48 == 0)
{
lean_object* x_78; 
lean_dec(x_47);
lean_dec(x_3);
x_78 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_78;
goto block_11;
}
else
{
if (x_54 == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_47);
lean_dec(x_3);
x_79 = lean_mk_string_unchecked("expected: '", 11, 11);
x_80 = lean_uint8_to_nat(x_53);
x_81 = l___private_Init_Data_Repr_0__Nat_reprFast(x_80);
x_82 = lean_string_append(x_79, x_81);
lean_dec(x_81);
x_83 = lean_mk_string_unchecked("'", 1, 1);
x_84 = lean_string_append(x_82, x_83);
lean_dec(x_83);
x_5 = x_2;
x_6 = x_84;
goto block_11;
}
else
{
lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_85 = lean_unsigned_to_nat(1u);
x_86 = lean_nat_add(x_4, x_85);
x_87 = lean_nat_dec_lt(x_86, x_47);
lean_dec(x_47);
if (x_87 == 0)
{
lean_object* x_88; 
lean_dec(x_86);
lean_dec(x_3);
x_88 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_2;
x_6 = x_88;
goto block_11;
}
else
{
uint8_t x_89; lean_object* x_90; uint32_t x_91; uint8_t x_92; uint8_t x_93; 
x_89 = lean_byte_array_fget(x_3, x_86);
x_90 = lean_unsigned_to_nat(48u);
x_91 = l_Char_ofNat(x_90);
x_92 = lean_uint32_to_uint8(x_91);
x_93 = lean_uint8_dec_le(x_92, x_89);
if (x_93 == 0)
{
lean_dec(x_86);
lean_dec(x_3);
goto block_46;
}
else
{
lean_object* x_94; uint32_t x_95; uint8_t x_96; uint8_t x_97; 
x_94 = lean_unsigned_to_nat(57u);
x_95 = l_Char_ofNat(x_94);
x_96 = lean_uint32_to_uint8(x_95);
x_97 = lean_uint8_dec_le(x_89, x_96);
if (x_97 == 0)
{
lean_dec(x_86);
lean_dec(x_3);
goto block_46;
}
else
{
lean_object* x_98; lean_object* x_99; uint32_t x_100; uint8_t x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; 
x_98 = lean_nat_add(x_86, x_85);
lean_dec(x_86);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_3);
lean_ctor_set(x_99, 1, x_98);
x_100 = l_Char_ofUInt8(x_89);
x_101 = lean_uint32_to_uint8(x_100);
x_102 = lean_uint8_sub(x_101, x_92);
x_103 = lean_uint8_to_nat(x_102);
x_104 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_99, x_103);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_unsigned_to_nat(0u);
x_108 = lean_nat_dec_eq(x_105, x_107);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; 
lean_dec(x_2);
x_109 = lean_nat_to_int(x_105);
x_110 = lean_int_neg(x_109);
lean_dec(x_109);
x_12 = x_106;
x_13 = x_110;
goto block_42;
}
else
{
lean_object* x_111; 
lean_dec(x_106);
lean_dec(x_105);
x_111 = lean_mk_string_unchecked("id was 0", 8, 8);
x_5 = x_2;
x_6 = x_111;
goto block_11;
}
}
}
}
}
}
}
}
block_11:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_nat_dec_eq(x_4, x_7);
lean_dec(x_7);
lean_dec(x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_1);
return x_10;
}
}
block_42:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_byte_array_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_18 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_5 = x_12;
x_6 = x_18;
goto block_11;
}
else
{
lean_object* x_19; uint32_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; 
x_19 = lean_unsigned_to_nat(32u);
x_20 = l_Char_ofNat(x_19);
x_21 = lean_uint32_to_uint8(x_20);
x_22 = lean_byte_array_fget(x_14, x_15);
x_23 = lean_uint8_dec_eq(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_24 = lean_mk_string_unchecked("expected: '", 11, 11);
x_25 = lean_uint8_to_nat(x_21);
x_26 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
x_27 = lean_string_append(x_24, x_26);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("'", 1, 1);
x_29 = lean_string_append(x_27, x_28);
lean_dec(x_28);
x_5 = x_12;
x_6 = x_29;
goto block_11;
}
else
{
uint8_t x_30; 
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_ctor_get(x_12, 1);
lean_dec(x_31);
x_32 = lean_ctor_get(x_12, 0);
lean_dec(x_32);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_nat_add(x_15, x_33);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_34);
x_35 = lean_array_push(x_1, x_13);
x_36 = l_Std_Internal_Parsec_manyCore___at___Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0_spec__0(x_35, x_12);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_12);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_nat_add(x_15, x_37);
lean_dec(x_15);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_14);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_array_push(x_1, x_13);
x_41 = l_Std_Internal_Parsec_manyCore___at___Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0_spec__0(x_40, x_39);
return x_41;
}
}
}
}
block_44:
{
lean_object* x_43; 
x_43 = lean_mk_string_unchecked("digit expected", 14, 14);
x_5 = x_2;
x_6 = x_43;
goto block_11;
}
block_46:
{
lean_object* x_45; 
x_45 = lean_mk_string_unchecked("digit expected", 14, 14);
x_5 = x_2;
x_6 = x_45;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause_spec__0(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_byte_array_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_12 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_12);
return x_4;
}
else
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; 
x_13 = lean_unsigned_to_nat(48u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_uint32_to_uint8(x_14);
x_16 = lean_byte_array_fget(x_8, x_9);
x_17 = lean_uint8_dec_eq(x_16, x_15);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_18 = lean_mk_string_unchecked("expected: '", 11, 11);
x_19 = lean_uint8_to_nat(x_15);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_21 = lean_string_append(x_18, x_20);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_23);
return x_4;
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_6);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_6, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_6, 0);
lean_dec(x_26);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_9, x_27);
lean_dec(x_9);
lean_ctor_set(x_6, 1, x_28);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_6);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_nat_add(x_9, x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_8);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_4, 0, x_31);
return x_4;
}
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_4, 0);
x_33 = lean_ctor_get(x_4, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_4);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
x_36 = lean_byte_array_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_38 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
else
{
lean_object* x_40; uint32_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_40 = lean_unsigned_to_nat(48u);
x_41 = l_Char_ofNat(x_40);
x_42 = lean_uint32_to_uint8(x_41);
x_43 = lean_byte_array_fget(x_34, x_35);
x_44 = lean_uint8_dec_eq(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_45 = lean_mk_string_unchecked("expected: '", 11, 11);
x_46 = lean_uint8_to_nat(x_42);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_46);
x_48 = lean_string_append(x_45, x_47);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("'", 1, 1);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_32);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
if (lean_is_exclusive(x_32)) {
 lean_ctor_release(x_32, 0);
 lean_ctor_release(x_32, 1);
 x_52 = x_32;
} else {
 lean_dec_ref(x_32);
 x_52 = lean_box(0);
}
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_add(x_35, x_53);
lean_dec(x_35);
if (lean_is_scalar(x_52)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_52;
}
lean_ctor_set(x_55, 0, x_34);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_33);
return x_56;
}
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(45u);
x_9 = l_Char_ofNat(x_8);
x_10 = lean_uint32_to_uint8(x_9);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_uint8_dec_eq(x_11, x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("expected: '", 11, 11);
x_14 = lean_uint8_to_nat(x_10);
x_15 = l___private_Init_Data_Repr_0__Nat_reprFast(x_14);
x_16 = lean_string_append(x_13, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked("'", 1, 1);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_28; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_3, x_23);
lean_dec(x_3);
lean_inc(x_24);
lean_inc(x_2);
lean_ctor_set(x_1, 1, x_24);
x_28 = lean_nat_dec_lt(x_24, x_4);
lean_dec(x_4);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_24);
lean_dec(x_2);
x_29 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
uint8_t x_31; lean_object* x_32; uint32_t x_33; uint8_t x_34; uint8_t x_35; 
x_31 = lean_byte_array_fget(x_2, x_24);
x_32 = lean_unsigned_to_nat(48u);
x_33 = l_Char_ofNat(x_32);
x_34 = lean_uint32_to_uint8(x_33);
x_35 = lean_uint8_dec_le(x_34, x_31);
if (x_35 == 0)
{
lean_dec(x_24);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_36; uint32_t x_37; uint8_t x_38; uint8_t x_39; 
x_36 = lean_unsigned_to_nat(57u);
x_37 = l_Char_ofNat(x_36);
x_38 = lean_uint32_to_uint8(x_37);
x_39 = lean_uint8_dec_le(x_31, x_38);
if (x_39 == 0)
{
lean_dec(x_24);
lean_dec(x_2);
goto block_27;
}
else
{
lean_object* x_40; lean_object* x_41; uint32_t x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_1);
x_40 = lean_nat_add(x_24, x_23);
lean_dec(x_24);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_2);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Char_ofUInt8(x_31);
x_43 = lean_uint32_to_uint8(x_42);
x_44 = lean_uint8_sub(x_43, x_34);
x_45 = lean_uint8_to_nat(x_44);
x_46 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_41, x_45);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_46, 0);
x_49 = lean_ctor_get(x_46, 1);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_dec_eq(x_48, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 1);
lean_inc(x_53);
x_54 = lean_byte_array_size(x_52);
x_55 = lean_nat_dec_lt(x_53, x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_46);
lean_dec(x_48);
x_56 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
else
{
lean_object* x_58; uint32_t x_59; uint8_t x_60; uint8_t x_61; uint8_t x_62; 
x_58 = lean_unsigned_to_nat(32u);
x_59 = l_Char_ofNat(x_58);
x_60 = lean_uint32_to_uint8(x_59);
x_61 = lean_byte_array_fget(x_52, x_53);
x_62 = lean_uint8_dec_eq(x_61, x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_53);
lean_dec(x_52);
lean_free_object(x_46);
lean_dec(x_48);
x_63 = lean_mk_string_unchecked("expected: '", 11, 11);
x_64 = lean_uint8_to_nat(x_60);
x_65 = l___private_Init_Data_Repr_0__Nat_reprFast(x_64);
x_66 = lean_string_append(x_63, x_65);
lean_dec(x_65);
x_67 = lean_mk_string_unchecked("'", 1, 1);
x_68 = lean_string_append(x_66, x_67);
lean_dec(x_67);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_49);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
else
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_49);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_49, 1);
lean_dec(x_71);
x_72 = lean_ctor_get(x_49, 0);
lean_dec(x_72);
x_73 = lean_nat_add(x_53, x_23);
lean_dec(x_53);
lean_ctor_set(x_49, 1, x_73);
x_74 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_49);
if (lean_obj_tag(x_74) == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_74, 1);
x_77 = lean_nat_to_int(x_48);
x_78 = lean_int_neg(x_77);
lean_dec(x_77);
x_79 = lean_nat_abs(x_78);
lean_dec(x_78);
lean_ctor_set(x_46, 1, x_76);
lean_ctor_set(x_46, 0, x_79);
lean_ctor_set(x_74, 1, x_46);
return x_74;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_ctor_get(x_74, 0);
x_81 = lean_ctor_get(x_74, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_74);
x_82 = lean_nat_to_int(x_48);
x_83 = lean_int_neg(x_82);
lean_dec(x_82);
x_84 = lean_nat_abs(x_83);
lean_dec(x_83);
lean_ctor_set(x_46, 1, x_81);
lean_ctor_set(x_46, 0, x_84);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_80);
lean_ctor_set(x_85, 1, x_46);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_free_object(x_46);
lean_dec(x_48);
x_86 = !lean_is_exclusive(x_74);
if (x_86 == 0)
{
return x_74;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_74, 0);
x_88 = lean_ctor_get(x_74, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_74);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_49);
x_90 = lean_nat_add(x_53, x_23);
lean_dec(x_53);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_52);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_91);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
x_96 = lean_nat_to_int(x_48);
x_97 = lean_int_neg(x_96);
lean_dec(x_96);
x_98 = lean_nat_abs(x_97);
lean_dec(x_97);
lean_ctor_set(x_46, 1, x_94);
lean_ctor_set(x_46, 0, x_98);
if (lean_is_scalar(x_95)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_95;
}
lean_ctor_set(x_99, 0, x_93);
lean_ctor_set(x_99, 1, x_46);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_free_object(x_46);
lean_dec(x_48);
x_100 = lean_ctor_get(x_92, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_92, 1);
lean_inc(x_101);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_102 = x_92;
} else {
 lean_dec_ref(x_92);
 x_102 = lean_box(0);
}
if (lean_is_scalar(x_102)) {
 x_103 = lean_alloc_ctor(1, 2, 0);
} else {
 x_103 = x_102;
}
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; 
lean_free_object(x_46);
lean_dec(x_48);
x_104 = lean_mk_string_unchecked("id was 0", 8, 8);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_49);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_106 = lean_ctor_get(x_46, 0);
x_107 = lean_ctor_get(x_46, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_46);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_eq(x_106, x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; 
x_110 = lean_ctor_get(x_107, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
x_112 = lean_byte_array_size(x_110);
x_113 = lean_nat_dec_lt(x_111, x_112);
lean_dec(x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_106);
x_114 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_107);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
else
{
lean_object* x_116; uint32_t x_117; uint8_t x_118; uint8_t x_119; uint8_t x_120; 
x_116 = lean_unsigned_to_nat(32u);
x_117 = l_Char_ofNat(x_116);
x_118 = lean_uint32_to_uint8(x_117);
x_119 = lean_byte_array_fget(x_110, x_111);
x_120 = lean_uint8_dec_eq(x_119, x_118);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_106);
x_121 = lean_mk_string_unchecked("expected: '", 11, 11);
x_122 = lean_uint8_to_nat(x_118);
x_123 = l___private_Init_Data_Repr_0__Nat_reprFast(x_122);
x_124 = lean_string_append(x_121, x_123);
lean_dec(x_123);
x_125 = lean_mk_string_unchecked("'", 1, 1);
x_126 = lean_string_append(x_124, x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_127, 0, x_107);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_128 = x_107;
} else {
 lean_dec_ref(x_107);
 x_128 = lean_box(0);
}
x_129 = lean_nat_add(x_111, x_23);
lean_dec(x_111);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_110);
lean_ctor_set(x_130, 1, x_129);
x_131 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_130);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_131, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_134 = x_131;
} else {
 lean_dec_ref(x_131);
 x_134 = lean_box(0);
}
x_135 = lean_nat_to_int(x_106);
x_136 = lean_int_neg(x_135);
lean_dec(x_135);
x_137 = lean_nat_abs(x_136);
lean_dec(x_136);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_133);
if (lean_is_scalar(x_134)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_134;
}
lean_ctor_set(x_139, 0, x_132);
lean_ctor_set(x_139, 1, x_138);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_106);
x_140 = lean_ctor_get(x_131, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_131, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_142 = x_131;
} else {
 lean_dec_ref(x_131);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
else
{
lean_object* x_144; lean_object* x_145; 
lean_dec(x_106);
x_144 = lean_mk_string_unchecked("id was 0", 8, 8);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_107);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
}
block_27:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_mk_string_unchecked("digit expected", 14, 14);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_152; 
lean_dec(x_1);
x_146 = lean_unsigned_to_nat(1u);
x_147 = lean_nat_add(x_3, x_146);
lean_dec(x_3);
lean_inc(x_147);
lean_inc(x_2);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_2);
lean_ctor_set(x_148, 1, x_147);
x_152 = lean_nat_dec_lt(x_147, x_4);
lean_dec(x_4);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_147);
lean_dec(x_2);
x_153 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_148);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
else
{
uint8_t x_155; lean_object* x_156; uint32_t x_157; uint8_t x_158; uint8_t x_159; 
x_155 = lean_byte_array_fget(x_2, x_147);
x_156 = lean_unsigned_to_nat(48u);
x_157 = l_Char_ofNat(x_156);
x_158 = lean_uint32_to_uint8(x_157);
x_159 = lean_uint8_dec_le(x_158, x_155);
if (x_159 == 0)
{
lean_dec(x_147);
lean_dec(x_2);
goto block_151;
}
else
{
lean_object* x_160; uint32_t x_161; uint8_t x_162; uint8_t x_163; 
x_160 = lean_unsigned_to_nat(57u);
x_161 = l_Char_ofNat(x_160);
x_162 = lean_uint32_to_uint8(x_161);
x_163 = lean_uint8_dec_le(x_155, x_162);
if (x_163 == 0)
{
lean_dec(x_147);
lean_dec(x_2);
goto block_151;
}
else
{
lean_object* x_164; lean_object* x_165; uint32_t x_166; uint8_t x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; uint8_t x_175; 
lean_dec(x_148);
x_164 = lean_nat_add(x_147, x_146);
lean_dec(x_147);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_2);
lean_ctor_set(x_165, 1, x_164);
x_166 = l_Char_ofUInt8(x_155);
x_167 = lean_uint32_to_uint8(x_166);
x_168 = lean_uint8_sub(x_167, x_158);
x_169 = lean_uint8_to_nat(x_168);
x_170 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_165, x_169);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_173 = x_170;
} else {
 lean_dec_ref(x_170);
 x_173 = lean_box(0);
}
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_nat_dec_eq(x_171, x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; 
x_176 = lean_ctor_get(x_172, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_172, 1);
lean_inc(x_177);
x_178 = lean_byte_array_size(x_176);
x_179 = lean_nat_dec_lt(x_177, x_178);
lean_dec(x_178);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_171);
x_180 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_172);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
else
{
lean_object* x_182; uint32_t x_183; uint8_t x_184; uint8_t x_185; uint8_t x_186; 
x_182 = lean_unsigned_to_nat(32u);
x_183 = l_Char_ofNat(x_182);
x_184 = lean_uint32_to_uint8(x_183);
x_185 = lean_byte_array_fget(x_176, x_177);
x_186 = lean_uint8_dec_eq(x_185, x_184);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_177);
lean_dec(x_176);
lean_dec(x_173);
lean_dec(x_171);
x_187 = lean_mk_string_unchecked("expected: '", 11, 11);
x_188 = lean_uint8_to_nat(x_184);
x_189 = l___private_Init_Data_Repr_0__Nat_reprFast(x_188);
x_190 = lean_string_append(x_187, x_189);
lean_dec(x_189);
x_191 = lean_mk_string_unchecked("'", 1, 1);
x_192 = lean_string_append(x_190, x_191);
lean_dec(x_191);
x_193 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_193, 0, x_172);
lean_ctor_set(x_193, 1, x_192);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; 
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 lean_ctor_release(x_172, 1);
 x_194 = x_172;
} else {
 lean_dec_ref(x_172);
 x_194 = lean_box(0);
}
x_195 = lean_nat_add(x_177, x_146);
lean_dec(x_177);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_176);
lean_ctor_set(x_196, 1, x_195);
x_197 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_196);
if (lean_obj_tag(x_197) == 0)
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_198 = lean_ctor_get(x_197, 0);
lean_inc(x_198);
x_199 = lean_ctor_get(x_197, 1);
lean_inc(x_199);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_200 = x_197;
} else {
 lean_dec_ref(x_197);
 x_200 = lean_box(0);
}
x_201 = lean_nat_to_int(x_171);
x_202 = lean_int_neg(x_201);
lean_dec(x_201);
x_203 = lean_nat_abs(x_202);
lean_dec(x_202);
if (lean_is_scalar(x_173)) {
 x_204 = lean_alloc_ctor(0, 2, 0);
} else {
 x_204 = x_173;
}
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_199);
if (lean_is_scalar(x_200)) {
 x_205 = lean_alloc_ctor(0, 2, 0);
} else {
 x_205 = x_200;
}
lean_ctor_set(x_205, 0, x_198);
lean_ctor_set(x_205, 1, x_204);
return x_205;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_173);
lean_dec(x_171);
x_206 = lean_ctor_get(x_197, 0);
lean_inc(x_206);
x_207 = lean_ctor_get(x_197, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_208 = x_197;
} else {
 lean_dec_ref(x_197);
 x_208 = lean_box(0);
}
if (lean_is_scalar(x_208)) {
 x_209 = lean_alloc_ctor(1, 2, 0);
} else {
 x_209 = x_208;
}
lean_ctor_set(x_209, 0, x_206);
lean_ctor_set(x_209, 1, x_207);
return x_209;
}
}
}
}
else
{
lean_object* x_210; lean_object* x_211; 
lean_dec(x_173);
lean_dec(x_171);
x_210 = lean_mk_string_unchecked("id was 0", 8, 8);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_172);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
}
block_151:
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_mk_string_unchecked("digit expected", 14, 14);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_11; 
lean_inc(x_2);
x_11 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRes(x_2);
if (lean_obj_tag(x_11) == 0)
{
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_push(x_1, x_13);
x_1 = x_14;
x_2 = x_12;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_11, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_dec(x_11);
x_3 = x_16;
x_4 = x_17;
goto block_10;
}
}
else
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_11, 1);
lean_inc(x_18);
lean_dec(x_11);
lean_inc(x_2);
x_3 = x_2;
x_4 = x_18;
goto block_10;
}
block_10:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 1);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseClause(x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
x_9 = lean_byte_array_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_11);
return x_3;
}
else
{
lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(32u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = lean_byte_array_fget(x_7, x_8);
x_16 = lean_uint8_dec_eq(x_15, x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_17 = lean_mk_string_unchecked("expected: '", 11, 11);
x_18 = lean_uint8_to_nat(x_14);
x_19 = l___private_Init_Data_Repr_0__Nat_reprFast(x_18);
x_20 = lean_string_append(x_17, x_19);
lean_dec(x_19);
x_21 = lean_mk_string_unchecked("'", 1, 1);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 1, x_22);
return x_3;
}
else
{
uint8_t x_23; 
lean_free_object(x_3);
x_23 = !lean_is_exclusive(x_5);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_5, 1);
lean_dec(x_24);
x_25 = lean_ctor_get(x_5, 0);
lean_dec(x_25);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_8, x_26);
lean_dec(x_8);
lean_ctor_set(x_5, 1, x_27);
x_28 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_5);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
x_33 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(x_32, x_29);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
x_39 = lean_byte_array_size(x_37);
x_40 = lean_nat_dec_lt(x_38, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_1);
x_41 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_41);
return x_33;
}
else
{
lean_object* x_42; uint32_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; 
x_42 = lean_unsigned_to_nat(48u);
x_43 = l_Char_ofNat(x_42);
x_44 = lean_uint32_to_uint8(x_43);
x_45 = lean_byte_array_fget(x_37, x_38);
x_46 = lean_uint8_dec_eq(x_45, x_44);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_1);
x_47 = lean_mk_string_unchecked("expected: '", 11, 11);
x_48 = lean_uint8_to_nat(x_44);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_48);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("'", 1, 1);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_52);
return x_33;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_35);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_35, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_35, 0);
lean_dec(x_55);
x_56 = lean_nat_add(x_38, x_26);
lean_dec(x_38);
lean_ctor_set(x_35, 1, x_56);
x_57 = lean_array_get_size(x_6);
x_58 = lean_nat_dec_eq(x_57, x_31);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_array_get_size(x_36);
x_60 = lean_nat_dec_eq(x_59, x_31);
lean_dec(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_62 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_62, 0, x_1);
lean_ctor_set(x_62, 1, x_6);
lean_ctor_set(x_62, 2, x_61);
lean_ctor_set(x_62, 3, x_30);
lean_ctor_set(x_62, 4, x_36);
lean_ctor_set(x_33, 1, x_62);
return x_33;
}
else
{
lean_object* x_63; 
lean_dec(x_36);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_6);
lean_ctor_set(x_63, 2, x_30);
lean_ctor_set(x_33, 1, x_63);
return x_33;
}
}
else
{
lean_object* x_64; uint8_t x_65; 
lean_dec(x_6);
x_64 = lean_array_get_size(x_36);
lean_dec(x_36);
x_65 = lean_nat_dec_eq(x_64, x_31);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_30);
lean_dec(x_1);
x_66 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_66);
return x_33;
}
else
{
lean_object* x_67; 
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_30);
lean_ctor_set(x_33, 1, x_67);
return x_33;
}
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
lean_dec(x_35);
x_68 = lean_nat_add(x_38, x_26);
lean_dec(x_38);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_37);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_array_get_size(x_6);
x_71 = lean_nat_dec_eq(x_70, x_31);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; uint8_t x_73; 
x_72 = lean_array_get_size(x_36);
x_73 = lean_nat_dec_eq(x_72, x_31);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
x_74 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_75 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_6);
lean_ctor_set(x_75, 2, x_74);
lean_ctor_set(x_75, 3, x_30);
lean_ctor_set(x_75, 4, x_36);
lean_ctor_set(x_33, 1, x_75);
lean_ctor_set(x_33, 0, x_69);
return x_33;
}
else
{
lean_object* x_76; 
lean_dec(x_36);
x_76 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_76, 0, x_1);
lean_ctor_set(x_76, 1, x_6);
lean_ctor_set(x_76, 2, x_30);
lean_ctor_set(x_33, 1, x_76);
lean_ctor_set(x_33, 0, x_69);
return x_33;
}
}
else
{
lean_object* x_77; uint8_t x_78; 
lean_dec(x_6);
x_77 = lean_array_get_size(x_36);
lean_dec(x_36);
x_78 = lean_nat_dec_eq(x_77, x_31);
lean_dec(x_77);
if (x_78 == 0)
{
lean_object* x_79; 
lean_dec(x_30);
lean_dec(x_1);
x_79 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
lean_ctor_set_tag(x_33, 1);
lean_ctor_set(x_33, 1, x_79);
lean_ctor_set(x_33, 0, x_69);
return x_33;
}
else
{
lean_object* x_80; 
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_1);
lean_ctor_set(x_80, 1, x_30);
lean_ctor_set(x_33, 1, x_80);
lean_ctor_set(x_33, 0, x_69);
return x_33;
}
}
}
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_81 = lean_ctor_get(x_33, 0);
x_82 = lean_ctor_get(x_33, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_33);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_81, 1);
lean_inc(x_84);
x_85 = lean_byte_array_size(x_83);
x_86 = lean_nat_dec_lt(x_84, x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_1);
x_87 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_81);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
else
{
lean_object* x_89; uint32_t x_90; uint8_t x_91; uint8_t x_92; uint8_t x_93; 
x_89 = lean_unsigned_to_nat(48u);
x_90 = l_Char_ofNat(x_89);
x_91 = lean_uint32_to_uint8(x_90);
x_92 = lean_byte_array_fget(x_83, x_84);
x_93 = lean_uint8_dec_eq(x_92, x_91);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_84);
lean_dec(x_83);
lean_dec(x_82);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_1);
x_94 = lean_mk_string_unchecked("expected: '", 11, 11);
x_95 = lean_uint8_to_nat(x_91);
x_96 = l___private_Init_Data_Repr_0__Nat_reprFast(x_95);
x_97 = lean_string_append(x_94, x_96);
lean_dec(x_96);
x_98 = lean_mk_string_unchecked("'", 1, 1);
x_99 = lean_string_append(x_97, x_98);
lean_dec(x_98);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_81);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_101 = x_81;
} else {
 lean_dec_ref(x_81);
 x_101 = lean_box(0);
}
x_102 = lean_nat_add(x_84, x_26);
lean_dec(x_84);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_83);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_get_size(x_6);
x_105 = lean_nat_dec_eq(x_104, x_31);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_array_get_size(x_82);
x_107 = lean_nat_dec_eq(x_106, x_31);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_109 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_109, 0, x_1);
lean_ctor_set(x_109, 1, x_6);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_30);
lean_ctor_set(x_109, 4, x_82);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_82);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_1);
lean_ctor_set(x_111, 1, x_6);
lean_ctor_set(x_111, 2, x_30);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_103);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
lean_object* x_113; uint8_t x_114; 
lean_dec(x_6);
x_113 = lean_array_get_size(x_82);
lean_dec(x_82);
x_114 = lean_nat_dec_eq(x_113, x_31);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_30);
lean_dec(x_1);
x_115 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_103);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_1);
lean_ctor_set(x_117, 1, x_30);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_103);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_1);
x_119 = !lean_is_exclusive(x_33);
if (x_119 == 0)
{
return x_33;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_33, 0);
x_121 = lean_ctor_get(x_33, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_33);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_6);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_28);
if (x_123 == 0)
{
return x_28;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_28, 0);
x_125 = lean_ctor_get(x_28, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_28);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_5);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_add(x_8, x_127);
lean_dec(x_8);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_7);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_unsigned_to_nat(0u);
x_134 = lean_mk_empty_array_with_capacity(x_133);
x_135 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(x_134, x_131);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_138 = x_135;
} else {
 lean_dec_ref(x_135);
 x_138 = lean_box(0);
}
x_139 = lean_ctor_get(x_136, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_136, 1);
lean_inc(x_140);
x_141 = lean_byte_array_size(x_139);
x_142 = lean_nat_dec_lt(x_140, x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_1);
x_143 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_138)) {
 x_144 = lean_alloc_ctor(1, 2, 0);
} else {
 x_144 = x_138;
 lean_ctor_set_tag(x_144, 1);
}
lean_ctor_set(x_144, 0, x_136);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
else
{
lean_object* x_145; uint32_t x_146; uint8_t x_147; uint8_t x_148; uint8_t x_149; 
x_145 = lean_unsigned_to_nat(48u);
x_146 = l_Char_ofNat(x_145);
x_147 = lean_uint32_to_uint8(x_146);
x_148 = lean_byte_array_fget(x_139, x_140);
x_149 = lean_uint8_dec_eq(x_148, x_147);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_1);
x_150 = lean_mk_string_unchecked("expected: '", 11, 11);
x_151 = lean_uint8_to_nat(x_147);
x_152 = l___private_Init_Data_Repr_0__Nat_reprFast(x_151);
x_153 = lean_string_append(x_150, x_152);
lean_dec(x_152);
x_154 = lean_mk_string_unchecked("'", 1, 1);
x_155 = lean_string_append(x_153, x_154);
lean_dec(x_154);
if (lean_is_scalar(x_138)) {
 x_156 = lean_alloc_ctor(1, 2, 0);
} else {
 x_156 = x_138;
 lean_ctor_set_tag(x_156, 1);
}
lean_ctor_set(x_156, 0, x_136);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
if (lean_is_exclusive(x_136)) {
 lean_ctor_release(x_136, 0);
 lean_ctor_release(x_136, 1);
 x_157 = x_136;
} else {
 lean_dec_ref(x_136);
 x_157 = lean_box(0);
}
x_158 = lean_nat_add(x_140, x_127);
lean_dec(x_140);
if (lean_is_scalar(x_157)) {
 x_159 = lean_alloc_ctor(0, 2, 0);
} else {
 x_159 = x_157;
}
lean_ctor_set(x_159, 0, x_139);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_array_get_size(x_6);
x_161 = lean_nat_dec_eq(x_160, x_133);
lean_dec(x_160);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; 
x_162 = lean_array_get_size(x_137);
x_163 = lean_nat_dec_eq(x_162, x_133);
lean_dec(x_162);
if (x_163 == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_6);
x_165 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_165, 0, x_1);
lean_ctor_set(x_165, 1, x_6);
lean_ctor_set(x_165, 2, x_164);
lean_ctor_set(x_165, 3, x_132);
lean_ctor_set(x_165, 4, x_137);
if (lean_is_scalar(x_138)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_138;
}
lean_ctor_set(x_166, 0, x_159);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
else
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_137);
x_167 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_167, 0, x_1);
lean_ctor_set(x_167, 1, x_6);
lean_ctor_set(x_167, 2, x_132);
if (lean_is_scalar(x_138)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_138;
}
lean_ctor_set(x_168, 0, x_159);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
else
{
lean_object* x_169; uint8_t x_170; 
lean_dec(x_6);
x_169 = lean_array_get_size(x_137);
lean_dec(x_137);
x_170 = lean_nat_dec_eq(x_169, x_133);
lean_dec(x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; 
lean_dec(x_132);
lean_dec(x_1);
x_171 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
if (lean_is_scalar(x_138)) {
 x_172 = lean_alloc_ctor(1, 2, 0);
} else {
 x_172 = x_138;
 lean_ctor_set_tag(x_172, 1);
}
lean_ctor_set(x_172, 0, x_159);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
else
{
lean_object* x_173; lean_object* x_174; 
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_1);
lean_ctor_set(x_173, 1, x_132);
if (lean_is_scalar(x_138)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_138;
}
lean_ctor_set(x_174, 0, x_159);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_132);
lean_dec(x_6);
lean_dec(x_1);
x_175 = lean_ctor_get(x_135, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_135, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_177 = x_135;
} else {
 lean_dec_ref(x_135);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_6);
lean_dec(x_1);
x_179 = lean_ctor_get(x_130, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_130, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_181 = x_130;
} else {
 lean_dec_ref(x_130);
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
}
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; uint8_t x_188; 
x_183 = lean_ctor_get(x_3, 0);
x_184 = lean_ctor_get(x_3, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_3);
x_185 = lean_ctor_get(x_183, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
x_187 = lean_byte_array_size(x_185);
x_188 = lean_nat_dec_lt(x_186, x_187);
lean_dec(x_187);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
x_189 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_183);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
else
{
lean_object* x_191; uint32_t x_192; uint8_t x_193; uint8_t x_194; uint8_t x_195; 
x_191 = lean_unsigned_to_nat(32u);
x_192 = l_Char_ofNat(x_191);
x_193 = lean_uint32_to_uint8(x_192);
x_194 = lean_byte_array_fget(x_185, x_186);
x_195 = lean_uint8_dec_eq(x_194, x_193);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_1);
x_196 = lean_mk_string_unchecked("expected: '", 11, 11);
x_197 = lean_uint8_to_nat(x_193);
x_198 = l___private_Init_Data_Repr_0__Nat_reprFast(x_197);
x_199 = lean_string_append(x_196, x_198);
lean_dec(x_198);
x_200 = lean_mk_string_unchecked("'", 1, 1);
x_201 = lean_string_append(x_199, x_200);
lean_dec(x_200);
x_202 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_202, 0, x_183);
lean_ctor_set(x_202, 1, x_201);
return x_202;
}
else
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_203 = x_183;
} else {
 lean_dec_ref(x_183);
 x_203 = lean_box(0);
}
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_nat_add(x_186, x_204);
lean_dec(x_186);
if (lean_is_scalar(x_203)) {
 x_206 = lean_alloc_ctor(0, 2, 0);
} else {
 x_206 = x_203;
}
lean_ctor_set(x_206, 0, x_185);
lean_ctor_set(x_206, 1, x_205);
x_207 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseIdList(x_206);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_unsigned_to_nat(0u);
x_211 = lean_mk_empty_array_with_capacity(x_210);
x_212 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat_spec__0(x_211, x_208);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_212, 1);
lean_inc(x_214);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_215 = x_212;
} else {
 lean_dec_ref(x_212);
 x_215 = lean_box(0);
}
x_216 = lean_ctor_get(x_213, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_213, 1);
lean_inc(x_217);
x_218 = lean_byte_array_size(x_216);
x_219 = lean_nat_dec_lt(x_217, x_218);
lean_dec(x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_209);
lean_dec(x_184);
lean_dec(x_1);
x_220 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_215)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_215;
 lean_ctor_set_tag(x_221, 1);
}
lean_ctor_set(x_221, 0, x_213);
lean_ctor_set(x_221, 1, x_220);
return x_221;
}
else
{
lean_object* x_222; uint32_t x_223; uint8_t x_224; uint8_t x_225; uint8_t x_226; 
x_222 = lean_unsigned_to_nat(48u);
x_223 = l_Char_ofNat(x_222);
x_224 = lean_uint32_to_uint8(x_223);
x_225 = lean_byte_array_fget(x_216, x_217);
x_226 = lean_uint8_dec_eq(x_225, x_224);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_209);
lean_dec(x_184);
lean_dec(x_1);
x_227 = lean_mk_string_unchecked("expected: '", 11, 11);
x_228 = lean_uint8_to_nat(x_224);
x_229 = l___private_Init_Data_Repr_0__Nat_reprFast(x_228);
x_230 = lean_string_append(x_227, x_229);
lean_dec(x_229);
x_231 = lean_mk_string_unchecked("'", 1, 1);
x_232 = lean_string_append(x_230, x_231);
lean_dec(x_231);
if (lean_is_scalar(x_215)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_215;
 lean_ctor_set_tag(x_233, 1);
}
lean_ctor_set(x_233, 0, x_213);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_234 = x_213;
} else {
 lean_dec_ref(x_213);
 x_234 = lean_box(0);
}
x_235 = lean_nat_add(x_217, x_204);
lean_dec(x_217);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(0, 2, 0);
} else {
 x_236 = x_234;
}
lean_ctor_set(x_236, 0, x_216);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_array_get_size(x_184);
x_238 = lean_nat_dec_eq(x_237, x_210);
lean_dec(x_237);
if (x_238 == 0)
{
lean_object* x_239; uint8_t x_240; 
x_239 = lean_array_get_size(x_214);
x_240 = lean_nat_dec_eq(x_239, x_210);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_241 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_184);
x_242 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_242, 0, x_1);
lean_ctor_set(x_242, 1, x_184);
lean_ctor_set(x_242, 2, x_241);
lean_ctor_set(x_242, 3, x_209);
lean_ctor_set(x_242, 4, x_214);
if (lean_is_scalar(x_215)) {
 x_243 = lean_alloc_ctor(0, 2, 0);
} else {
 x_243 = x_215;
}
lean_ctor_set(x_243, 0, x_236);
lean_ctor_set(x_243, 1, x_242);
return x_243;
}
else
{
lean_object* x_244; lean_object* x_245; 
lean_dec(x_214);
x_244 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_244, 0, x_1);
lean_ctor_set(x_244, 1, x_184);
lean_ctor_set(x_244, 2, x_209);
if (lean_is_scalar(x_215)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_215;
}
lean_ctor_set(x_245, 0, x_236);
lean_ctor_set(x_245, 1, x_244);
return x_245;
}
}
else
{
lean_object* x_246; uint8_t x_247; 
lean_dec(x_184);
x_246 = lean_array_get_size(x_214);
lean_dec(x_214);
x_247 = lean_nat_dec_eq(x_246, x_210);
lean_dec(x_246);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; 
lean_dec(x_209);
lean_dec(x_1);
x_248 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
if (lean_is_scalar(x_215)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_215;
 lean_ctor_set_tag(x_249, 1);
}
lean_ctor_set(x_249, 0, x_236);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
else
{
lean_object* x_250; lean_object* x_251; 
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_1);
lean_ctor_set(x_250, 1, x_209);
if (lean_is_scalar(x_215)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_215;
}
lean_ctor_set(x_251, 0, x_236);
lean_ctor_set(x_251, 1, x_250);
return x_251;
}
}
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_209);
lean_dec(x_184);
lean_dec(x_1);
x_252 = lean_ctor_get(x_212, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_212, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_212)) {
 lean_ctor_release(x_212, 0);
 lean_ctor_release(x_212, 1);
 x_254 = x_212;
} else {
 lean_dec_ref(x_212);
 x_254 = lean_box(0);
}
if (lean_is_scalar(x_254)) {
 x_255 = lean_alloc_ctor(1, 2, 0);
} else {
 x_255 = x_254;
}
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_253);
return x_255;
}
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_184);
lean_dec(x_1);
x_256 = lean_ctor_get(x_207, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_207, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_258 = x_207;
} else {
 lean_dec_ref(x_207);
 x_258 = lean_box(0);
}
if (lean_is_scalar(x_258)) {
 x_259 = lean_alloc_ctor(1, 2, 0);
} else {
 x_259 = x_258;
}
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_257);
return x_259;
}
}
}
}
}
else
{
uint8_t x_260; 
lean_dec(x_1);
x_260 = !lean_is_exclusive(x_3);
if (x_260 == 0)
{
return x_3;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_261 = lean_ctor_get(x_3, 0);
x_262 = lean_ctor_get(x_3, 1);
lean_inc(x_262);
lean_inc(x_261);
lean_dec(x_3);
x_263 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
return x_263;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_byte_array_size(x_5);
x_8 = lean_nat_dec_lt(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_10 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; uint8_t x_15; 
x_11 = lean_byte_array_fget(x_5, x_6);
x_12 = lean_unsigned_to_nat(48u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_to_uint8(x_13);
x_15 = lean_uint8_dec_le(x_14, x_11);
if (x_15 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; uint8_t x_19; 
x_16 = lean_unsigned_to_nat(57u);
x_17 = l_Char_ofNat(x_16);
x_18 = lean_uint32_to_uint8(x_17);
x_19 = lean_uint8_dec_le(x_11, x_18);
if (x_19 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint32_t x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_6, x_23);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_24);
x_25 = l_Char_ofUInt8(x_11);
x_26 = lean_uint32_to_uint8(x_25);
x_27 = lean_uint8_sub(x_26, x_14);
x_28 = lean_uint8_to_nat(x_27);
x_29 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_1, x_28);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_nat_dec_eq(x_31, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
x_37 = lean_byte_array_size(x_35);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
x_39 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 1, x_39);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
lean_object* x_40; uint32_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; 
x_40 = lean_unsigned_to_nat(32u);
x_41 = l_Char_ofNat(x_40);
x_42 = lean_uint32_to_uint8(x_41);
x_43 = lean_byte_array_fget(x_35, x_36);
x_44 = lean_uint8_dec_eq(x_43, x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
x_45 = lean_mk_string_unchecked("expected: '", 11, 11);
x_46 = lean_uint8_to_nat(x_42);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_46);
x_48 = lean_string_append(x_45, x_47);
lean_dec(x_47);
x_49 = lean_mk_string_unchecked("'", 1, 1);
x_50 = lean_string_append(x_48, x_49);
lean_dec(x_49);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 1, x_50);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_32);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_32, 1);
lean_dec(x_52);
x_53 = lean_ctor_get(x_32, 0);
lean_dec(x_53);
x_54 = lean_nat_add(x_36, x_23);
lean_dec(x_36);
lean_inc(x_54);
lean_inc(x_35);
lean_ctor_set(x_32, 1, x_54);
x_55 = lean_nat_dec_lt(x_54, x_37);
lean_dec(x_37);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_54);
lean_dec(x_35);
lean_dec(x_31);
x_56 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 1, x_56);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
else
{
uint8_t x_57; lean_object* x_58; uint32_t x_59; uint8_t x_60; uint8_t x_61; 
lean_free_object(x_29);
x_57 = lean_byte_array_fget(x_35, x_54);
lean_dec(x_54);
lean_dec(x_35);
x_58 = lean_unsigned_to_nat(100u);
x_59 = l_Char_ofNat(x_58);
x_60 = lean_uint32_to_uint8(x_59);
x_61 = lean_uint8_dec_eq(x_57, x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(x_31, x_32);
return x_62;
}
else
{
lean_object* x_63; 
lean_dec(x_31);
x_63 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(x_32);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
lean_dec(x_32);
x_64 = lean_nat_add(x_36, x_23);
lean_dec(x_36);
lean_inc(x_64);
lean_inc(x_35);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_35);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_nat_dec_lt(x_64, x_37);
lean_dec(x_37);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_64);
lean_dec(x_35);
lean_dec(x_31);
x_67 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 1, x_67);
lean_ctor_set(x_29, 0, x_65);
return x_29;
}
else
{
uint8_t x_68; lean_object* x_69; uint32_t x_70; uint8_t x_71; uint8_t x_72; 
lean_free_object(x_29);
x_68 = lean_byte_array_fget(x_35, x_64);
lean_dec(x_64);
lean_dec(x_35);
x_69 = lean_unsigned_to_nat(100u);
x_70 = l_Char_ofNat(x_69);
x_71 = lean_uint32_to_uint8(x_70);
x_72 = lean_uint8_dec_eq(x_68, x_71);
if (x_72 == 0)
{
lean_object* x_73; 
x_73 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(x_31, x_65);
return x_73;
}
else
{
lean_object* x_74; 
lean_dec(x_31);
x_74 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(x_65);
return x_74;
}
}
}
}
}
}
else
{
lean_object* x_75; 
lean_dec(x_31);
x_75 = lean_mk_string_unchecked("id was 0", 8, 8);
lean_ctor_set_tag(x_29, 1);
lean_ctor_set(x_29, 1, x_75);
lean_ctor_set(x_29, 0, x_32);
return x_29;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_29, 0);
x_77 = lean_ctor_get(x_29, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_29);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_76, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
x_82 = lean_byte_array_size(x_80);
x_83 = lean_nat_dec_lt(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_76);
x_84 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_77);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
else
{
lean_object* x_86; uint32_t x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_86 = lean_unsigned_to_nat(32u);
x_87 = l_Char_ofNat(x_86);
x_88 = lean_uint32_to_uint8(x_87);
x_89 = lean_byte_array_fget(x_80, x_81);
x_90 = lean_uint8_dec_eq(x_89, x_88);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_82);
lean_dec(x_81);
lean_dec(x_80);
lean_dec(x_76);
x_91 = lean_mk_string_unchecked("expected: '", 11, 11);
x_92 = lean_uint8_to_nat(x_88);
x_93 = l___private_Init_Data_Repr_0__Nat_reprFast(x_92);
x_94 = lean_string_append(x_91, x_93);
lean_dec(x_93);
x_95 = lean_mk_string_unchecked("'", 1, 1);
x_96 = lean_string_append(x_94, x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_77);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; uint8_t x_101; 
if (lean_is_exclusive(x_77)) {
 lean_ctor_release(x_77, 0);
 lean_ctor_release(x_77, 1);
 x_98 = x_77;
} else {
 lean_dec_ref(x_77);
 x_98 = lean_box(0);
}
x_99 = lean_nat_add(x_81, x_23);
lean_dec(x_81);
lean_inc(x_99);
lean_inc(x_80);
if (lean_is_scalar(x_98)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_98;
}
lean_ctor_set(x_100, 0, x_80);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_nat_dec_lt(x_99, x_82);
lean_dec(x_82);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
lean_dec(x_99);
lean_dec(x_80);
lean_dec(x_76);
x_102 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_100);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
else
{
uint8_t x_104; lean_object* x_105; uint32_t x_106; uint8_t x_107; uint8_t x_108; 
x_104 = lean_byte_array_fget(x_80, x_99);
lean_dec(x_99);
lean_dec(x_80);
x_105 = lean_unsigned_to_nat(100u);
x_106 = l_Char_ofNat(x_105);
x_107 = lean_uint32_to_uint8(x_106);
x_108 = lean_uint8_dec_eq(x_104, x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(x_76, x_100);
return x_109;
}
else
{
lean_object* x_110; 
lean_dec(x_76);
x_110 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(x_100);
return x_110;
}
}
}
}
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_76);
x_111 = lean_mk_string_unchecked("id was 0", 8, 8);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_77);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; uint32_t x_116; uint8_t x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_1);
x_113 = lean_unsigned_to_nat(1u);
x_114 = lean_nat_add(x_6, x_113);
lean_dec(x_6);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_5);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Char_ofUInt8(x_11);
x_117 = lean_uint32_to_uint8(x_116);
x_118 = lean_uint8_sub(x_117, x_14);
x_119 = lean_uint8_to_nat(x_118);
x_120 = l___private_Std_Internal_Parsec_ByteArray_0__Std_Internal_Parsec_ByteArray_digitsCore_go(x_115, x_119);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_123 = x_120;
} else {
 lean_dec_ref(x_120);
 x_123 = lean_box(0);
}
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_nat_dec_eq(x_121, x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_126 = lean_ctor_get(x_122, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_122, 1);
lean_inc(x_127);
x_128 = lean_byte_array_size(x_126);
x_129 = lean_nat_dec_lt(x_127, x_128);
if (x_129 == 0)
{
lean_object* x_130; lean_object* x_131; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_121);
x_130 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_123)) {
 x_131 = lean_alloc_ctor(1, 2, 0);
} else {
 x_131 = x_123;
 lean_ctor_set_tag(x_131, 1);
}
lean_ctor_set(x_131, 0, x_122);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
else
{
lean_object* x_132; uint32_t x_133; uint8_t x_134; uint8_t x_135; uint8_t x_136; 
x_132 = lean_unsigned_to_nat(32u);
x_133 = l_Char_ofNat(x_132);
x_134 = lean_uint32_to_uint8(x_133);
x_135 = lean_byte_array_fget(x_126, x_127);
x_136 = lean_uint8_dec_eq(x_135, x_134);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_dec(x_128);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_121);
x_137 = lean_mk_string_unchecked("expected: '", 11, 11);
x_138 = lean_uint8_to_nat(x_134);
x_139 = l___private_Init_Data_Repr_0__Nat_reprFast(x_138);
x_140 = lean_string_append(x_137, x_139);
lean_dec(x_139);
x_141 = lean_mk_string_unchecked("'", 1, 1);
x_142 = lean_string_append(x_140, x_141);
lean_dec(x_141);
if (lean_is_scalar(x_123)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_123;
 lean_ctor_set_tag(x_143, 1);
}
lean_ctor_set(x_143, 0, x_122);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_144 = x_122;
} else {
 lean_dec_ref(x_122);
 x_144 = lean_box(0);
}
x_145 = lean_nat_add(x_127, x_113);
lean_dec(x_127);
lean_inc(x_145);
lean_inc(x_126);
if (lean_is_scalar(x_144)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_144;
}
lean_ctor_set(x_146, 0, x_126);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_nat_dec_lt(x_145, x_128);
lean_dec(x_128);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
lean_dec(x_145);
lean_dec(x_126);
lean_dec(x_121);
x_148 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_123)) {
 x_149 = lean_alloc_ctor(1, 2, 0);
} else {
 x_149 = x_123;
 lean_ctor_set_tag(x_149, 1);
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
else
{
uint8_t x_150; lean_object* x_151; uint32_t x_152; uint8_t x_153; uint8_t x_154; 
lean_dec(x_123);
x_150 = lean_byte_array_fget(x_126, x_145);
lean_dec(x_145);
lean_dec(x_126);
x_151 = lean_unsigned_to_nat(100u);
x_152 = l_Char_ofNat(x_151);
x_153 = lean_uint32_to_uint8(x_152);
x_154 = lean_uint8_dec_eq(x_150, x_153);
if (x_154 == 0)
{
lean_object* x_155; 
x_155 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseRat(x_121, x_146);
return x_155;
}
else
{
lean_object* x_156; 
lean_dec(x_121);
x_156 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseDelete(x_146);
return x_156;
}
}
}
}
}
else
{
lean_object* x_157; lean_object* x_158; 
lean_dec(x_121);
x_157 = lean_mk_string_unchecked("id was 0", 8, 8);
if (lean_is_scalar(x_123)) {
 x_158 = lean_alloc_ctor(1, 2, 0);
} else {
 x_158 = x_123;
 lean_ctor_set_tag(x_158, 1);
}
lean_ctor_set(x_158, 0, x_122);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("digit expected", 14, 14);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_10; lean_object* x_11; uint8_t x_22; lean_object* x_23; uint8_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_29; lean_object* x_30; lean_object* x_44; uint8_t x_45; 
x_29 = lean_ctor_get(x_3, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_44 = lean_byte_array_size(x_29);
x_45 = lean_nat_dec_lt(x_30, x_44);
lean_dec(x_44);
if (x_45 == 0)
{
if (x_1 == 0)
{
goto block_43;
}
else
{
lean_dec(x_30);
lean_dec(x_29);
goto block_19;
}
}
else
{
if (x_1 == 0)
{
lean_dec(x_30);
lean_dec(x_29);
goto block_19;
}
else
{
goto block_43;
}
}
block_9:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(x_5);
x_7 = lean_array_push(x_2, x_6);
x_2 = x_7;
x_3 = x_4;
goto _start;
}
block_17:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
x_14 = lean_nat_dec_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_2);
return x_16;
}
}
block_19:
{
lean_object* x_18; 
x_18 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_inc(x_3);
x_10 = x_3;
x_11 = x_18;
goto block_17;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_mk_string_unchecked("condition not satisfied", 23, 23);
lean_inc(x_3);
x_10 = x_3;
x_11 = x_20;
goto block_17;
}
block_24:
{
if (x_1 == 0)
{
lean_dec(x_3);
x_4 = x_23;
x_5 = x_22;
goto block_9;
}
else
{
lean_dec(x_23);
goto block_21;
}
}
block_28:
{
if (x_27 == 0)
{
x_22 = x_25;
x_23 = x_26;
goto block_24;
}
else
{
if (x_1 == 0)
{
lean_dec(x_26);
goto block_21;
}
else
{
lean_dec(x_3);
x_4 = x_26;
x_5 = x_25;
goto block_9;
}
}
}
block_43:
{
uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint32_t x_36; uint8_t x_37; uint8_t x_38; 
x_31 = lean_byte_array_fget(x_29, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_30, x_32);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_unsigned_to_nat(10u);
x_36 = l_Char_ofNat(x_35);
x_37 = lean_uint32_to_uint8(x_36);
x_38 = lean_uint8_dec_eq(x_31, x_37);
if (x_38 == 0)
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; uint8_t x_42; 
x_39 = lean_unsigned_to_nat(13u);
x_40 = l_Char_ofNat(x_39);
x_41 = lean_uint32_to_uint8(x_40);
x_42 = lean_uint8_dec_eq(x_31, x_41);
if (x_42 == 0)
{
x_25 = x_31;
x_26 = x_34;
x_27 = x_1;
goto block_28;
}
else
{
x_25 = x_31;
x_26 = x_34;
x_27 = x_38;
goto block_28;
}
}
else
{
x_22 = x_31;
x_23 = x_34;
goto block_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_11; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
x_17 = lean_byte_array_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_2);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
uint8_t x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_byte_array_fget(x_15, x_16);
lean_dec(x_16);
lean_dec(x_15);
x_22 = lean_unsigned_to_nat(99u);
x_23 = l_Char_ofNat(x_22);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_uint8_dec_eq(x_21, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_inc(x_2);
x_26 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseAction(x_2);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_27 = x_2;
} else {
 lean_dec_ref(x_2);
 x_27 = lean_box(0);
}
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_40; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_61; uint8_t x_62; 
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_30 = x_26;
} else {
 lean_dec_ref(x_26);
 x_30 = lean_box(0);
}
x_44 = lean_ctor_get(x_28, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_28, 1);
lean_inc(x_45);
x_61 = lean_byte_array_size(x_44);
x_62 = lean_nat_dec_lt(x_45, x_61);
lean_dec(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
lean_dec(x_44);
x_63 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_46 = x_28;
x_47 = x_63;
goto block_60;
}
else
{
lean_object* x_64; uint32_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; 
x_64 = lean_unsigned_to_nat(10u);
x_65 = l_Char_ofNat(x_64);
x_66 = lean_uint32_to_uint8(x_65);
x_67 = lean_byte_array_fget(x_44, x_45);
x_68 = lean_uint8_dec_eq(x_67, x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_44);
x_69 = lean_mk_string_unchecked("expected: '", 11, 11);
x_70 = lean_uint8_to_nat(x_66);
x_71 = l___private_Init_Data_Repr_0__Nat_reprFast(x_70);
x_72 = lean_string_append(x_69, x_71);
lean_dec(x_71);
x_73 = lean_mk_string_unchecked("'", 1, 1);
x_74 = lean_string_append(x_72, x_73);
lean_dec(x_73);
x_46 = x_28;
x_47 = x_74;
goto block_60;
}
else
{
uint8_t x_75; 
lean_dec(x_27);
x_75 = !lean_is_exclusive(x_28);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_76 = lean_ctor_get(x_28, 1);
lean_dec(x_76);
x_77 = lean_ctor_get(x_28, 0);
lean_dec(x_77);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_add(x_45, x_78);
lean_dec(x_45);
lean_inc(x_79);
lean_inc(x_44);
lean_ctor_set(x_28, 1, x_79);
x_31 = x_28;
x_32 = x_44;
x_33 = x_79;
goto block_39;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_28);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_nat_add(x_45, x_80);
lean_dec(x_45);
lean_inc(x_81);
lean_inc(x_44);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_44);
lean_ctor_set(x_82, 1, x_81);
x_31 = x_82;
x_32 = x_44;
x_33 = x_81;
goto block_39;
}
}
}
block_39:
{
lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_34 = lean_array_push(x_1, x_29);
x_35 = lean_byte_array_size(x_32);
lean_dec(x_32);
x_36 = lean_nat_dec_lt(x_33, x_35);
lean_dec(x_35);
lean_dec(x_33);
if (x_36 == 0)
{
lean_object* x_37; 
if (lean_is_scalar(x_30)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_30;
}
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_34);
return x_37;
}
else
{
lean_dec(x_30);
x_1 = x_34;
x_2 = x_31;
goto _start;
}
}
block_43:
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
x_31 = x_40;
x_32 = x_41;
x_33 = x_42;
goto block_39;
}
block_60:
{
lean_object* x_48; uint8_t x_49; 
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
x_49 = lean_nat_dec_eq(x_45, x_48);
lean_dec(x_48);
lean_dec(x_45);
if (x_49 == 0)
{
lean_object* x_50; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_1);
if (lean_is_scalar(x_27)) {
 x_50 = lean_alloc_ctor(1, 2, 0);
} else {
 x_50 = x_27;
 lean_ctor_set_tag(x_50, 1);
}
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_47);
lean_dec(x_27);
x_51 = lean_mk_string_unchecked("\r\n", 2, 2);
x_52 = lean_string_to_utf8(x_51);
lean_dec(x_51);
x_53 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_52, x_46);
lean_dec(x_52);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_40 = x_54;
goto block_43;
}
else
{
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_inc(x_55);
lean_dec(x_53);
x_40 = x_55;
goto block_43;
}
else
{
uint8_t x_56; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_53);
if (x_56 == 0)
{
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 0);
x_58 = lean_ctor_get(x_53, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_53);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
}
}
else
{
uint8_t x_83; 
lean_dec(x_27);
lean_dec(x_1);
x_83 = !lean_is_exclusive(x_26);
if (x_83 == 0)
{
return x_26;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_26, 0);
x_85 = lean_ctor_get(x_26, 1);
lean_inc(x_85);
lean_inc(x_84);
lean_dec(x_26);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_84);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_unsigned_to_nat(0u);
x_88 = lean_mk_empty_array_with_capacity(x_87);
x_89 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(x_25, x_88, x_2);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_109; uint8_t x_110; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
x_109 = lean_byte_array_size(x_92);
x_110 = lean_nat_dec_lt(x_93, x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_92);
x_111 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_94 = x_90;
x_95 = x_111;
goto block_108;
}
else
{
lean_object* x_112; uint32_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; 
x_112 = lean_unsigned_to_nat(10u);
x_113 = l_Char_ofNat(x_112);
x_114 = lean_uint32_to_uint8(x_113);
x_115 = lean_byte_array_fget(x_92, x_93);
x_116 = lean_uint8_dec_eq(x_115, x_114);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_92);
x_117 = lean_mk_string_unchecked("expected: '", 11, 11);
x_118 = lean_uint8_to_nat(x_114);
x_119 = l___private_Init_Data_Repr_0__Nat_reprFast(x_118);
x_120 = lean_string_append(x_117, x_119);
lean_dec(x_119);
x_121 = lean_mk_string_unchecked("'", 1, 1);
x_122 = lean_string_append(x_120, x_121);
lean_dec(x_121);
x_94 = x_90;
x_95 = x_122;
goto block_108;
}
else
{
uint8_t x_123; 
lean_dec(x_91);
x_123 = !lean_is_exclusive(x_90);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_124 = lean_ctor_get(x_90, 1);
lean_dec(x_124);
x_125 = lean_ctor_get(x_90, 0);
lean_dec(x_125);
x_126 = lean_unsigned_to_nat(1u);
x_127 = lean_nat_add(x_93, x_126);
lean_dec(x_93);
lean_inc(x_127);
lean_inc(x_92);
lean_ctor_set(x_90, 1, x_127);
x_3 = x_90;
x_4 = x_92;
x_5 = x_127;
goto block_10;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_90);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_93, x_128);
lean_dec(x_93);
lean_inc(x_129);
lean_inc(x_92);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_92);
lean_ctor_set(x_130, 1, x_129);
x_3 = x_130;
x_4 = x_92;
x_5 = x_129;
goto block_10;
}
}
}
block_108:
{
lean_object* x_96; uint8_t x_97; 
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
x_97 = lean_nat_dec_eq(x_93, x_96);
lean_dec(x_96);
lean_dec(x_93);
if (x_97 == 0)
{
lean_object* x_98; 
lean_dec(x_1);
if (lean_is_scalar(x_91)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_91;
 lean_ctor_set_tag(x_98, 1);
}
lean_ctor_set(x_98, 0, x_94);
lean_ctor_set(x_98, 1, x_95);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_95);
lean_dec(x_91);
x_99 = lean_mk_string_unchecked("\r\n", 2, 2);
x_100 = lean_string_to_utf8(x_99);
lean_dec(x_99);
x_101 = l_Std_Internal_Parsec_ByteArray_skipBytes(x_100, x_94);
lean_dec(x_100);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
lean_dec(x_101);
x_11 = x_102;
goto block_14;
}
else
{
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_101, 0);
lean_inc(x_103);
lean_dec(x_101);
x_11 = x_103;
goto block_14;
}
else
{
uint8_t x_104; 
lean_dec(x_1);
x_104 = !lean_is_exclusive(x_101);
if (x_104 == 0)
{
return x_101;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_101, 0);
x_106 = lean_ctor_get(x_101, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_101);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_1);
x_131 = !lean_is_exclusive(x_89);
if (x_131 == 0)
{
return x_89;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_89, 0);
x_133 = lean_ctor_get(x_89, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_89);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
}
block_10:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_byte_array_size(x_4);
lean_dec(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_1);
return x_8;
}
else
{
x_2 = x_3;
goto _start;
}
}
block_14:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_3 = x_11;
x_4 = x_12;
x_5 = x_13;
goto block_10;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions_go(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseZero(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_uint8_of_nat(x_8);
x_10 = lean_byte_array_fget(x_2, x_3);
x_11 = lean_uint8_dec_eq(x_10, x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_mk_string_unchecked("expected: '", 11, 11);
x_13 = lean_uint8_to_nat(x_9);
x_14 = l___private_Init_Data_Repr_0__Nat_reprFast(x_13);
x_15 = lean_string_append(x_12, x_14);
lean_dec(x_14);
x_16 = lean_mk_string_unchecked("'", 1, 1);
x_17 = lean_string_append(x_15, x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_1);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_1, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_1, 0);
lean_dec(x_21);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_23);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(uint64_t x_1, uint64_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; uint8_t x_17; uint8_t x_51; lean_object* x_55; uint64_t x_56; uint8_t x_57; 
x_11 = lean_ctor_get(x_3, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_byte_array_fget(x_4, x_5);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_5, x_14);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_15);
x_55 = lean_unsigned_to_nat(28u);
x_56 = lean_uint64_of_nat(x_55);
x_57 = lean_uint64_dec_eq(x_2, x_56);
if (x_57 == 0)
{
x_51 = x_57;
goto block_54;
}
else
{
lean_object* x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; 
x_58 = lean_unsigned_to_nat(15u);
x_59 = lean_uint8_of_nat(x_58);
x_60 = lean_uint8_complement(x_59);
x_61 = lean_uint8_land(x_13, x_60);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_uint8_of_nat(x_62);
x_64 = lean_uint8_dec_eq(x_61, x_63);
if (x_64 == 0)
{
x_51 = x_57;
goto block_54;
}
else
{
goto block_50;
}
}
block_25:
{
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_uint64_to_nat(x_16);
x_19 = lean_nat_to_int(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_uint64_to_nat(x_16);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_int_neg(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
block_50:
{
lean_object* x_26; uint8_t x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_uint8_of_nat(x_26);
x_28 = lean_uint8_dec_eq(x_13, x_27);
if (x_28 == 0)
{
lean_object* x_29; uint8_t x_30; uint8_t x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; 
x_29 = lean_unsigned_to_nat(127u);
x_30 = lean_uint8_of_nat(x_29);
x_31 = lean_uint8_land(x_13, x_30);
x_32 = lean_uint8_to_uint64(x_31);
x_33 = lean_uint64_shift_left(x_32, x_2);
x_34 = lean_uint64_lor(x_1, x_33);
x_35 = lean_unsigned_to_nat(128u);
x_36 = lean_uint8_of_nat(x_35);
x_37 = lean_uint8_land(x_13, x_36);
x_38 = lean_uint8_dec_eq(x_37, x_27);
if (x_38 == 0)
{
lean_object* x_39; uint64_t x_40; uint64_t x_41; 
x_39 = lean_unsigned_to_nat(7u);
x_40 = lean_uint64_of_nat(x_39);
x_41 = lean_uint64_add(x_2, x_40);
x_1 = x_34;
x_2 = x_41;
goto _start;
}
else
{
uint64_t x_43; uint64_t x_44; uint64_t x_45; uint64_t x_46; uint8_t x_47; 
x_43 = lean_uint64_of_nat(x_14);
x_44 = lean_uint64_shift_right(x_34, x_43);
x_45 = lean_uint64_land(x_43, x_34);
x_46 = lean_uint64_of_nat(x_26);
x_47 = lean_uint64_dec_eq(x_45, x_46);
if (x_47 == 0)
{
x_16 = x_44;
x_17 = x_38;
goto block_25;
}
else
{
x_16 = x_44;
x_17 = x_28;
goto block_25;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_mk_string_unchecked("Invalid zero byte in literal", 28, 28);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_3);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
block_54:
{
if (x_51 == 0)
{
goto block_50;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_mk_string_unchecked("Excessive literal", 17, 17);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_3);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; uint8_t x_70; uint8_t x_104; lean_object* x_108; uint64_t x_109; uint8_t x_110; 
lean_dec(x_3);
x_65 = lean_byte_array_fget(x_4, x_5);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_nat_add(x_5, x_66);
lean_dec(x_5);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_4);
lean_ctor_set(x_68, 1, x_67);
x_108 = lean_unsigned_to_nat(28u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_dec_eq(x_2, x_109);
if (x_110 == 0)
{
x_104 = x_110;
goto block_107;
}
else
{
lean_object* x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; lean_object* x_115; uint8_t x_116; uint8_t x_117; 
x_111 = lean_unsigned_to_nat(15u);
x_112 = lean_uint8_of_nat(x_111);
x_113 = lean_uint8_complement(x_112);
x_114 = lean_uint8_land(x_65, x_113);
x_115 = lean_unsigned_to_nat(0u);
x_116 = lean_uint8_of_nat(x_115);
x_117 = lean_uint8_dec_eq(x_114, x_116);
if (x_117 == 0)
{
x_104 = x_110;
goto block_107;
}
else
{
goto block_103;
}
}
block_78:
{
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_uint64_to_nat(x_69);
x_72 = lean_nat_to_int(x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_uint64_to_nat(x_69);
x_75 = lean_nat_to_int(x_74);
x_76 = lean_int_neg(x_75);
lean_dec(x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_68);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
block_103:
{
lean_object* x_79; uint8_t x_80; uint8_t x_81; 
x_79 = lean_unsigned_to_nat(0u);
x_80 = lean_uint8_of_nat(x_79);
x_81 = lean_uint8_dec_eq(x_65, x_80);
if (x_81 == 0)
{
lean_object* x_82; uint8_t x_83; uint8_t x_84; uint64_t x_85; uint64_t x_86; uint64_t x_87; lean_object* x_88; uint8_t x_89; uint8_t x_90; uint8_t x_91; 
x_82 = lean_unsigned_to_nat(127u);
x_83 = lean_uint8_of_nat(x_82);
x_84 = lean_uint8_land(x_65, x_83);
x_85 = lean_uint8_to_uint64(x_84);
x_86 = lean_uint64_shift_left(x_85, x_2);
x_87 = lean_uint64_lor(x_1, x_86);
x_88 = lean_unsigned_to_nat(128u);
x_89 = lean_uint8_of_nat(x_88);
x_90 = lean_uint8_land(x_65, x_89);
x_91 = lean_uint8_dec_eq(x_90, x_80);
if (x_91 == 0)
{
lean_object* x_92; uint64_t x_93; uint64_t x_94; 
x_92 = lean_unsigned_to_nat(7u);
x_93 = lean_uint64_of_nat(x_92);
x_94 = lean_uint64_add(x_2, x_93);
x_1 = x_87;
x_2 = x_94;
x_3 = x_68;
goto _start;
}
else
{
uint64_t x_96; uint64_t x_97; uint64_t x_98; uint64_t x_99; uint8_t x_100; 
x_96 = lean_uint64_of_nat(x_66);
x_97 = lean_uint64_shift_right(x_87, x_96);
x_98 = lean_uint64_land(x_96, x_87);
x_99 = lean_uint64_of_nat(x_79);
x_100 = lean_uint64_dec_eq(x_98, x_99);
if (x_100 == 0)
{
x_69 = x_97;
x_70 = x_91;
goto block_78;
}
else
{
x_69 = x_97;
x_70 = x_81;
goto block_78;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_mk_string_unchecked("Invalid zero byte in literal", 28, 28);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_68);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
block_107:
{
if (x_104 == 0)
{
goto block_103;
}
else
{
lean_object* x_105; lean_object* x_106; 
x_105 = lean_mk_string_unchecked("Excessive literal", 17, 17);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_68);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_6 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit_go(x_3, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseNeg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_mk_string_unchecked("parsed non negative lit where negative was expected", 51, 51);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; 
x_9 = lean_nat_abs(x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_dec_lt(x_11, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = lean_mk_string_unchecked("parsed non negative lit where negative was expected", 51, 51);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_abs(x_11);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parsePos(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_dec_lt(x_6, x_4);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; 
x_9 = lean_nat_abs(x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_dec_lt(x_13, x_11);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_abs(x_11);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_dec_lt(x_6, x_4);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_4);
x_8 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_8);
return x_2;
}
else
{
lean_object* x_9; 
x_9 = lean_nat_abs(x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_2);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_to_int(x_12);
x_14 = lean_int_dec_lt(x_13, x_11);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_15 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_nat_abs(x_11);
lean_dec(x_11);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_2);
if (x_19 == 0)
{
return x_2;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_2);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_10 = lean_byte_array_fget(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_uint8_of_nat(x_11);
x_13 = lean_uint8_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_1);
x_14 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_2, x_16);
x_2 = x_17;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
x_6 = lean_byte_array_size(x_4);
x_7 = lean_nat_dec_lt(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
uint8_t x_10; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_10 = lean_byte_array_fget(x_4, x_5);
lean_dec(x_5);
lean_dec(x_4);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_uint8_of_nat(x_25);
x_27 = lean_uint8_land(x_26, x_10);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_uint8_of_nat(x_28);
x_30 = lean_uint8_dec_eq(x_27, x_29);
if (x_30 == 0)
{
if (x_7 == 0)
{
goto block_24;
}
else
{
lean_object* x_31; 
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_3);
lean_ctor_set(x_31, 1, x_2);
return x_31;
}
}
else
{
goto block_24;
}
block_24:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_uint8_of_nat(x_11);
x_13 = lean_uint8_dec_eq(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_1);
x_14 = lean_apply_1(x_1, x_3);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_2, x_16);
x_2 = x_17;
x_3 = x_15;
goto _start;
}
else
{
uint8_t x_19; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_3);
lean_ctor_set(x_23, 1, x_2);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseId), 1, 0);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit), 1, 0);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_38; uint8_t x_39; uint8_t x_40; lean_object* x_41; uint8_t x_42; uint8_t x_43; 
x_9 = lean_byte_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_uint8_of_nat(x_38);
x_40 = lean_uint8_land(x_39, x_9);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_uint8_of_nat(x_41);
x_43 = lean_uint8_dec_eq(x_40, x_42);
if (x_43 == 0)
{
if (x_6 == 0)
{
goto block_37;
}
else
{
lean_object* x_44; 
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_2);
lean_ctor_set(x_44, 1, x_1);
return x_44;
}
}
else
{
goto block_37;
}
block_37:
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_uint8_of_nat(x_10);
x_12 = lean_uint8_dec_eq(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_2);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
x_17 = lean_nat_to_int(x_10);
x_18 = lean_int_dec_lt(x_17, x_16);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_16);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_free_object(x_13);
x_20 = lean_nat_abs(x_16);
lean_dec(x_16);
x_21 = lean_array_push(x_1, x_20);
x_1 = x_21;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_13);
x_25 = lean_nat_to_int(x_10);
x_26 = lean_int_dec_lt(x_25, x_24);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_1);
x_27 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_nat_abs(x_24);
lean_dec(x_24);
x_30 = lean_array_push(x_1, x_29);
x_1 = x_30;
x_2 = x_23;
goto _start;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_13);
if (x_32 == 0)
{
return x_13;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_13, 0);
x_34 = lean_ctor_get(x_13, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_13);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_1);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0_spec__0(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("parsed non negative lit where negative was expected", 51, 51);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_10; 
lean_free_object(x_2);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_nat_abs(x_5);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_10, 1, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_nat_abs(x_5);
lean_dec(x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_5);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_nat_to_int(x_26);
x_28 = lean_int_dec_lt(x_25, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
lean_dec(x_25);
x_29 = lean_mk_string_unchecked("parsed non negative lit where negative was expected", 51, 51);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
else
{
lean_object* x_31; 
x_31 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_24);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_nat_abs(x_25);
lean_dec(x_25);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
if (lean_is_scalar(x_34)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_34;
}
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_25);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_40 = x_31;
} else {
 lean_dec_ref(x_31);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_2);
if (x_42 == 0)
{
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_2, 0);
x_44 = lean_ctor_get(x_2, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_2);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRatHints(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes), 1, 0);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_byte_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_uint8_of_nat(x_10);
x_12 = lean_uint8_dec_eq(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_push(x_1, x_15);
x_1 = x_16;
x_2 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0_spec__0(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_byte_array_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint8_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_9 = lean_byte_array_fget(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_uint8_of_nat(x_10);
x_12 = lean_uint8_dec_eq(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes(x_2);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_array_push(x_1, x_15);
x_1 = x_16;
x_2 = x_14;
goto _start;
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_13);
if (x_18 == 0)
{
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; 
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_1);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero_go___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2_spec__2(x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseLit(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_dec_lt(x_7, x_5);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_9);
return x_2;
}
else
{
lean_object* x_10; 
lean_free_object(x_2);
x_10 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
x_16 = lean_byte_array_size(x_14);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_18 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_18);
return x_10;
}
else
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; 
x_19 = lean_uint8_of_nat(x_6);
x_20 = lean_byte_array_fget(x_14, x_15);
x_21 = lean_uint8_dec_eq(x_20, x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_5);
x_22 = lean_mk_string_unchecked("expected: '", 11, 11);
x_23 = lean_uint8_to_nat(x_19);
x_24 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = lean_mk_string_unchecked("'", 1, 1);
x_27 = lean_string_append(x_25, x_26);
lean_dec(x_26);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 1, x_27);
return x_10;
}
else
{
uint8_t x_28; 
lean_free_object(x_10);
x_28 = !lean_is_exclusive(x_12);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_12, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_12, 0);
lean_dec(x_30);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_15, x_31);
lean_dec(x_15);
lean_ctor_set(x_12, 1, x_32);
x_33 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_12);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2(x_34);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_byte_array_size(x_40);
x_43 = lean_nat_dec_lt(x_41, x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_5);
x_44 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_44);
return x_36;
}
else
{
uint8_t x_45; uint8_t x_46; 
x_45 = lean_byte_array_fget(x_40, x_41);
x_46 = lean_uint8_dec_eq(x_45, x_19);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_5);
x_47 = lean_mk_string_unchecked("expected: '", 11, 11);
x_48 = lean_uint8_to_nat(x_19);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_48);
x_50 = lean_string_append(x_47, x_49);
lean_dec(x_49);
x_51 = lean_mk_string_unchecked("'", 1, 1);
x_52 = lean_string_append(x_50, x_51);
lean_dec(x_51);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_52);
return x_36;
}
else
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_38);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_54 = lean_ctor_get(x_38, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_38, 0);
lean_dec(x_55);
x_56 = lean_nat_abs(x_5);
lean_dec(x_5);
x_57 = lean_nat_add(x_41, x_31);
lean_dec(x_41);
lean_ctor_set(x_38, 1, x_57);
x_58 = lean_array_get_size(x_13);
x_59 = lean_nat_dec_eq(x_58, x_6);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; uint8_t x_61; 
x_60 = lean_array_get_size(x_39);
x_61 = lean_nat_dec_eq(x_60, x_6);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_63 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_13);
lean_ctor_set(x_63, 2, x_62);
lean_ctor_set(x_63, 3, x_35);
lean_ctor_set(x_63, 4, x_39);
lean_ctor_set(x_36, 1, x_63);
return x_36;
}
else
{
lean_object* x_64; 
lean_dec(x_39);
x_64 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_13);
lean_ctor_set(x_64, 2, x_35);
lean_ctor_set(x_36, 1, x_64);
return x_36;
}
}
else
{
lean_object* x_65; uint8_t x_66; 
lean_dec(x_13);
x_65 = lean_array_get_size(x_39);
lean_dec(x_39);
x_66 = lean_nat_dec_eq(x_65, x_6);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; 
lean_dec(x_56);
lean_dec(x_35);
x_67 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_67);
return x_36;
}
else
{
lean_object* x_68; 
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_56);
lean_ctor_set(x_68, 1, x_35);
lean_ctor_set(x_36, 1, x_68);
return x_36;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_dec(x_38);
x_69 = lean_nat_abs(x_5);
lean_dec(x_5);
x_70 = lean_nat_add(x_41, x_31);
lean_dec(x_41);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_40);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_get_size(x_13);
x_73 = lean_nat_dec_eq(x_72, x_6);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; uint8_t x_75; 
x_74 = lean_array_get_size(x_39);
x_75 = lean_nat_dec_eq(x_74, x_6);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_77 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_77, 0, x_69);
lean_ctor_set(x_77, 1, x_13);
lean_ctor_set(x_77, 2, x_76);
lean_ctor_set(x_77, 3, x_35);
lean_ctor_set(x_77, 4, x_39);
lean_ctor_set(x_36, 1, x_77);
lean_ctor_set(x_36, 0, x_71);
return x_36;
}
else
{
lean_object* x_78; 
lean_dec(x_39);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_69);
lean_ctor_set(x_78, 1, x_13);
lean_ctor_set(x_78, 2, x_35);
lean_ctor_set(x_36, 1, x_78);
lean_ctor_set(x_36, 0, x_71);
return x_36;
}
}
else
{
lean_object* x_79; uint8_t x_80; 
lean_dec(x_13);
x_79 = lean_array_get_size(x_39);
lean_dec(x_39);
x_80 = lean_nat_dec_eq(x_79, x_6);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; 
lean_dec(x_69);
lean_dec(x_35);
x_81 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
lean_ctor_set_tag(x_36, 1);
lean_ctor_set(x_36, 1, x_81);
lean_ctor_set(x_36, 0, x_71);
return x_36;
}
else
{
lean_object* x_82; 
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_69);
lean_ctor_set(x_82, 1, x_35);
lean_ctor_set(x_36, 1, x_82);
lean_ctor_set(x_36, 0, x_71);
return x_36;
}
}
}
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_83 = lean_ctor_get(x_36, 0);
x_84 = lean_ctor_get(x_36, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_36);
x_85 = lean_ctor_get(x_83, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
x_87 = lean_byte_array_size(x_85);
x_88 = lean_nat_dec_lt(x_86, x_87);
lean_dec(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_5);
x_89 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_83);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
else
{
uint8_t x_91; uint8_t x_92; 
x_91 = lean_byte_array_fget(x_85, x_86);
x_92 = lean_uint8_dec_eq(x_91, x_19);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_5);
x_93 = lean_mk_string_unchecked("expected: '", 11, 11);
x_94 = lean_uint8_to_nat(x_19);
x_95 = l___private_Init_Data_Repr_0__Nat_reprFast(x_94);
x_96 = lean_string_append(x_93, x_95);
lean_dec(x_95);
x_97 = lean_mk_string_unchecked("'", 1, 1);
x_98 = lean_string_append(x_96, x_97);
lean_dec(x_97);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_83);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_100 = x_83;
} else {
 lean_dec_ref(x_83);
 x_100 = lean_box(0);
}
x_101 = lean_nat_abs(x_5);
lean_dec(x_5);
x_102 = lean_nat_add(x_86, x_31);
lean_dec(x_86);
if (lean_is_scalar(x_100)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_100;
}
lean_ctor_set(x_103, 0, x_85);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_array_get_size(x_13);
x_105 = lean_nat_dec_eq(x_104, x_6);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_array_get_size(x_84);
x_107 = lean_nat_dec_eq(x_106, x_6);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_109 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_109, 0, x_101);
lean_ctor_set(x_109, 1, x_13);
lean_ctor_set(x_109, 2, x_108);
lean_ctor_set(x_109, 3, x_35);
lean_ctor_set(x_109, 4, x_84);
x_110 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_110, 0, x_103);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; 
lean_dec(x_84);
x_111 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_111, 0, x_101);
lean_ctor_set(x_111, 1, x_13);
lean_ctor_set(x_111, 2, x_35);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_103);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
lean_object* x_113; uint8_t x_114; 
lean_dec(x_13);
x_113 = lean_array_get_size(x_84);
lean_dec(x_84);
x_114 = lean_nat_dec_eq(x_113, x_6);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
lean_dec(x_101);
lean_dec(x_35);
x_115 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_103);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; 
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_101);
lean_ctor_set(x_117, 1, x_35);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_103);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_35);
lean_dec(x_13);
lean_dec(x_5);
x_119 = !lean_is_exclusive(x_36);
if (x_119 == 0)
{
return x_36;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_36, 0);
x_121 = lean_ctor_get(x_36, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_36);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
else
{
uint8_t x_123; 
lean_dec(x_13);
lean_dec(x_5);
x_123 = !lean_is_exclusive(x_33);
if (x_123 == 0)
{
return x_33;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_33, 0);
x_125 = lean_ctor_get(x_33, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_33);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_12);
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_add(x_15, x_127);
lean_dec(x_15);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_14);
lean_ctor_set(x_129, 1, x_128);
x_130 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2(x_131);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_ctor_get(x_134, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_134, 1);
lean_inc(x_138);
x_139 = lean_byte_array_size(x_137);
x_140 = lean_nat_dec_lt(x_138, x_139);
lean_dec(x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_13);
lean_dec(x_5);
x_141 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_136)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_136;
 lean_ctor_set_tag(x_142, 1);
}
lean_ctor_set(x_142, 0, x_134);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
else
{
uint8_t x_143; uint8_t x_144; 
x_143 = lean_byte_array_fget(x_137, x_138);
x_144 = lean_uint8_dec_eq(x_143, x_19);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_13);
lean_dec(x_5);
x_145 = lean_mk_string_unchecked("expected: '", 11, 11);
x_146 = lean_uint8_to_nat(x_19);
x_147 = l___private_Init_Data_Repr_0__Nat_reprFast(x_146);
x_148 = lean_string_append(x_145, x_147);
lean_dec(x_147);
x_149 = lean_mk_string_unchecked("'", 1, 1);
x_150 = lean_string_append(x_148, x_149);
lean_dec(x_149);
if (lean_is_scalar(x_136)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_136;
 lean_ctor_set_tag(x_151, 1);
}
lean_ctor_set(x_151, 0, x_134);
lean_ctor_set(x_151, 1, x_150);
return x_151;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; uint8_t x_157; 
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_152 = x_134;
} else {
 lean_dec_ref(x_134);
 x_152 = lean_box(0);
}
x_153 = lean_nat_abs(x_5);
lean_dec(x_5);
x_154 = lean_nat_add(x_138, x_127);
lean_dec(x_138);
if (lean_is_scalar(x_152)) {
 x_155 = lean_alloc_ctor(0, 2, 0);
} else {
 x_155 = x_152;
}
lean_ctor_set(x_155, 0, x_137);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_array_get_size(x_13);
x_157 = lean_nat_dec_eq(x_156, x_6);
lean_dec(x_156);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
x_158 = lean_array_get_size(x_135);
x_159 = lean_nat_dec_eq(x_158, x_6);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_13);
x_161 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_161, 0, x_153);
lean_ctor_set(x_161, 1, x_13);
lean_ctor_set(x_161, 2, x_160);
lean_ctor_set(x_161, 3, x_132);
lean_ctor_set(x_161, 4, x_135);
if (lean_is_scalar(x_136)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_136;
}
lean_ctor_set(x_162, 0, x_155);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
else
{
lean_object* x_163; lean_object* x_164; 
lean_dec(x_135);
x_163 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_163, 0, x_153);
lean_ctor_set(x_163, 1, x_13);
lean_ctor_set(x_163, 2, x_132);
if (lean_is_scalar(x_136)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_136;
}
lean_ctor_set(x_164, 0, x_155);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_object* x_165; uint8_t x_166; 
lean_dec(x_13);
x_165 = lean_array_get_size(x_135);
lean_dec(x_135);
x_166 = lean_nat_dec_eq(x_165, x_6);
lean_dec(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; 
lean_dec(x_153);
lean_dec(x_132);
x_167 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
if (lean_is_scalar(x_136)) {
 x_168 = lean_alloc_ctor(1, 2, 0);
} else {
 x_168 = x_136;
 lean_ctor_set_tag(x_168, 1);
}
lean_ctor_set(x_168, 0, x_155);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
else
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_153);
lean_ctor_set(x_169, 1, x_132);
if (lean_is_scalar(x_136)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_136;
}
lean_ctor_set(x_170, 0, x_155);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_132);
lean_dec(x_13);
lean_dec(x_5);
x_171 = lean_ctor_get(x_133, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_133, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_173 = x_133;
} else {
 lean_dec_ref(x_133);
 x_173 = lean_box(0);
}
if (lean_is_scalar(x_173)) {
 x_174 = lean_alloc_ctor(1, 2, 0);
} else {
 x_174 = x_173;
}
lean_ctor_set(x_174, 0, x_171);
lean_ctor_set(x_174, 1, x_172);
return x_174;
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_13);
lean_dec(x_5);
x_175 = lean_ctor_get(x_130, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_130, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_177 = x_130;
} else {
 lean_dec_ref(x_130);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_179 = lean_ctor_get(x_10, 0);
x_180 = lean_ctor_get(x_10, 1);
lean_inc(x_180);
lean_inc(x_179);
lean_dec(x_10);
x_181 = lean_ctor_get(x_179, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_179, 1);
lean_inc(x_182);
x_183 = lean_byte_array_size(x_181);
x_184 = lean_nat_dec_lt(x_182, x_183);
lean_dec(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_5);
x_185 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_179);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
else
{
uint8_t x_187; uint8_t x_188; uint8_t x_189; 
x_187 = lean_uint8_of_nat(x_6);
x_188 = lean_byte_array_fget(x_181, x_182);
x_189 = lean_uint8_dec_eq(x_188, x_187);
if (x_189 == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_5);
x_190 = lean_mk_string_unchecked("expected: '", 11, 11);
x_191 = lean_uint8_to_nat(x_187);
x_192 = l___private_Init_Data_Repr_0__Nat_reprFast(x_191);
x_193 = lean_string_append(x_190, x_192);
lean_dec(x_192);
x_194 = lean_mk_string_unchecked("'", 1, 1);
x_195 = lean_string_append(x_193, x_194);
lean_dec(x_194);
x_196 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_196, 0, x_179);
lean_ctor_set(x_196, 1, x_195);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
if (lean_is_exclusive(x_179)) {
 lean_ctor_release(x_179, 0);
 lean_ctor_release(x_179, 1);
 x_197 = x_179;
} else {
 lean_dec_ref(x_179);
 x_197 = lean_box(0);
}
x_198 = lean_unsigned_to_nat(1u);
x_199 = lean_nat_add(x_182, x_198);
lean_dec(x_182);
if (lean_is_scalar(x_197)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_197;
}
lean_ctor_set(x_200, 0, x_181);
lean_ctor_set(x_200, 1, x_199);
x_201 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_201, 1);
lean_inc(x_203);
lean_dec(x_201);
x_204 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2(x_202);
if (lean_obj_tag(x_204) == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_207 = x_204;
} else {
 lean_dec_ref(x_204);
 x_207 = lean_box(0);
}
x_208 = lean_ctor_get(x_205, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_205, 1);
lean_inc(x_209);
x_210 = lean_byte_array_size(x_208);
x_211 = lean_nat_dec_lt(x_209, x_210);
lean_dec(x_210);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_203);
lean_dec(x_180);
lean_dec(x_5);
x_212 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_207)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_207;
 lean_ctor_set_tag(x_213, 1);
}
lean_ctor_set(x_213, 0, x_205);
lean_ctor_set(x_213, 1, x_212);
return x_213;
}
else
{
uint8_t x_214; uint8_t x_215; 
x_214 = lean_byte_array_fget(x_208, x_209);
x_215 = lean_uint8_dec_eq(x_214, x_187);
if (x_215 == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_206);
lean_dec(x_203);
lean_dec(x_180);
lean_dec(x_5);
x_216 = lean_mk_string_unchecked("expected: '", 11, 11);
x_217 = lean_uint8_to_nat(x_187);
x_218 = l___private_Init_Data_Repr_0__Nat_reprFast(x_217);
x_219 = lean_string_append(x_216, x_218);
lean_dec(x_218);
x_220 = lean_mk_string_unchecked("'", 1, 1);
x_221 = lean_string_append(x_219, x_220);
lean_dec(x_220);
if (lean_is_scalar(x_207)) {
 x_222 = lean_alloc_ctor(1, 2, 0);
} else {
 x_222 = x_207;
 lean_ctor_set_tag(x_222, 1);
}
lean_ctor_set(x_222, 0, x_205);
lean_ctor_set(x_222, 1, x_221);
return x_222;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; uint8_t x_228; 
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_223 = x_205;
} else {
 lean_dec_ref(x_205);
 x_223 = lean_box(0);
}
x_224 = lean_nat_abs(x_5);
lean_dec(x_5);
x_225 = lean_nat_add(x_209, x_198);
lean_dec(x_209);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_208);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_array_get_size(x_180);
x_228 = lean_nat_dec_eq(x_227, x_6);
lean_dec(x_227);
if (x_228 == 0)
{
lean_object* x_229; uint8_t x_230; 
x_229 = lean_array_get_size(x_206);
x_230 = lean_nat_dec_eq(x_229, x_6);
lean_dec(x_229);
if (x_230 == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_180);
x_232 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_232, 0, x_224);
lean_ctor_set(x_232, 1, x_180);
lean_ctor_set(x_232, 2, x_231);
lean_ctor_set(x_232, 3, x_203);
lean_ctor_set(x_232, 4, x_206);
if (lean_is_scalar(x_207)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_207;
}
lean_ctor_set(x_233, 0, x_226);
lean_ctor_set(x_233, 1, x_232);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_dec(x_206);
x_234 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_234, 0, x_224);
lean_ctor_set(x_234, 1, x_180);
lean_ctor_set(x_234, 2, x_203);
if (lean_is_scalar(x_207)) {
 x_235 = lean_alloc_ctor(0, 2, 0);
} else {
 x_235 = x_207;
}
lean_ctor_set(x_235, 0, x_226);
lean_ctor_set(x_235, 1, x_234);
return x_235;
}
}
else
{
lean_object* x_236; uint8_t x_237; 
lean_dec(x_180);
x_236 = lean_array_get_size(x_206);
lean_dec(x_206);
x_237 = lean_nat_dec_eq(x_236, x_6);
lean_dec(x_236);
if (x_237 == 0)
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_224);
lean_dec(x_203);
x_238 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
if (lean_is_scalar(x_207)) {
 x_239 = lean_alloc_ctor(1, 2, 0);
} else {
 x_239 = x_207;
 lean_ctor_set_tag(x_239, 1);
}
lean_ctor_set(x_239, 0, x_226);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
else
{
lean_object* x_240; lean_object* x_241; 
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_224);
lean_ctor_set(x_240, 1, x_203);
if (lean_is_scalar(x_207)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_207;
}
lean_ctor_set(x_241, 0, x_226);
lean_ctor_set(x_241, 1, x_240);
return x_241;
}
}
}
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
lean_dec(x_203);
lean_dec(x_180);
lean_dec(x_5);
x_242 = lean_ctor_get(x_204, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_204, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 lean_ctor_release(x_204, 1);
 x_244 = x_204;
} else {
 lean_dec_ref(x_204);
 x_244 = lean_box(0);
}
if (lean_is_scalar(x_244)) {
 x_245 = lean_alloc_ctor(1, 2, 0);
} else {
 x_245 = x_244;
}
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
return x_245;
}
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_180);
lean_dec(x_5);
x_246 = lean_ctor_get(x_201, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_201, 1);
lean_inc(x_247);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_248 = x_201;
} else {
 lean_dec_ref(x_201);
 x_248 = lean_box(0);
}
if (lean_is_scalar(x_248)) {
 x_249 = lean_alloc_ctor(1, 2, 0);
} else {
 x_249 = x_248;
}
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
return x_249;
}
}
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_5);
x_250 = !lean_is_exclusive(x_10);
if (x_250 == 0)
{
return x_10;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_10, 0);
x_252 = lean_ctor_get(x_10, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_10);
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
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_254 = lean_ctor_get(x_2, 0);
x_255 = lean_ctor_get(x_2, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_2);
x_256 = lean_unsigned_to_nat(0u);
x_257 = lean_nat_to_int(x_256);
x_258 = lean_int_dec_lt(x_257, x_255);
lean_dec(x_257);
if (x_258 == 0)
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_255);
x_259 = lean_mk_string_unchecked("parsed non positive lit where positive was expected", 51, 51);
x_260 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_260, 0, x_254);
lean_ctor_set(x_260, 1, x_259);
return x_260;
}
else
{
lean_object* x_261; 
x_261 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__0(x_254);
if (lean_obj_tag(x_261) == 0)
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; 
x_262 = lean_ctor_get(x_261, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_264 = x_261;
} else {
 lean_dec_ref(x_261);
 x_264 = lean_box(0);
}
x_265 = lean_ctor_get(x_262, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_262, 1);
lean_inc(x_266);
x_267 = lean_byte_array_size(x_265);
x_268 = lean_nat_dec_lt(x_266, x_267);
lean_dec(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_255);
x_269 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_264)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_264;
 lean_ctor_set_tag(x_270, 1);
}
lean_ctor_set(x_270, 0, x_262);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
else
{
uint8_t x_271; uint8_t x_272; uint8_t x_273; 
x_271 = lean_uint8_of_nat(x_256);
x_272 = lean_byte_array_fget(x_265, x_266);
x_273 = lean_uint8_dec_eq(x_272, x_271);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_266);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_255);
x_274 = lean_mk_string_unchecked("expected: '", 11, 11);
x_275 = lean_uint8_to_nat(x_271);
x_276 = l___private_Init_Data_Repr_0__Nat_reprFast(x_275);
x_277 = lean_string_append(x_274, x_276);
lean_dec(x_276);
x_278 = lean_mk_string_unchecked("'", 1, 1);
x_279 = lean_string_append(x_277, x_278);
lean_dec(x_278);
if (lean_is_scalar(x_264)) {
 x_280 = lean_alloc_ctor(1, 2, 0);
} else {
 x_280 = x_264;
 lean_ctor_set_tag(x_280, 1);
}
lean_ctor_set(x_280, 0, x_262);
lean_ctor_set(x_280, 1, x_279);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
lean_dec(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_281 = x_262;
} else {
 lean_dec_ref(x_262);
 x_281 = lean_box(0);
}
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_nat_add(x_266, x_282);
lean_dec(x_266);
if (lean_is_scalar(x_281)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_281;
}
lean_ctor_set(x_284, 0, x_265);
lean_ctor_set(x_284, 1, x_283);
x_285 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_284);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd_spec__2(x_286);
if (lean_obj_tag(x_288) == 0)
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; uint8_t x_295; 
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_291 = x_288;
} else {
 lean_dec_ref(x_288);
 x_291 = lean_box(0);
}
x_292 = lean_ctor_get(x_289, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_289, 1);
lean_inc(x_293);
x_294 = lean_byte_array_size(x_292);
x_295 = lean_nat_dec_lt(x_293, x_294);
lean_dec(x_294);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; 
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_290);
lean_dec(x_287);
lean_dec(x_263);
lean_dec(x_255);
x_296 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
if (lean_is_scalar(x_291)) {
 x_297 = lean_alloc_ctor(1, 2, 0);
} else {
 x_297 = x_291;
 lean_ctor_set_tag(x_297, 1);
}
lean_ctor_set(x_297, 0, x_289);
lean_ctor_set(x_297, 1, x_296);
return x_297;
}
else
{
uint8_t x_298; uint8_t x_299; 
x_298 = lean_byte_array_fget(x_292, x_293);
x_299 = lean_uint8_dec_eq(x_298, x_271);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_293);
lean_dec(x_292);
lean_dec(x_290);
lean_dec(x_287);
lean_dec(x_263);
lean_dec(x_255);
x_300 = lean_mk_string_unchecked("expected: '", 11, 11);
x_301 = lean_uint8_to_nat(x_271);
x_302 = l___private_Init_Data_Repr_0__Nat_reprFast(x_301);
x_303 = lean_string_append(x_300, x_302);
lean_dec(x_302);
x_304 = lean_mk_string_unchecked("'", 1, 1);
x_305 = lean_string_append(x_303, x_304);
lean_dec(x_304);
if (lean_is_scalar(x_291)) {
 x_306 = lean_alloc_ctor(1, 2, 0);
} else {
 x_306 = x_291;
 lean_ctor_set_tag(x_306, 1);
}
lean_ctor_set(x_306, 0, x_289);
lean_ctor_set(x_306, 1, x_305);
return x_306;
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_307 = x_289;
} else {
 lean_dec_ref(x_289);
 x_307 = lean_box(0);
}
x_308 = lean_nat_abs(x_255);
lean_dec(x_255);
x_309 = lean_nat_add(x_293, x_282);
lean_dec(x_293);
if (lean_is_scalar(x_307)) {
 x_310 = lean_alloc_ctor(0, 2, 0);
} else {
 x_310 = x_307;
}
lean_ctor_set(x_310, 0, x_292);
lean_ctor_set(x_310, 1, x_309);
x_311 = lean_array_get_size(x_263);
x_312 = lean_nat_dec_eq(x_311, x_256);
lean_dec(x_311);
if (x_312 == 0)
{
lean_object* x_313; uint8_t x_314; 
x_313 = lean_array_get_size(x_290);
x_314 = lean_nat_dec_eq(x_313, x_256);
lean_dec(x_313);
if (x_314 == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; 
x_315 = l___private_Std_Tactic_BVDecide_LRAT_Parser_0__Std_Tactic_BVDecide_LRAT_Parser_getPivot(x_263);
x_316 = lean_alloc_ctor(2, 5, 0);
lean_ctor_set(x_316, 0, x_308);
lean_ctor_set(x_316, 1, x_263);
lean_ctor_set(x_316, 2, x_315);
lean_ctor_set(x_316, 3, x_287);
lean_ctor_set(x_316, 4, x_290);
if (lean_is_scalar(x_291)) {
 x_317 = lean_alloc_ctor(0, 2, 0);
} else {
 x_317 = x_291;
}
lean_ctor_set(x_317, 0, x_310);
lean_ctor_set(x_317, 1, x_316);
return x_317;
}
else
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_290);
x_318 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_318, 0, x_308);
lean_ctor_set(x_318, 1, x_263);
lean_ctor_set(x_318, 2, x_287);
if (lean_is_scalar(x_291)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_291;
}
lean_ctor_set(x_319, 0, x_310);
lean_ctor_set(x_319, 1, x_318);
return x_319;
}
}
else
{
lean_object* x_320; uint8_t x_321; 
lean_dec(x_263);
x_320 = lean_array_get_size(x_290);
lean_dec(x_290);
x_321 = lean_nat_dec_eq(x_320, x_256);
lean_dec(x_320);
if (x_321 == 0)
{
lean_object* x_322; lean_object* x_323; 
lean_dec(x_308);
lean_dec(x_287);
x_322 = lean_mk_string_unchecked("There cannot be any ratHints for adding the empty clause", 56, 56);
if (lean_is_scalar(x_291)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_291;
 lean_ctor_set_tag(x_323, 1);
}
lean_ctor_set(x_323, 0, x_310);
lean_ctor_set(x_323, 1, x_322);
return x_323;
}
else
{
lean_object* x_324; lean_object* x_325; 
x_324 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_324, 0, x_308);
lean_ctor_set(x_324, 1, x_287);
if (lean_is_scalar(x_291)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_291;
}
lean_ctor_set(x_325, 0, x_310);
lean_ctor_set(x_325, 1, x_324);
return x_325;
}
}
}
}
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_287);
lean_dec(x_263);
lean_dec(x_255);
x_326 = lean_ctor_get(x_288, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_288, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_288)) {
 lean_ctor_release(x_288, 0);
 lean_ctor_release(x_288, 1);
 x_328 = x_288;
} else {
 lean_dec_ref(x_288);
 x_328 = lean_box(0);
}
if (lean_is_scalar(x_328)) {
 x_329 = lean_alloc_ctor(1, 2, 0);
} else {
 x_329 = x_328;
}
lean_ctor_set(x_329, 0, x_326);
lean_ctor_set(x_329, 1, x_327);
return x_329;
}
}
else
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_dec(x_263);
lean_dec(x_255);
x_330 = lean_ctor_get(x_285, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_285, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_332 = x_285;
} else {
 lean_dec_ref(x_285);
 x_332 = lean_box(0);
}
if (lean_is_scalar(x_332)) {
 x_333 = lean_alloc_ctor(1, 2, 0);
} else {
 x_333 = x_332;
}
lean_ctor_set(x_333, 0, x_330);
lean_ctor_set(x_333, 1, x_331);
return x_333;
}
}
}
}
else
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_255);
x_334 = lean_ctor_get(x_261, 0);
lean_inc(x_334);
x_335 = lean_ctor_get(x_261, 1);
lean_inc(x_335);
if (lean_is_exclusive(x_261)) {
 lean_ctor_release(x_261, 0);
 lean_ctor_release(x_261, 1);
 x_336 = x_261;
} else {
 lean_dec_ref(x_261);
 x_336 = lean_box(0);
}
if (lean_is_scalar(x_336)) {
 x_337 = lean_alloc_ctor(1, 2, 0);
} else {
 x_337 = x_336;
}
lean_ctor_set(x_337, 0, x_334);
lean_ctor_set(x_337, 1, x_335);
return x_337;
}
}
}
}
else
{
uint8_t x_338; 
x_338 = !lean_is_exclusive(x_2);
if (x_338 == 0)
{
return x_2;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_2, 0);
x_340 = lean_ctor_get(x_2, 1);
lean_inc(x_340);
lean_inc(x_339);
lean_dec(x_2);
x_341 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_341, 0, x_339);
lean_ctor_set(x_341, 1, x_340);
return x_341;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_manyTillNegOrZero___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseRes_spec__0(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
x_8 = lean_byte_array_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_10 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_10);
return x_2;
}
else
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_uint8_of_nat(x_11);
x_13 = lean_byte_array_fget(x_6, x_7);
x_14 = lean_uint8_dec_eq(x_13, x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_mk_string_unchecked("expected: '", 11, 11);
x_16 = lean_uint8_to_nat(x_12);
x_17 = l___private_Init_Data_Repr_0__Nat_reprFast(x_16);
x_18 = lean_string_append(x_15, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("'", 1, 1);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 1, x_20);
return x_2;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_4);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_4, 1);
lean_dec(x_22);
x_23 = lean_ctor_get(x_4, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_7, x_24);
lean_dec(x_7);
lean_ctor_set(x_4, 1, x_25);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_5);
lean_ctor_set(x_2, 1, x_26);
return x_2;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_4);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_7, x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_2, 1, x_30);
lean_ctor_set(x_2, 0, x_29);
return x_2;
}
}
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_2);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_byte_array_size(x_33);
x_36 = lean_nat_dec_lt(x_34, x_35);
lean_dec(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_37 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_31);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
else
{
lean_object* x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; 
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_uint8_of_nat(x_39);
x_41 = lean_byte_array_fget(x_33, x_34);
x_42 = lean_uint8_dec_eq(x_41, x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
x_43 = lean_mk_string_unchecked("expected: '", 11, 11);
x_44 = lean_uint8_to_nat(x_40);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
x_46 = lean_string_append(x_43, x_45);
lean_dec(x_45);
x_47 = lean_mk_string_unchecked("'", 1, 1);
x_48 = lean_string_append(x_46, x_47);
lean_dec(x_47);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_31);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_50 = x_31;
} else {
 lean_dec_ref(x_31);
 x_50 = lean_box(0);
}
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_nat_add(x_34, x_51);
lean_dec(x_34);
if (lean_is_scalar(x_50)) {
 x_53 = lean_alloc_ctor(0, 2, 0);
} else {
 x_53 = x_50;
}
lean_ctor_set(x_53, 0, x_33);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_32);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
return x_55;
}
}
}
}
else
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_2);
if (x_56 == 0)
{
return x_2;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_2, 0);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_2);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_4 = lean_byte_array_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; uint8_t x_17; 
x_9 = lean_ctor_get(x_1, 1);
lean_dec(x_9);
x_10 = lean_ctor_get(x_1, 0);
lean_dec(x_10);
x_11 = lean_byte_array_fget(x_2, x_3);
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_add(x_3, x_12);
lean_dec(x_3);
lean_ctor_set(x_1, 1, x_13);
x_14 = lean_unsigned_to_nat(97u);
x_15 = l_Char_ofNat(x_14);
x_16 = lean_uint32_to_uint8(x_15);
x_17 = lean_uint8_dec_eq(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(100u);
x_19 = l_Char_ofNat(x_18);
x_20 = lean_uint32_to_uint8(x_19);
x_21 = lean_uint8_dec_eq(x_11, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_mk_string_unchecked("Expected a or d got: ", 21, 21);
x_23 = lean_uint8_to_nat(x_11);
x_24 = l___private_Init_Data_Repr_0__Nat_reprFast(x_23);
x_25 = lean_string_append(x_22, x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
else
{
lean_object* x_27; 
x_27 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(x_1);
return x_27;
}
}
else
{
lean_object* x_28; 
x_28 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(x_1);
return x_28;
}
}
else
{
uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint32_t x_34; uint8_t x_35; uint8_t x_36; 
lean_dec(x_1);
x_29 = lean_byte_array_fget(x_2, x_3);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_add(x_3, x_30);
lean_dec(x_3);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_unsigned_to_nat(97u);
x_34 = l_Char_ofNat(x_33);
x_35 = lean_uint32_to_uint8(x_34);
x_36 = lean_uint8_dec_eq(x_29, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint32_t x_38; uint8_t x_39; uint8_t x_40; 
x_37 = lean_unsigned_to_nat(100u);
x_38 = l_Char_ofNat(x_37);
x_39 = lean_uint32_to_uint8(x_38);
x_40 = lean_uint8_dec_eq(x_29, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_mk_string_unchecked("Expected a or d got: ", 21, 21);
x_42 = lean_uint8_to_nat(x_29);
x_43 = l___private_Init_Data_Repr_0__Nat_reprFast(x_42);
x_44 = lean_string_append(x_41, x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
else
{
lean_object* x_46; 
x_46 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseDelete(x_32);
return x_46;
}
}
else
{
lean_object* x_47; 
x_47 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction_parseAdd(x_32);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_2);
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseAction(x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_5);
x_1 = x_6;
x_2 = x_4;
goto _start;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_ctor_get(x_3, 1);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_dec(x_1);
return x_3;
}
else
{
lean_dec(x_10);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_3, 0);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_3);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
else
{
lean_object* x_20; 
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_14);
lean_ctor_set(x_20, 1, x_1);
return x_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = l_Std_Internal_Parsec_manyCore___at___Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions_spec__0(x_3, x_1);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_byte_array_size(x_6);
lean_dec(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
lean_dec(x_7);
if (x_9 == 0)
{
lean_dec(x_5);
return x_4;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_4);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_4, 1);
lean_dec(x_11);
x_12 = lean_ctor_get(x_4, 0);
lean_dec(x_12);
x_13 = lean_mk_string_unchecked("expected end of input", 21, 21);
lean_ctor_set_tag(x_4, 1);
lean_ctor_set(x_4, 1, x_13);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
x_14 = lean_mk_string_unchecked("expected end of input", 21, 21);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_5);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_Parser_parseActions(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_byte_array_size(x_6);
x_9 = lean_nat_dec_lt(x_7, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_10 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; uint8_t x_16; 
x_12 = lean_byte_array_fget(x_6, x_7);
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(97u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_uint32_to_uint8(x_14);
x_16 = lean_uint8_dec_eq(x_12, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; uint8_t x_20; 
x_17 = lean_unsigned_to_nat(100u);
x_18 = l_Char_ofNat(x_17);
x_19 = lean_uint32_to_uint8(x_18);
x_20 = lean_uint8_dec_eq(x_12, x_19);
x_2 = x_20;
goto block_5;
}
else
{
x_2 = x_16;
goto block_5;
}
}
block_5:
{
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_Parser_Text_parseActions(x_1);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_Parser_Binary_parseActions(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readBinFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
x_7 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_6, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_ctor_set_tag(x_7, 18);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set_tag(x_3, 1);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
}
else
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_7, 0);
lean_inc(x_11);
lean_dec(x_7);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
x_15 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_14, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 x_17 = x_15;
} else {
 lean_dec_ref(x_15);
 x_17 = lean_box(0);
}
if (lean_is_scalar(x_17)) {
 x_18 = lean_alloc_ctor(18, 1, 0);
} else {
 x_18 = x_17;
 lean_ctor_set_tag(x_18, 18);
}
lean_ctor_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_13);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_13);
return x_21;
}
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_3);
if (x_22 == 0)
{
return x_3;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_3, 0);
x_24 = lean_ctor_get(x_3, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_3);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_loadLRATProof___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_loadLRATProof(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_parseLRATProof(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Std_Tactic_BVDecide_LRAT_Parser_parseActions), 1, 0);
x_3 = l_Std_Internal_Parsec_ByteArray_Parser_run___redArg(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_6);
x_8 = lean_mk_string_unchecked(" ", 1, 1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_4, x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_mk_string_unchecked("-", 1, 1);
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_3);
x_5 = lean_string_append(x_2, x_4);
lean_dec(x_4);
x_6 = lean_mk_string_unchecked(" ", 1, 1);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_7, x_9);
lean_dec(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHint(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_array_uget(x_1, x_2);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_nat_to_int(x_16);
x_18 = lean_int_dec_lt(x_15, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_nat_abs(x_15);
lean_dec(x_15);
x_20 = l___private_Init_Data_Repr_0__Nat_reprFast(x_19);
x_5 = x_20;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_21 = lean_nat_abs(x_15);
lean_dec(x_15);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_sub(x_21, x_22);
lean_dec(x_21);
x_24 = lean_mk_string_unchecked("-", 1, 1);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_23, x_25);
lean_dec(x_23);
x_27 = l___private_Init_Data_Repr_0__Nat_reprFast(x_26);
x_28 = lean_string_append(x_24, x_27);
lean_dec(x_27);
x_5 = x_28;
goto block_13;
}
}
else
{
return x_4;
}
block_13:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_mk_string_unchecked(" ", 1, 1);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
x_5 = lean_mk_string_unchecked(" 0 ", 3, 3);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_3);
lean_dec(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("0", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
return x_10;
}
case 1:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 2);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_15 = lean_mk_string_unchecked(" ", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_12);
lean_dec(x_12);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("0 ", 2, 2);
x_20 = lean_string_append(x_18, x_19);
lean_dec(x_19);
x_21 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_13);
lean_dec(x_13);
x_22 = lean_string_append(x_20, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("0", 1, 1);
x_24 = lean_string_append(x_22, x_23);
lean_dec(x_23);
return x_24;
}
case 2:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 4);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l___private_Init_Data_Repr_0__Nat_reprFast(x_25);
x_30 = lean_mk_string_unchecked(" ", 1, 1);
x_31 = lean_string_append(x_29, x_30);
lean_dec(x_30);
x_32 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeClause(x_26);
lean_dec(x_26);
x_33 = lean_string_append(x_31, x_32);
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("0 ", 2, 2);
x_35 = lean_string_append(x_33, x_34);
lean_dec(x_34);
x_36 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_27);
lean_dec(x_27);
x_37 = lean_string_append(x_35, x_36);
lean_dec(x_36);
x_38 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeRatHints(x_28);
lean_dec(x_28);
x_39 = lean_string_append(x_37, x_38);
lean_dec(x_38);
x_40 = lean_mk_string_unchecked("0", 1, 1);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
return x_41;
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
lean_dec(x_1);
x_43 = lean_mk_string_unchecked("1 d ", 4, 4);
x_44 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serializeIdList(x_42);
lean_dec(x_42);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = lean_mk_string_unchecked("0", 1, 1);
x_47 = lean_string_append(x_45, x_46);
lean_dec(x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToString_serialize(x_6);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("\n", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToString_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startDelete(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(100u);
x_3 = l_Char_ofNat(x_2);
x_4 = lean_uint32_to_uint8(x_3);
x_5 = lean_byte_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(lean_object* x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; lean_object* x_10; uint64_t x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_dec_eq(x_2, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint64_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(127u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_dec_lt(x_14, x_2);
if (x_15 == 0)
{
uint8_t x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_uint64_to_uint8(x_2);
x_17 = lean_uint8_of_nat(x_13);
x_18 = lean_uint8_land(x_16, x_17);
x_3 = x_18;
goto block_9;
}
else
{
uint8_t x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_19 = lean_uint64_to_uint8(x_2);
x_20 = lean_uint8_of_nat(x_13);
x_21 = lean_uint8_land(x_19, x_20);
x_22 = lean_unsigned_to_nat(128u);
x_23 = lean_uint8_of_nat(x_22);
x_24 = lean_uint8_lor(x_21, x_23);
x_3 = x_24;
goto block_9;
}
}
else
{
return x_1;
}
block_9:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; 
x_4 = lean_byte_array_push(x_1, x_3);
x_5 = lean_unsigned_to_nat(7u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_shift_right(x_2, x_6);
x_1 = x_4;
x_2 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_ByteArray_empty;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_nat_to_int(x_20);
x_22 = lean_int_dec_lt(x_21, x_2);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_nat_abs(x_2);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_shiftl(x_23, x_24);
lean_dec(x_23);
x_26 = lean_nat_add(x_25, x_24);
lean_dec(x_25);
x_3 = x_26;
goto block_19;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_nat_abs(x_2);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_nat_shiftl(x_27, x_28);
lean_dec(x_27);
x_3 = x_29;
goto block_19;
}
block_19:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_unsigned_to_nat(64u);
x_6 = lean_nat_pow(x_4, x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_sub(x_6, x_7);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("Std.Tactic.BVDecide.LRAT.Parser", 31, 31);
x_11 = lean_mk_string_unchecked("Std.Tactic.BVDecide.LRAT.lratProofToBinary.addInt", 49, 49);
x_12 = lean_unsigned_to_nat(384u);
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_mk_string_unchecked("assertion violation: mapped ≤ (2^64 - 1) -- our parser \"only\" supports 64 bit literals\n    ", 93, 91);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt_spec__0(x_15);
return x_16;
}
else
{
uint64_t x_17; lean_object* x_18; 
x_17 = lean_uint64_of_nat(x_3);
lean_dec(x_3);
x_18 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_variableLengthEncode(x_1, x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_zeroByte(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint8_of_nat(x_2);
x_4 = lean_byte_array_push(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addNat(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_nat_to_int(x_2);
x_4 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_startAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_2 = lean_unsigned_to_nat(97u);
x_3 = l_Char_ofNat(x_2);
x_4 = lean_uint32_to_uint8(x_3);
x_5 = lean_byte_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_nat_to_int(x_6);
x_8 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_nat_to_int(x_6);
x_8 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(x_1, x_11, x_3, x_8);
return x_12;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
x_17 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_12, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
x_5 = x_17;
goto block_10;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
x_5 = x_17;
goto block_10;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_12);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_18, x_22, x_23, x_17);
lean_dec(x_18);
x_5 = x_24;
goto block_10;
}
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_neg(x_15);
lean_dec(x_15);
x_17 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_4, x_16);
lean_dec(x_16);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_12, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
x_5 = x_17;
goto block_10;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
x_5 = x_17;
goto block_10;
}
else
{
size_t x_22; size_t x_23; lean_object* x_24; 
x_22 = lean_usize_of_nat(x_12);
x_23 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_24 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_18, x_22, x_23, x_17);
lean_dec(x_18);
x_5 = x_24;
goto block_10;
}
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3_spec__3(x_1, x_8, x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_9; lean_object* x_10; uint8_t x_13; lean_object* x_14; lean_object* x_17; uint8_t x_18; 
x_17 = lean_array_get_size(x_1);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_19; 
x_19 = lean_array_fget(x_1, x_2);
switch (lean_obj_tag(x_19)) {
case 0:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint32_t x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(97u);
x_23 = l_Char_ofNat(x_22);
x_24 = lean_uint32_to_uint8(x_23);
x_25 = lean_byte_array_push(x_3, x_24);
x_26 = lean_nat_to_int(x_20);
x_27 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_25, x_26);
lean_dec(x_26);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_uint8_of_nat(x_28);
x_33 = lean_byte_array_push(x_27, x_29);
x_34 = lean_array_get_size(x_21);
x_35 = lean_nat_dec_lt(x_28, x_34);
if (x_35 == 0)
{
lean_dec(x_34);
lean_dec(x_21);
x_30 = x_33;
goto block_32;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_34, x_34);
if (x_36 == 0)
{
lean_dec(x_34);
lean_dec(x_21);
x_30 = x_33;
goto block_32;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = lean_usize_of_nat(x_28);
x_38 = lean_usize_of_nat(x_34);
lean_dec(x_34);
x_39 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_21, x_37, x_38, x_33);
lean_dec(x_21);
x_30 = x_39;
goto block_32;
}
}
block_32:
{
lean_object* x_31; 
x_31 = lean_byte_array_push(x_30, x_29);
x_4 = x_31;
goto block_8;
}
}
case 1:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint32_t x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_60; uint8_t x_61; 
x_40 = lean_ctor_get(x_19, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_19, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_19, 2);
lean_inc(x_42);
lean_dec(x_19);
x_43 = lean_unsigned_to_nat(97u);
x_44 = l_Char_ofNat(x_43);
x_45 = lean_uint32_to_uint8(x_44);
x_46 = lean_byte_array_push(x_3, x_45);
x_47 = lean_nat_to_int(x_40);
x_48 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_46, x_47);
lean_dec(x_47);
x_49 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get_size(x_41);
x_61 = lean_nat_dec_lt(x_49, x_60);
if (x_61 == 0)
{
lean_dec(x_60);
lean_dec(x_41);
x_50 = x_48;
goto block_59;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_60, x_60);
if (x_62 == 0)
{
lean_dec(x_60);
lean_dec(x_41);
x_50 = x_48;
goto block_59;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
x_63 = lean_usize_of_nat(x_49);
x_64 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_65 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(x_41, x_63, x_64, x_48);
lean_dec(x_41);
x_50 = x_65;
goto block_59;
}
}
block_59:
{
uint8_t x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_uint8_of_nat(x_49);
x_52 = lean_byte_array_push(x_50, x_51);
x_53 = lean_array_get_size(x_42);
x_54 = lean_nat_dec_lt(x_49, x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_42);
x_9 = x_51;
x_10 = x_52;
goto block_12;
}
else
{
uint8_t x_55; 
x_55 = lean_nat_dec_le(x_53, x_53);
if (x_55 == 0)
{
lean_dec(x_53);
lean_dec(x_42);
x_9 = x_51;
x_10 = x_52;
goto block_12;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = lean_usize_of_nat(x_49);
x_57 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_58 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_42, x_56, x_57, x_52);
lean_dec(x_42);
x_9 = x_51;
x_10 = x_58;
goto block_12;
}
}
}
}
case 2:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint32_t x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_86; lean_object* x_96; uint8_t x_97; 
x_66 = lean_ctor_get(x_19, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_19, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_19, 3);
lean_inc(x_68);
x_69 = lean_ctor_get(x_19, 4);
lean_inc(x_69);
lean_dec(x_19);
x_70 = lean_unsigned_to_nat(97u);
x_71 = l_Char_ofNat(x_70);
x_72 = lean_uint32_to_uint8(x_71);
x_73 = lean_byte_array_push(x_3, x_72);
x_74 = lean_nat_to_int(x_66);
x_75 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_addInt(x_73, x_74);
lean_dec(x_74);
x_76 = lean_unsigned_to_nat(0u);
x_96 = lean_array_get_size(x_67);
x_97 = lean_nat_dec_lt(x_76, x_96);
if (x_97 == 0)
{
lean_dec(x_96);
lean_dec(x_67);
x_86 = x_75;
goto block_95;
}
else
{
uint8_t x_98; 
x_98 = lean_nat_dec_le(x_96, x_96);
if (x_98 == 0)
{
lean_dec(x_96);
lean_dec(x_67);
x_86 = x_75;
goto block_95;
}
else
{
size_t x_99; size_t x_100; lean_object* x_101; 
x_99 = lean_usize_of_nat(x_76);
x_100 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_101 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(x_67, x_99, x_100, x_75);
lean_dec(x_67);
x_86 = x_101;
goto block_95;
}
}
block_85:
{
lean_object* x_79; uint8_t x_80; 
x_79 = lean_array_get_size(x_69);
x_80 = lean_nat_dec_lt(x_76, x_79);
if (x_80 == 0)
{
lean_dec(x_79);
lean_dec(x_69);
x_13 = x_77;
x_14 = x_78;
goto block_16;
}
else
{
uint8_t x_81; 
x_81 = lean_nat_dec_le(x_79, x_79);
if (x_81 == 0)
{
lean_dec(x_79);
lean_dec(x_69);
x_13 = x_77;
x_14 = x_78;
goto block_16;
}
else
{
size_t x_82; size_t x_83; lean_object* x_84; 
x_82 = lean_usize_of_nat(x_76);
x_83 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_84 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3(x_69, x_82, x_83, x_78);
lean_dec(x_69);
x_13 = x_77;
x_14 = x_84;
goto block_16;
}
}
}
block_95:
{
uint8_t x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_87 = lean_uint8_of_nat(x_76);
x_88 = lean_byte_array_push(x_86, x_87);
x_89 = lean_array_get_size(x_68);
x_90 = lean_nat_dec_lt(x_76, x_89);
if (x_90 == 0)
{
lean_dec(x_89);
lean_dec(x_68);
x_77 = x_87;
x_78 = x_88;
goto block_85;
}
else
{
uint8_t x_91; 
x_91 = lean_nat_dec_le(x_89, x_89);
if (x_91 == 0)
{
lean_dec(x_89);
lean_dec(x_68);
x_77 = x_87;
x_78 = x_88;
goto block_85;
}
else
{
size_t x_92; size_t x_93; lean_object* x_94; 
x_92 = lean_usize_of_nat(x_76);
x_93 = lean_usize_of_nat(x_89);
lean_dec(x_89);
x_94 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_68, x_92, x_93, x_88);
lean_dec(x_68);
x_77 = x_87;
x_78 = x_94;
goto block_85;
}
}
}
}
default: 
{
lean_object* x_102; lean_object* x_103; uint32_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_112; uint8_t x_113; 
x_102 = lean_ctor_get(x_19, 0);
lean_inc(x_102);
lean_dec(x_19);
x_103 = lean_unsigned_to_nat(100u);
x_104 = l_Char_ofNat(x_103);
x_105 = lean_uint32_to_uint8(x_104);
x_106 = lean_byte_array_push(x_3, x_105);
x_107 = lean_unsigned_to_nat(0u);
x_112 = lean_array_get_size(x_102);
x_113 = lean_nat_dec_lt(x_107, x_112);
if (x_113 == 0)
{
lean_dec(x_112);
lean_dec(x_102);
x_108 = x_106;
goto block_111;
}
else
{
uint8_t x_114; 
x_114 = lean_nat_dec_le(x_112, x_112);
if (x_114 == 0)
{
lean_dec(x_112);
lean_dec(x_102);
x_108 = x_106;
goto block_111;
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
x_115 = lean_usize_of_nat(x_107);
x_116 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_117 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_102, x_115, x_116, x_106);
lean_dec(x_102);
x_108 = x_117;
goto block_111;
}
}
block_111:
{
uint8_t x_109; lean_object* x_110; 
x_109 = lean_uint8_of_nat(x_107);
x_110 = lean_byte_array_push(x_108, x_109);
x_4 = x_110;
goto block_8;
}
}
}
}
block_8:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_2, x_5);
lean_dec(x_2);
x_2 = x_6;
x_3 = x_4;
goto _start;
}
block_12:
{
lean_object* x_11; 
x_11 = lean_byte_array_push(x_10, x_9);
x_4 = x_11;
goto block_8;
}
block_16:
{
lean_object* x_15; 
x_15 = lean_byte_array_push(x_14, x_13);
x_4 = x_15;
goto block_8;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Std_Tactic_BVDecide_LRAT_lratProofToBinary_go_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_array_get_size(x_1);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_shiftl(x_3, x_4);
lean_dec(x_3);
x_6 = lean_mk_empty_byte_array(x_5);
lean_dec(x_5);
x_7 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary_go(x_1, x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_lratProofToBinary___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
if (x_3 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = l_Std_Tactic_BVDecide_LRAT_lratProofToString(x_2);
x_6 = lean_string_to_utf8(x_5);
lean_dec(x_5);
x_7 = l_IO_FS_writeBinFile(x_1, x_6, x_4);
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Std_Tactic_BVDecide_LRAT_lratProofToBinary(x_2);
x_9 = l_IO_FS_writeBinFile(x_1, x_8, x_4);
lean_dec(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_LRAT_dumpLRATProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_3);
lean_dec(x_3);
x_6 = l_Std_Tactic_BVDecide_LRAT_dumpLRATProof(x_1, x_2, x_5, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Init_System_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_LRAT_Actions(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Internal_Parsec(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_LRAT_Parser(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_LRAT_Actions(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Internal_Parsec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
