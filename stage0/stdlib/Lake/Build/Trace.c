// Lean compiler output
// Module: Lake.Build.Trace
// Imports: Lake.Util.IO Lean.Data.Json
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
LEAN_EXPORT lean_object* l_Lake_MTime_instOrd;
uint8_t l_Ord_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_instToString;
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringTextFilePath;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_instToJson;
LEAN_EXPORT lean_object* l_Lake_instComputeHashFilePathIO;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofNat(lean_object*);
lean_object* l_Std_Format_fill(lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t);
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object*, lean_object*, lean_object*, uint64_t, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t, uint64_t);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instBEq;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace____x40_Lake_Build_Trace___hyg_1359_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_io_metadata(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_ByteArray_foldlMUnsafe_fold___at___Lake_computeBinFileHash_spec__0(lean_object*, size_t, size_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashTextFilePathIO___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object*);
lean_object* l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed(lean_object*, lean_object*);
lean_object* l_Std_Format_joinSep(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil___boxed__const__1;
extern lean_object* l_IO_FS_instReprSystemTime;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object*);
lean_object* l_ByteArray_foldlMUnsafe_fold___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_instMonadLiftT(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t);
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instBEqHash;
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceList___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMin;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t, lean_object*, uint64_t);
lean_object* l_String_crlfToLf(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash____x40_Lake_Build_Trace___hyg_614_(uint64_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray___lam__0(uint64_t, uint8_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprHash;
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instNilTrace;
uint64_t lean_uint8_to_uint64(uint8_t);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashBoolId;
LEAN_EXPORT lean_object* l_Lake_Hash_instFromJson;
lean_object* l_List_foldl___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* lean_uint64_to_nat(uint64_t);
LEAN_EXPORT lean_object* l_Lake_instCheckExistsFilePath;
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instNilTrace;
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Trace_0__Lake_beqHash____x40_Lake_Build_Trace___hyg_466_(uint64_t, uint64_t);
uint8_t lean_byte_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime___boxed__const__1;
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object*, lean_object*);
uint8_t l_Ord_instDecidableRelLt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t);
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object*);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___Lake_computeBinFileHash_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace____x40_Lake_Build_Trace___hyg_1359____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashStringId;
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash____x40_Lake_Build_Trace___hyg_614____boxed(lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_0__IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3066_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashTextFilePathIO;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instMixTrace;
lean_object* l_Lean_bignumFromJson_x3f(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace___redArg____x40_Lake_Build_Trace___hyg_1359_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3124____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Build_Trace_0__Lake_decEqHash____x40_Lake_Build_Trace___hyg_524_(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_String_anyAux___at___String_toNat_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_beqHash____x40_Lake_Build_Trace___hyg_466____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceArray(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instOfNat;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t);
lean_object* l_IO_FS_readFile(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instGetMTimeFilePath;
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMax;
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instRepr;
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceList(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs___boxed(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_nil;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprBuildTrace;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_instNilTrace;
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTrace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash___redArg____x40_Lake_Build_Trace___hyg_614_(uint64_t);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace___redArg___lam__0____x40_Lake_Build_Trace___hyg_1359_(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime;
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_foldlAux___at___String_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_bignumToJson(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object*, lean_object*, uint64_t, lean_object*, lean_object*);
uint8_t lean_uint64_dec_eq(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instLT;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instMixTrace;
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath;
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_MTime_instLE;
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash;
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash___redArg____x40_Lake_Build_Trace___hyg_614____boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_System_FilePath_pathExists___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_decEqHash____x40_Lake_Build_Trace___hyg_524____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object*, lean_object*);
lean_object* l_IO_FS_readBinFile(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* lean_byte_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_instMixTrace;
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instComputeHashTextFilePathIO___lam__0(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object*);
lean_object* l_List_foldlM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_computeTrace___redArg(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lake_instCheckExistsFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_pathExists___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_apply_1(x_5, x_7);
x_9 = lean_apply_2(x_6, lean_box(0), x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_inhabitedOfNilTrace___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_inhabitedOfNilTrace___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_inhabitedOfNilTrace(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceList___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_foldl___redArg(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceList(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_foldl___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_array_get_size(x_3);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
x_14 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_9);
lean_ctor_set(x_14, 3, x_10);
lean_ctor_set(x_14, 4, x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_nat_dec_lt(x_4, x_5);
if (x_16 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_5, x_5);
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
return x_2;
}
else
{
size_t x_18; size_t x_19; lean_object* x_20; 
x_18 = lean_usize_of_nat(x_4);
x_19 = lean_usize_of_nat(x_5);
lean_dec(x_5);
x_20 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_15, x_1, x_3, x_18, x_19, x_2);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_mixTraceArray(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_mixTraceArray___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_apply_2(x_1, x_2, x_4);
x_6 = lean_apply_2(x_3, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__0), 4, 3);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_6);
lean_closure_set(x_8, 2, x_2);
x_9 = lean_apply_1(x_3, x_7);
x_10 = lean_apply_2(x_4, lean_box(0), x_9);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_10, 0, x_1);
lean_closure_set(x_10, 1, x_9);
lean_closure_set(x_10, 2, x_3);
lean_closure_set(x_10, 3, x_4);
lean_closure_set(x_10, 4, x_7);
x_11 = l_List_foldlM___redArg(x_5, x_10, x_2, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_computeListTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_6);
lean_closure_set(x_14, 3, x_8);
lean_closure_set(x_14, 4, x_11);
x_15 = l_List_foldlM___redArg(x_9, x_14, x_5, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_instMonadLiftT(lean_box(0));
x_6 = lean_alloc_closure((void*)(l_Lake_computeListTrace), 10, 9);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, lean_box(0));
lean_closure_set(x_6, 3, x_1);
lean_closure_set(x_6, 4, x_2);
lean_closure_set(x_6, 5, x_3);
lean_closure_set(x_6, 6, lean_box(0));
lean_closure_set(x_6, 7, x_5);
lean_closure_set(x_6, 8, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceListOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_instComputeTraceListOfMonad___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_6);
x_12 = lean_nat_dec_lt(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_apply_2(x_9, lean_box(0), x_2);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_11, x_11);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_apply_2(x_9, lean_box(0), x_2);
return x_15;
}
else
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_16, 0, x_1);
lean_closure_set(x_16, 1, x_9);
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_4);
lean_closure_set(x_16, 4, x_7);
x_17 = lean_usize_of_nat(x_10);
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_5, x_16, x_6, x_17, x_18, x_2);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayTrace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_10);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_17 = lean_apply_2(x_13, lean_box(0), x_5);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_15, x_15);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
x_19 = lean_apply_2(x_13, lean_box(0), x_5);
return x_19;
}
else
{
lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_20 = lean_alloc_closure((void*)(l_Lake_computeListTrace___redArg___lam__1), 7, 5);
lean_closure_set(x_20, 0, x_4);
lean_closure_set(x_20, 1, x_13);
lean_closure_set(x_20, 2, x_6);
lean_closure_set(x_20, 3, x_8);
lean_closure_set(x_20, 4, x_11);
x_21 = lean_usize_of_nat(x_14);
x_22 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_23 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_9, x_20, x_10, x_21, x_22, x_5);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_instMonadLiftT(lean_box(0));
x_6 = lean_alloc_closure((void*)(l_Lake_computeArrayTrace), 10, 9);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, lean_box(0));
lean_closure_set(x_6, 2, lean_box(0));
lean_closure_set(x_6, 3, x_1);
lean_closure_set(x_6, 4, x_2);
lean_closure_set(x_6, 5, x_3);
lean_closure_set(x_6, 6, lean_box(0));
lean_closure_set(x_6, 7, x_5);
lean_closure_set(x_6, 8, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceArrayOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_instComputeTraceArrayOfMonad___redArg(x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Trace_0__Lake_beqHash____x40_Lake_Build_Trace___hyg_466_(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_beqHash____x40_Lake_Build_Trace___hyg_466____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l___private_Lake_Build_Trace_0__Lake_beqHash____x40_Lake_Build_Trace___hyg_466_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_instBEqHash() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Trace_0__Lake_beqHash____x40_Lake_Build_Trace___hyg_466____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Build_Trace_0__Lake_decEqHash____x40_Lake_Build_Trace___hyg_524_(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_decEqHash____x40_Lake_Build_Trace___hyg_524____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l___private_Lake_Build_Trace_0__Lake_decEqHash____x40_Lake_Build_Trace___hyg_524_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqHash(uint64_t x_1, uint64_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_uint64_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqHash(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash___redArg____x40_Lake_Build_Trace___hyg_614_(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("val", 3, 3);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked(" := ", 4, 4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(7u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_uint64_to_nat(x_1);
x_13 = l___private_Init_Data_Repr_0__Nat_reprFast(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
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
x_20 = lean_mk_string_unchecked(" }", 2, 2);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_to_int(x_21);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_2);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_20);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_unbox(x_16);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
return x_28;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash____x40_Lake_Build_Trace___hyg_614_(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Trace_0__Lake_reprHash___redArg____x40_Lake_Build_Trace___hyg_614_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash___redArg____x40_Lake_Build_Trace___hyg_614____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l___private_Lake_Build_Trace_0__Lake_reprHash___redArg____x40_Lake_Build_Trace___hyg_614_(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprHash____x40_Lake_Build_Trace___hyg_614____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Build_Trace_0__Lake_reprHash____x40_Lake_Build_Trace___hyg_614_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprHash() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Trace_0__Lake_reprHash____x40_Lake_Build_Trace___hyg_614____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofNat(lean_object* x_1) {
_start:
{
uint64_t x_2; 
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofNat___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_string_utf8_byte_size(x_1);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_instDecidableEqPos(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_String_anyAux___at___String_toNat_x3f_spec__1(x_1, x_1, x_9, x_10);
lean_dec(x_9);
if (x_12 == 0)
{
goto block_8;
}
else
{
if (x_11 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
goto block_8;
}
}
}
else
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = lean_box(0);
return x_14;
}
block_8:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = l_String_foldlAux___at___String_toNat_x3f_spec__0(x_1, x_3, x_2, x_2);
lean_dec(x_3);
x_5 = lean_uint64_of_nat(x_4);
lean_dec(x_4);
x_6 = lean_box_uint64(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Hash_ofString_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lake_Hash_ofString_x3f(x_5);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = l_Lake_Hash_ofString_x3f(x_7);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_3, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_13);
return x_3;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_load_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Hash_load_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static uint64_t _init_l_Lake_Hash_nil() {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
static uint64_t _init_l_Lake_Hash_instNilTrace() {
_start:
{
uint64_t x_1; 
x_1 = l_Lake_Hash_nil;
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_mix(uint64_t x_1, uint64_t x_2) {
_start:
{
uint64_t x_3; 
x_3 = lean_uint64_mix_hash(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_mix___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox_uint64(x_2);
lean_dec(x_2);
x_5 = l_Lake_Hash_mix(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Hash_instMixTrace() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_mix___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toString___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_Hash_toString(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Hash_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_toString___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofString(lean_object* x_1) {
_start:
{
uint64_t x_2; uint64_t x_3; uint64_t x_4; 
x_2 = lean_string_hash(x_1);
x_3 = l_Lake_Hash_nil;
x_4 = lean_uint64_mix_hash(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofString___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofString(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray___lam__0(uint64_t x_1, uint8_t x_2) {
_start:
{
uint64_t x_3; uint64_t x_4; 
x_3 = lean_uint8_to_uint64(x_2);
x_4 = lean_uint64_mix_hash(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofByteArray(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_2 = lean_unsigned_to_nat(7u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_byte_array_size(x_1);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_5);
lean_ctor_set(x_12, 1, x_6);
x_13 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_8);
lean_ctor_set(x_13, 3, x_9);
lean_ctor_set(x_13, 4, x_10);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
x_15 = lean_nat_dec_lt(x_3, x_4);
if (x_15 == 0)
{
uint64_t x_16; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_16 = lean_uint64_of_nat(x_2);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_4, x_4);
if (x_17 == 0)
{
uint64_t x_18; 
lean_dec(x_14);
lean_dec(x_4);
lean_dec(x_1);
x_18 = lean_uint64_of_nat(x_2);
return x_18;
}
else
{
lean_object* x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; 
x_19 = lean_alloc_closure((void*)(l_Lake_Hash_ofByteArray___lam__0___boxed), 2, 0);
x_20 = lean_uint64_of_nat(x_2);
x_21 = lean_usize_of_nat(x_3);
x_22 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_23 = lean_box_uint64(x_20);
x_24 = l_ByteArray_foldlMUnsafe_fold___redArg(x_14, x_19, x_1, x_21, x_22, x_23);
x_25 = lean_unbox_uint64(x_24);
lean_dec(x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; uint8_t x_4; uint64_t x_5; lean_object* x_6; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_Hash_ofByteArray___lam__0(x_3, x_4);
x_6 = lean_box_uint64(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofByteArray___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lake_Hash_ofByteArray(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint64_t l_Lake_Hash_ofBool(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_unsigned_to_nat(13u);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
else
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_unsigned_to_nat(11u);
x_5 = lean_uint64_of_nat(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_ofBool___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_Hash_ofBool(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_uint64_to_nat(x_1);
x_3 = l_Lean_bignumToJson(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_toJson___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_Hash_toJson(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_Hash_instToJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_toJson___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Hash_fromJson_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_bignumFromJson_x3f(x_1);
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
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_cstr_to_nat("18446744073709551616");
x_9 = lean_nat_dec_le(x_8, x_7);
lean_dec(x_8);
if (x_9 == 0)
{
uint64_t x_10; lean_object* x_11; 
x_10 = lean_uint64_of_nat(x_7);
lean_dec(x_7);
x_11 = lean_box_uint64(x_10);
lean_ctor_set(x_2, 0, x_11);
return x_2;
}
else
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 0, x_12);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_cstr_to_nat("18446744073709551616");
x_15 = lean_nat_dec_le(x_14, x_13);
lean_dec(x_14);
if (x_15 == 0)
{
uint64_t x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_uint64_of_nat(x_13);
lean_dec(x_13);
x_17 = lean_box_uint64(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_13);
x_19 = lean_mk_string_unchecked("value '{j}' is too large for `UInt64`", 37, 37);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
}
}
static lean_object* _init_l_Lake_Hash_instFromJson() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_fromJson_x3f), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instComputeTraceHashOfComputeHash___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceHashOfComputeHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_instComputeTraceHashOfComputeHash(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox_uint64(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lake_pureHash(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_apply_1(x_2, x_3);
x_5 = lean_unbox_uint64(x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = l_Lake_pureHash___redArg(x_1, x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_pureHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; 
x_4 = l_Lake_pureHash(x_1, x_2, x_3);
x_5 = lean_box_uint64(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_apply_2(x_2, lean_box(0), x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeHash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_apply_1(x_4, x_6);
x_8 = lean_apply_2(x_5, lean_box(0), x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_instComputeHashBoolId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_ofBool___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_instComputeHashStringId() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Hash_ofString___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_ByteArray_foldlMUnsafe_fold___at___Lake_computeBinFileHash_spec__0(lean_object* x_1, size_t x_2, size_t x_3, uint64_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
uint8_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_byte_array_uget(x_1, x_2);
x_7 = lean_uint8_to_uint64(x_6);
x_8 = lean_uint64_mix_hash(x_4, x_7);
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
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash(lean_object* x_1, lean_object* x_2) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_unsigned_to_nat(7u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_byte_array_size(x_5);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
uint64_t x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_5);
x_10 = lean_uint64_of_nat(x_6);
x_11 = lean_box_uint64(x_10);
lean_ctor_set(x_3, 0, x_11);
return x_3;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
uint64_t x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_5);
x_13 = lean_uint64_of_nat(x_6);
x_14 = lean_box_uint64(x_13);
lean_ctor_set(x_3, 0, x_14);
return x_3;
}
else
{
uint64_t x_15; size_t x_16; size_t x_17; uint64_t x_18; lean_object* x_19; 
x_15 = lean_uint64_of_nat(x_6);
x_16 = lean_usize_of_nat(x_7);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l_ByteArray_foldlMUnsafe_fold___at___Lake_computeBinFileHash_spec__0(x_5, x_16, x_17, x_15);
lean_dec(x_5);
x_19 = lean_box_uint64(x_18);
lean_ctor_set(x_3, 0, x_19);
return x_3;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_unsigned_to_nat(7u);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_byte_array_size(x_20);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
uint64_t x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_20);
x_26 = lean_uint64_of_nat(x_22);
x_27 = lean_box_uint64(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_21);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_24, x_24);
if (x_29 == 0)
{
uint64_t x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_20);
x_30 = lean_uint64_of_nat(x_22);
x_31 = lean_box_uint64(x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_21);
return x_32;
}
else
{
uint64_t x_33; size_t x_34; size_t x_35; uint64_t x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_uint64_of_nat(x_22);
x_34 = lean_usize_of_nat(x_23);
x_35 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_36 = l_ByteArray_foldlMUnsafe_fold___at___Lake_computeBinFileHash_spec__0(x_20, x_34, x_35, x_33);
lean_dec(x_20);
x_37 = lean_box_uint64(x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_21);
return x_38;
}
}
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_3);
if (x_39 == 0)
{
return x_3;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_3, 0);
x_41 = lean_ctor_get(x_3, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_3);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___Lake_computeBinFileHash_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint64_t x_7; uint64_t x_8; lean_object* x_9; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_ByteArray_foldlMUnsafe_fold___at___Lake_computeBinFileHash_spec__0(x_1, x_5, x_6, x_7);
lean_dec(x_1);
x_9 = lean_box_uint64(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_computeBinFileHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeBinFileHash(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instComputeHashFilePathIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_computeBinFileHash___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_IO_FS_readFile(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_String_crlfToLf(x_5);
lean_dec(x_5);
x_7 = lean_string_hash(x_6);
lean_dec(x_6);
x_8 = l_Lake_Hash_nil;
x_9 = lean_uint64_mix_hash(x_8, x_7);
x_10 = lean_box_uint64(x_9);
lean_ctor_set(x_3, 0, x_10);
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; lean_object* x_18; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = l_String_crlfToLf(x_11);
lean_dec(x_11);
x_14 = lean_string_hash(x_13);
lean_dec(x_13);
x_15 = l_Lake_Hash_nil;
x_16 = lean_uint64_mix_hash(x_15, x_14);
x_17 = lean_box_uint64(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_12);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_3);
if (x_19 == 0)
{
return x_3;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get(x_3, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_3);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeTextFileHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeTextFileHash(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_Lake_instCoeTextFilePathFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTextFilePathFilePath___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoeTextFilePathFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoeTextFilePathFilePath___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashTextFilePathIO___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_computeTextFileHash(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instComputeHashTextFilePathIO() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instComputeHashTextFilePathIO___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashTextFilePathIO___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instComputeHashTextFilePathIO___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instToStringTextFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instCoeTextFilePathFilePath___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash(lean_object* x_1, uint8_t x_2, lean_object* x_3) {
_start:
{
if (x_2 == 0)
{
lean_object* x_4; 
x_4 = l_Lake_computeBinFileHash(x_1, x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lake_computeTextFileHash(x_1, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeFileHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_computeFileHash(x_1, x_4, x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0(uint64_t x_1, lean_object* x_2, uint64_t x_3) {
_start:
{
uint64_t x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_uint64_mix_hash(x_1, x_3);
x_5 = lean_box_uint64(x_4);
x_6 = lean_apply_2(x_2, lean_box(0), x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_box_uint64(x_4);
x_7 = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_1);
x_8 = lean_apply_1(x_2, x_5);
x_9 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_8, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_computeArrayHash___redArg___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_nil;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_3);
x_9 = lean_nat_dec_lt(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_10 = l_Lake_computeArrayHash___redArg___boxed__const__1;
x_11 = lean_apply_2(x_6, lean_box(0), x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_8, x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = l_Lake_computeArrayHash___redArg___boxed__const__1;
x_14 = lean_apply_2(x_6, lean_box(0), x_13);
return x_14;
}
else
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; lean_object* x_19; 
x_15 = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_15, 0, x_6);
lean_closure_set(x_15, 1, x_1);
lean_closure_set(x_15, 2, x_4);
x_16 = lean_usize_of_nat(x_7);
x_17 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_18 = l_Lake_computeArrayHash___redArg___boxed__const__1;
x_19 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_2, x_15, x_3, x_16, x_17, x_18);
return x_19;
}
}
}
}
static lean_object* _init_l_Lake_computeArrayHash___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_nil;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_array_get_size(x_5);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = l_Lake_computeArrayHash___boxed__const__1;
x_13 = lean_apply_2(x_8, lean_box(0), x_12);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = lean_nat_dec_le(x_10, x_10);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_15 = l_Lake_computeArrayHash___boxed__const__1;
x_16 = lean_apply_2(x_8, lean_box(0), x_15);
return x_16;
}
else
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_alloc_closure((void*)(l_Lake_computeArrayHash___redArg___lam__1___boxed), 5, 3);
lean_closure_set(x_17, 0, x_8);
lean_closure_set(x_17, 1, x_3);
lean_closure_set(x_17, 2, x_6);
x_18 = lean_usize_of_nat(x_9);
x_19 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_20 = l_Lake_computeArrayHash___boxed__const__1;
x_21 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_4, x_17, x_5, x_18, x_19, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint64_t x_4; uint64_t x_5; lean_object* x_6; 
x_4 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_5 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_6 = l_Lake_computeArrayHash___redArg___lam__0(x_4, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_computeArrayHash___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_7 = l_Lake_computeArrayHash___redArg___lam__1(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(x_3, 0, lean_box(0));
lean_closure_set(x_3, 1, lean_box(0));
lean_closure_set(x_3, 2, x_1);
lean_closure_set(x_3, 3, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeHashArrayOfMonad(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_computeArrayHash), 5, 4);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_3);
lean_closure_set(x_5, 3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lake_MTime_instOfNat() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
x_3 = lean_uint32_of_nat(x_1);
x_4 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_MTime_instBEq() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_beqSystemTime____x40_Init_System_IO___hyg_3124____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instRepr() {
_start:
{
lean_object* x_1; 
x_1 = l_IO_FS_instReprSystemTime;
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instOrd() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_MTime_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMin___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Ord_instDecidableRelLe___redArg(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_dec(x_3);
return x_2;
}
}
}
static lean_object* _init_l_Lake_MTime_instMin() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_MTime_instMin___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_instMax___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Ord_instDecidableRelLe___redArg(x_1, x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
lean_dec(x_2);
return x_3;
}
}
}
static lean_object* _init_l_Lake_MTime_instMax() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_MTime_instMax___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_MTime_instNilTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
x_3 = lean_uint32_of_nat(x_1);
x_4 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set_uint32(x_4, sizeof(void*)*1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_MTime_instMixTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_MTime_instMax___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime___redArg(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instComputeTraceIOMTimeOfGetMTime___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instComputeTraceIOMTimeOfGetMTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instComputeTraceIOMTimeOfGetMTime(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_getFileMTime___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getFileMTime(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_instGetMTimeFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_getFileMTime___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_io_metadata(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_3);
if (x_11 == 0)
{
return x_3;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_3, 0);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_3);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
static lean_object* _init_l_Lake_instGetMTimeTextFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_instGetMTimeTextFilePath___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instGetMTimeTextFilePath___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_instGetMTimeTextFilePath___lam__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_2(x_1, x_2, x_4);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed), 2, 0);
x_9 = l_Ord_instDecidableRelLt___redArg(x_8, x_3, x_7);
x_10 = lean_box(x_9);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed), 2, 0);
x_14 = l_Ord_instDecidableRelLt___redArg(x_13, x_3, x_11);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_3);
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 0, x_19);
return x_5;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_MTime_checkUpToDate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace___redArg___lam__0____x40_Lake_Build_Trace___hyg_1359_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lake_Build_Trace_0__Lake_reprBuildTrace___redArg____x40_Lake_Build_Trace___hyg_1359_(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace___redArg____x40_Lake_Build_Trace___hyg_1359_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("caption", 7, 7);
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
x_10 = lean_unsigned_to_nat(11u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = l_String_quote(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
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
x_25 = lean_mk_string_unchecked("inputs", 6, 6);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(10u);
x_30 = lean_nat_to_int(x_29);
x_76 = lean_ctor_get(x_1, 1);
lean_inc(x_76);
x_77 = lean_array_get_size(x_76);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_nat_dec_eq(x_77, x_78);
lean_dec(x_77);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_alloc_closure((void*)(l___private_Lake_Build_Trace_0__Lake_reprBuildTrace___redArg___lam__0____x40_Lake_Build_Trace___hyg_1359_), 1, 0);
x_81 = lean_mk_string_unchecked("#[", 2, 2);
x_82 = lean_array_to_list(x_76);
lean_inc(x_21);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_21);
lean_ctor_set(x_83, 1, x_23);
x_84 = l_Std_Format_joinSep(lean_box(0), x_80, x_82, x_83);
x_85 = lean_mk_string_unchecked("]", 1, 1);
x_86 = lean_unsigned_to_nat(2u);
x_87 = lean_nat_to_int(x_86);
x_88 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_88, 0, x_81);
x_89 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_84);
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_85);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Std_Format_fill(x_92);
x_31 = x_93;
goto block_75;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_dec(x_76);
x_94 = lean_mk_string_unchecked("#[]", 3, 3);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_31 = x_95;
goto block_75;
}
block_75:
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_32 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_unbox(x_16);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_28);
lean_ctor_set(x_35, 1, x_33);
lean_inc(x_21);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_21);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_23);
x_38 = lean_mk_string_unchecked("hash", 4, 4);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
lean_inc(x_8);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_8);
x_42 = lean_unsigned_to_nat(8u);
x_43 = lean_nat_to_int(x_42);
x_44 = lean_ctor_get(x_1, 2);
lean_inc(x_44);
x_45 = lean_unbox_uint64(x_44);
lean_dec(x_44);
x_46 = l___private_Lake_Build_Trace_0__Lake_reprHash___redArg____x40_Lake_Build_Trace___hyg_614_(x_45);
x_47 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_unbox(x_16);
lean_ctor_set_uint8(x_48, sizeof(void*)*1, x_49);
x_50 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_48);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_21);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_23);
x_53 = lean_mk_string_unchecked("mtime", 5, 5);
x_54 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_54, 0, x_53);
x_55 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_8);
x_57 = lean_unsigned_to_nat(9u);
x_58 = lean_nat_to_int(x_57);
x_59 = lean_ctor_get(x_1, 3);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l___private_Init_System_IO_0__IO_FS_reprSystemTime___redArg____x40_Init_System_IO___hyg_3066_(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox(x_16);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_56);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_mk_string_unchecked(" }", 2, 2);
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_nat_to_int(x_66);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_2);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_64);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_65);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_67);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_unbox(x_16);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_74);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace____x40_Lake_Build_Trace___hyg_1359_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Trace_0__Lake_reprBuildTrace___redArg____x40_Lake_Build_Trace___hyg_1359_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Build_Trace_0__Lake_reprBuildTrace____x40_Lake_Build_Trace___hyg_1359____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Build_Trace_0__Lake_reprBuildTrace____x40_Lake_Build_Trace___hyg_1359_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprBuildTrace() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Build_Trace_0__Lake_reprBuildTrace____x40_Lake_Build_Trace___hyg_1359____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 1);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get(x_2, 3);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_3);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withCaption___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_BuildTrace_withCaption(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_2);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_withoutInputs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_BuildTrace_withoutInputs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash(uint64_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_nat_to_int(x_3);
x_6 = lean_uint32_of_nat(x_3);
x_7 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint32(x_7, sizeof(void*)*1, x_6);
x_8 = lean_box_uint64(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofHash___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_4 = l_Lake_BuildTrace_ofHash(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0(uint64_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("<hash>", 6, 6);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_nat_to_int(x_3);
x_6 = lean_uint32_of_nat(x_3);
x_7 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set_uint32(x_7, sizeof(void*)*1, x_6);
x_8 = lean_box_uint64(x_1);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_8);
lean_ctor_set(x_9, 3, x_7);
return x_9;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeHash() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildTrace_instCoeHash___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeHash___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint64(x_1);
lean_dec(x_1);
x_3 = l_Lake_BuildTrace_instCoeHash___lam__0(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_BuildTrace_ofMTime___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_nil;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_ofMTime(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_Lake_BuildTrace_ofMTime___boxed__const__1;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeMTime___lam__0___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_nil;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instCoeMTime___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("<mtime>", 7, 7);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = l_Lake_BuildTrace_instCoeMTime___lam__0___boxed__const__1;
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_5);
lean_ctor_set(x_6, 3, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_BuildTrace_instCoeMTime() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildTrace_instCoeMTime___lam__0), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_BuildTrace_nil___boxed__const__1() {
_start:
{
uint64_t x_1; lean_object* x_2; 
x_1 = l_Lake_Hash_nil;
x_2 = lean_box_uint64(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_nil(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_nat_to_int(x_2);
x_5 = lean_uint32_of_nat(x_2);
x_6 = lean_alloc_ctor(0, 1, 4);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set_uint32(x_6, sizeof(void*)*1, x_5);
x_7 = l_Lake_BuildTrace_nil___boxed__const__1;
x_8 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
lean_ctor_set(x_8, 3, x_6);
return x_8;
}
}
static lean_object* _init_l_Lake_BuildTrace_instNilTrace() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_mk_string_unchecked("<nil>", 5, 5);
x_2 = l_Lake_BuildTrace_nil(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_5);
x_7 = lean_apply_1(x_2, x_5);
x_8 = lean_apply_3(x_3, lean_box(0), x_7, x_6);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_5);
x_11 = lean_apply_2(x_4, x_5, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_apply_1(x_1, x_5);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_11, 0, x_17);
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_apply_1(x_1, x_5);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_mk_empty_array_with_capacity(x_21);
x_23 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_9);
lean_ctor_set(x_23, 3, x_18);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_19);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_11);
if (x_25 == 0)
{
return x_11;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_11, 0);
x_27 = lean_ctor_get(x_11, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_11);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_compute(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lake_BuildTrace_compute___redArg(x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute), 8, 6);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, lean_box(0));
lean_closure_set(x_5, 2, x_1);
lean_closure_set(x_5, 3, x_2);
lean_closure_set(x_5, 4, x_3);
lean_closure_set(x_5, 5, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_instComputeTraceIOOfToStringOfComputeHashOfMonadLiftTOfGetMTime(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_alloc_closure((void*)(l_Lake_BuildTrace_compute), 8, 6);
lean_closure_set(x_7, 0, lean_box(0));
lean_closure_set(x_7, 1, lean_box(0));
lean_closure_set(x_7, 2, x_3);
lean_closure_set(x_7, 3, x_4);
lean_closure_set(x_7, 4, x_5);
lean_closure_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_mix(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_2);
x_5 = lean_array_push(x_4, x_2);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
x_8 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_9 = lean_unbox_uint64(x_7);
lean_dec(x_7);
x_10 = lean_uint64_mix_hash(x_8, x_9);
x_11 = lean_alloc_closure((void*)(l___private_Init_System_IO_0__IO_FS_ordSystemTime____x40_Init_System_IO___hyg_3198____boxed), 2, 0);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_13);
lean_inc(x_12);
x_14 = l_Ord_instDecidableRelLe___redArg(x_11, x_12, x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_13);
x_15 = lean_box_uint64(x_10);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_5);
lean_ctor_set(x_16, 2, x_15);
lean_ctor_set(x_16, 3, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_17 = lean_box_uint64(x_10);
x_18 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_18, 0, x_3);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_17);
lean_ctor_set(x_18, 3, x_13);
return x_18;
}
}
}
static lean_object* _init_l_Lake_BuildTrace_instMixTrace() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_BuildTrace_mix), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg(lean_object* x_1, lean_object* x_2, uint64_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint64_t x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unbox_uint64(x_6);
lean_dec(x_6);
x_8 = lean_uint64_dec_eq(x_3, x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
else
{
lean_object* x_11; 
x_11 = lean_apply_2(x_1, x_2, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint64_t x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lake_BuildTrace_checkAgainstHash___redArg(x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint64_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint64(x_3);
lean_dec(x_3);
x_7 = l_Lake_BuildTrace_checkAgainstHash___redArg(x_1, x_2, x_6, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstHash___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint64_t x_7; lean_object* x_8; 
x_7 = lean_unbox_uint64(x_4);
lean_dec(x_4);
x_8 = l_Lake_BuildTrace_checkAgainstHash(x_1, x_2, x_3, x_7, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 3);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lake_MTime_checkUpToDate___redArg(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_BuildTrace_checkAgainstTime(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 3);
lean_inc(x_6);
lean_dec(x_4);
x_7 = l_Lake_MTime_checkUpToDate___redArg(x_2, x_3, x_6, x_5);
return x_7;
}
}
lean_object* initialize_Lake_Util_IO(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Data_Json(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Trace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Util_IO(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Data_Json(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instCheckExistsFilePath = _init_l_Lake_instCheckExistsFilePath();
lean_mark_persistent(l_Lake_instCheckExistsFilePath);
l_Lake_instBEqHash = _init_l_Lake_instBEqHash();
lean_mark_persistent(l_Lake_instBEqHash);
l_Lake_instReprHash = _init_l_Lake_instReprHash();
lean_mark_persistent(l_Lake_instReprHash);
l_Lake_Hash_nil = _init_l_Lake_Hash_nil();
l_Lake_Hash_instNilTrace = _init_l_Lake_Hash_instNilTrace();
l_Lake_Hash_instMixTrace = _init_l_Lake_Hash_instMixTrace();
lean_mark_persistent(l_Lake_Hash_instMixTrace);
l_Lake_Hash_instToString = _init_l_Lake_Hash_instToString();
lean_mark_persistent(l_Lake_Hash_instToString);
l_Lake_Hash_instToJson = _init_l_Lake_Hash_instToJson();
lean_mark_persistent(l_Lake_Hash_instToJson);
l_Lake_Hash_instFromJson = _init_l_Lake_Hash_instFromJson();
lean_mark_persistent(l_Lake_Hash_instFromJson);
l_Lake_instComputeHashBoolId = _init_l_Lake_instComputeHashBoolId();
lean_mark_persistent(l_Lake_instComputeHashBoolId);
l_Lake_instComputeHashStringId = _init_l_Lake_instComputeHashStringId();
lean_mark_persistent(l_Lake_instComputeHashStringId);
l_Lake_instComputeHashFilePathIO = _init_l_Lake_instComputeHashFilePathIO();
lean_mark_persistent(l_Lake_instComputeHashFilePathIO);
l_Lake_instCoeTextFilePathFilePath = _init_l_Lake_instCoeTextFilePathFilePath();
lean_mark_persistent(l_Lake_instCoeTextFilePathFilePath);
l_Lake_instComputeHashTextFilePathIO = _init_l_Lake_instComputeHashTextFilePathIO();
lean_mark_persistent(l_Lake_instComputeHashTextFilePathIO);
l_Lake_instToStringTextFilePath = _init_l_Lake_instToStringTextFilePath();
lean_mark_persistent(l_Lake_instToStringTextFilePath);
l_Lake_computeArrayHash___redArg___boxed__const__1 = _init_l_Lake_computeArrayHash___redArg___boxed__const__1();
lean_mark_persistent(l_Lake_computeArrayHash___redArg___boxed__const__1);
l_Lake_computeArrayHash___boxed__const__1 = _init_l_Lake_computeArrayHash___boxed__const__1();
lean_mark_persistent(l_Lake_computeArrayHash___boxed__const__1);
l_Lake_MTime_instOfNat = _init_l_Lake_MTime_instOfNat();
lean_mark_persistent(l_Lake_MTime_instOfNat);
l_Lake_MTime_instBEq = _init_l_Lake_MTime_instBEq();
lean_mark_persistent(l_Lake_MTime_instBEq);
l_Lake_MTime_instRepr = _init_l_Lake_MTime_instRepr();
lean_mark_persistent(l_Lake_MTime_instRepr);
l_Lake_MTime_instOrd = _init_l_Lake_MTime_instOrd();
lean_mark_persistent(l_Lake_MTime_instOrd);
l_Lake_MTime_instLT = _init_l_Lake_MTime_instLT();
lean_mark_persistent(l_Lake_MTime_instLT);
l_Lake_MTime_instLE = _init_l_Lake_MTime_instLE();
lean_mark_persistent(l_Lake_MTime_instLE);
l_Lake_MTime_instMin = _init_l_Lake_MTime_instMin();
lean_mark_persistent(l_Lake_MTime_instMin);
l_Lake_MTime_instMax = _init_l_Lake_MTime_instMax();
lean_mark_persistent(l_Lake_MTime_instMax);
l_Lake_MTime_instNilTrace = _init_l_Lake_MTime_instNilTrace();
lean_mark_persistent(l_Lake_MTime_instNilTrace);
l_Lake_MTime_instMixTrace = _init_l_Lake_MTime_instMixTrace();
lean_mark_persistent(l_Lake_MTime_instMixTrace);
l_Lake_instGetMTimeFilePath = _init_l_Lake_instGetMTimeFilePath();
lean_mark_persistent(l_Lake_instGetMTimeFilePath);
l_Lake_instGetMTimeTextFilePath = _init_l_Lake_instGetMTimeTextFilePath();
lean_mark_persistent(l_Lake_instGetMTimeTextFilePath);
l_Lake_instReprBuildTrace = _init_l_Lake_instReprBuildTrace();
lean_mark_persistent(l_Lake_instReprBuildTrace);
l_Lake_BuildTrace_instCoeHash = _init_l_Lake_BuildTrace_instCoeHash();
lean_mark_persistent(l_Lake_BuildTrace_instCoeHash);
l_Lake_BuildTrace_ofMTime___boxed__const__1 = _init_l_Lake_BuildTrace_ofMTime___boxed__const__1();
lean_mark_persistent(l_Lake_BuildTrace_ofMTime___boxed__const__1);
l_Lake_BuildTrace_instCoeMTime___lam__0___boxed__const__1 = _init_l_Lake_BuildTrace_instCoeMTime___lam__0___boxed__const__1();
lean_mark_persistent(l_Lake_BuildTrace_instCoeMTime___lam__0___boxed__const__1);
l_Lake_BuildTrace_instCoeMTime = _init_l_Lake_BuildTrace_instCoeMTime();
lean_mark_persistent(l_Lake_BuildTrace_instCoeMTime);
l_Lake_BuildTrace_nil___boxed__const__1 = _init_l_Lake_BuildTrace_nil___boxed__const__1();
lean_mark_persistent(l_Lake_BuildTrace_nil___boxed__const__1);
l_Lake_BuildTrace_instNilTrace = _init_l_Lake_BuildTrace_instNilTrace();
lean_mark_persistent(l_Lake_BuildTrace_instNilTrace);
l_Lake_BuildTrace_instMixTrace = _init_l_Lake_BuildTrace_instMixTrace();
lean_mark_persistent(l_Lake_BuildTrace_instMixTrace);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
