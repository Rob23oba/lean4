// Lean compiler output
// Module: Init.System.FilePath
// Imports: Init.System.Platform Init.Data.ToString.Basic
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
LEAN_EXPORT lean_object* l_System_FilePath_pathSeparators;
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___System_SearchPath_parse_spec__0(lean_object*);
lean_object* l_String_revFindAux(lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_join___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___System_FilePath_parent_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString___lam__0(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object*);
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath;
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_exeExtension;
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object*, lean_object*);
uint64_t lean_string_hash(lean_object*);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0___boxed(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___String_mapAux___at___System_FilePath_normalize_spec__1_spec__1(lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_26_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___System_SearchPath_parse_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___System_SearchPath_toString_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___System_FilePath_normalize_spec__1(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
lean_object* l_String_splitOnAux(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath;
uint32_t l_Char_toUpper(uint32_t);
LEAN_EXPORT lean_object* l_String_mapAux___at___System_FilePath_normalize_spec__1___boxed(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_List_elem___at___System_FilePath_normalize_spec__0___boxed(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object*);
LEAN_EXPORT lean_object* l_String_split___at___System_SearchPath_parse_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116____boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object*);
LEAN_EXPORT uint32_t l_System_FilePath_extSeparator;
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object*);
LEAN_EXPORT lean_object* l_System_instToStringFilePath;
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withFileName___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_26____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object*, lean_object*);
lean_object* l_String_revPosOfAux(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_System_FilePath_pathSeparator;
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___System_SearchPath_parse_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instHashableFilePath;
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___System_SearchPath_parse_spec__2(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object*);
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_SearchPath_parse___boxed(lean_object*);
LEAN_EXPORT lean_object* l_System_instInhabitedFilePath;
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_instDiv;
LEAN_EXPORT uint32_t l_System_SearchPath_separator;
LEAN_EXPORT uint64_t l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116_(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___System_FilePath_normalize_spec__0(uint32_t, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString;
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
extern uint8_t l_System_Platform_isWindows;
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___System_FilePath_parent_spec__0___boxed(lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___boxed(lean_object*);
static lean_object* _init_l_System_instInhabitedFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_26_(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_26____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_System_FilePath_0__System_decEqFilePath____x40_Init_System_FilePath___hyg_26_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_System_instDecidableEqFilePath(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_dec_eq(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instDecidableEqFilePath___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_System_instDecidableEqFilePath(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116_(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; uint64_t x_4; uint64_t x_5; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
x_4 = lean_string_hash(x_1);
x_5 = lean_uint64_mix_hash(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_System_instHashableFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Init_System_FilePath_0__System_hashFilePath____x40_Init_System_FilePath___hyg_116____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_mk_string_unchecked("FilePath.mk ", 12, 12);
x_4 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_String_quote(x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Repr_addAppParen(x_7, x_2);
return x_8;
}
}
static lean_object* _init_l_System_instReprFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_instReprFilePath___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instReprFilePath___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_instReprFilePath___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_System_instToStringFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_instToStringFilePath___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instToStringFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instToStringFilePath___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint32_t _init_l_System_FilePath_pathSeparator() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_unsigned_to_nat(47u);
x_3 = l_Char_ofNat(x_2);
return x_3;
}
else
{
lean_object* x_4; uint32_t x_5; 
x_4 = lean_unsigned_to_nat(92u);
x_5 = l_Char_ofNat(x_4);
return x_5;
}
}
}
static lean_object* _init_l_System_FilePath_pathSeparators() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_unsigned_to_nat(47u);
x_3 = l_Char_ofNat(x_2);
x_4 = lean_box(0);
x_5 = lean_box_uint32(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
else
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_unsigned_to_nat(92u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_unsigned_to_nat(47u);
x_10 = l_Char_ofNat(x_9);
x_11 = lean_box(0);
x_12 = lean_box_uint32(x_10);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_box_uint32(x_8);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
static uint32_t _init_l_System_FilePath_extSeparator() {
_start:
{
lean_object* x_1; uint32_t x_2; 
x_1 = lean_unsigned_to_nat(46u);
x_2 = l_Char_ofNat(x_1);
return x_2;
}
}
static lean_object* _init_l_System_FilePath_exeExtension() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("", 0, 0);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("exe", 3, 3);
return x_3;
}
}
}
LEAN_EXPORT uint8_t l_List_elem___at___System_FilePath_normalize_spec__0(uint32_t x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_unbox_uint32(x_5);
lean_dec(x_5);
x_8 = l_instDecidableEqChar(x_1, x_7);
if (x_8 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_6);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___String_mapAux___at___System_FilePath_normalize_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = l_System_FilePath_pathSeparators;
x_10 = lean_string_utf8_get(x_2, x_1);
x_11 = l_List_elem___at___System_FilePath_normalize_spec__0(x_10, x_9);
if (x_11 == 0)
{
x_3 = x_10;
goto block_7;
}
else
{
uint32_t x_12; 
x_12 = l_System_FilePath_pathSeparator;
x_3 = x_12;
goto block_7;
}
}
else
{
lean_dec(x_1);
return x_2;
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_set(x_2, x_1, x_3);
x_5 = lean_string_utf8_next(x_4, x_1);
lean_dec(x_1);
x_1 = x_5;
x_2 = x_4;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___System_FilePath_normalize_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = l_System_FilePath_pathSeparators;
x_10 = lean_string_utf8_get(x_2, x_1);
x_11 = l_List_elem___at___System_FilePath_normalize_spec__0(x_10, x_9);
if (x_11 == 0)
{
x_3 = x_10;
goto block_7;
}
else
{
uint32_t x_12; 
x_12 = l_System_FilePath_pathSeparator;
x_3 = x_12;
goto block_7;
}
}
else
{
return x_2;
}
block_7:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_utf8_set(x_2, x_1, x_3);
x_5 = lean_string_utf8_next(x_4, x_1);
x_6 = l_String_mapAux___at___String_mapAux___at___System_FilePath_normalize_spec__1_spec__1(x_5, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_normalize(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_10; uint8_t x_21; uint8_t x_31; 
x_31 = l_System_Platform_isWindows;
if (x_31 == 0)
{
x_21 = x_31;
goto block_30;
}
else
{
lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_string_length(x_1);
x_34 = lean_nat_dec_le(x_32, x_33);
lean_dec(x_33);
x_21 = x_34;
goto block_30;
}
block_9:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_System_FilePath_pathSeparators;
x_4 = l_List_lengthTR(lean_box(0), x_3);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_dec_eq(x_4, x_5);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = l_String_mapAux___at___System_FilePath_normalize_spec__1(x_7, x_2);
return x_8;
}
else
{
return x_2;
}
}
block_20:
{
if (x_10 == 0)
{
x_2 = x_1;
goto block_9;
}
else
{
lean_object* x_11; uint32_t x_12; lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_string_utf8_get(x_1, x_11);
x_13 = lean_unsigned_to_nat(58u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_12, x_14);
if (x_15 == 0)
{
x_2 = x_1;
goto block_9;
}
else
{
lean_object* x_16; uint32_t x_17; uint32_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_string_utf8_get(x_1, x_16);
x_18 = l_Char_toUpper(x_17);
x_19 = lean_string_utf8_set(x_1, x_16, x_18);
x_2 = x_19;
goto block_9;
}
}
}
block_30:
{
if (x_21 == 0)
{
x_2 = x_1;
goto block_9;
}
else
{
lean_object* x_22; lean_object* x_23; uint32_t x_24; uint32_t x_25; uint8_t x_26; 
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_unsigned_to_nat(97u);
x_24 = lean_uint32_of_nat(x_23);
x_25 = lean_string_utf8_get(x_1, x_22);
x_26 = lean_uint32_dec_le(x_24, x_25);
if (x_26 == 0)
{
x_10 = x_26;
goto block_20;
}
else
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(122u);
x_28 = lean_uint32_of_nat(x_27);
x_29 = lean_uint32_dec_le(x_25, x_28);
x_10 = x_29;
goto block_20;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___System_FilePath_normalize_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_List_elem___at___System_FilePath_normalize_spec__0(x_3, x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___System_FilePath_normalize_spec__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_String_mapAux___at___System_FilePath_normalize_spec__1(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isAbsolute(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_10 = l_System_FilePath_pathSeparators;
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_string_utf8_get(x_1, x_11);
x_13 = l_List_elem___at___System_FilePath_normalize_spec__0(x_12, x_10);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = l_System_Platform_isWindows;
if (x_14 == 0)
{
x_2 = x_14;
goto block_9;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_string_length(x_1);
x_17 = lean_nat_dec_lt(x_15, x_16);
lean_dec(x_16);
x_2 = x_17;
goto block_9;
}
}
else
{
return x_13;
}
block_9:
{
if (x_2 == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; uint32_t x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_next(x_1, x_3);
x_5 = lean_string_utf8_get(x_1, x_4);
lean_dec(x_4);
x_6 = lean_unsigned_to_nat(58u);
x_7 = l_Char_ofNat(x_6);
x_8 = l_instDecidableEqChar(x_5, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isAbsolute___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isAbsolute(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_System_FilePath_isRelative(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_System_FilePath_isAbsolute(x_1);
if (x_2 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_isRelative___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_System_FilePath_isRelative(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_System_FilePath_isAbsolute(x_2);
if (x_3 == 0)
{
uint32_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = l_System_FilePath_pathSeparator;
x_5 = lean_mk_string_unchecked("", 0, 0);
x_6 = lean_string_push(x_5, x_4);
x_7 = lean_string_append(x_1, x_6);
lean_dec(x_6);
x_8 = lean_string_append(x_7, x_2);
return x_8;
}
else
{
lean_dec(x_1);
lean_inc(x_2);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_join___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_join(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_instDiv() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_join___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_join(x_1, x_2);
return x_3;
}
}
static lean_object* _init_l_System_FilePath_instHDivString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_FilePath_instHDivString___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_instHDivString___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_instHDivString___lam__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0(lean_object* x_1, uint32_t x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_List_elem___at___System_FilePath_normalize_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_System_FilePath_pathSeparators;
x_3 = lean_alloc_closure((void*)(l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = l_String_revFindAux(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_4 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___lam__0(x_1, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___System_FilePath_parent_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_2, 0);
x_11 = l_instDecidableEqPos(x_9, x_10);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_16; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_24; 
x_24 = lean_box(0);
x_16 = x_24;
goto block_23;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_3, 0);
lean_inc(x_25);
x_26 = lean_string_utf8_extract(x_1, x_2, x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_16 = x_27;
goto block_23;
}
block_15:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_string_length(x_1);
x_7 = lean_nat_dec_eq(x_6, x_5);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_sub(x_5, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___System_FilePath_parent_spec__0(x_3, x_10);
lean_dec(x_10);
lean_dec(x_3);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_string_utf8_extract(x_1, x_2, x_5);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
else
{
lean_object* x_14; 
lean_dec(x_4);
lean_dec(x_3);
x_14 = lean_box(0);
return x_14;
}
}
block_23:
{
uint8_t x_17; 
x_17 = l_System_FilePath_isAbsolute(x_1);
if (x_17 == 0)
{
lean_dec(x_3);
return x_16;
}
else
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = l_System_FilePath_pathSeparators;
x_19 = lean_string_utf8_get(x_1, x_2);
x_20 = l_List_elem___at___System_FilePath_normalize_spec__0(x_19, x_18);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_unsigned_to_nat(3u);
x_4 = x_16;
x_5 = x_21;
goto block_15;
}
else
{
lean_object* x_22; 
x_22 = lean_unsigned_to_nat(1u);
x_4 = x_16;
x_5 = x_22;
goto block_15;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___System_FilePath_parent_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Option_Basic_0__Option_beqOption____x40_Init_Data_Option_Basic___hyg_159____at___System_FilePath_parent_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_parent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_parent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileName(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_10; lean_object* x_17; 
x_17 = l___private_Init_System_FilePath_0__System_FilePath_posOfLastSep(x_1);
if (lean_obj_tag(x_17) == 0)
{
x_10 = x_1;
goto block_16;
}
else
{
lean_object* x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(47u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_Char_utf8Size(x_20);
x_22 = lean_nat_add(x_18, x_21);
lean_dec(x_21);
lean_dec(x_18);
x_23 = lean_string_utf8_byte_size(x_1);
x_24 = lean_string_utf8_extract(x_1, x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_1);
x_10 = x_24;
goto block_16;
}
block_9:
{
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_mk_string_unchecked("..", 2, 2);
x_5 = lean_string_dec_eq(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_2);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
}
else
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_box(0);
return x_8;
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_instDecidableEqPos(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_mk_string_unchecked(".", 1, 1);
x_15 = lean_string_dec_eq(x_10, x_14);
lean_dec(x_14);
x_2 = x_10;
x_3 = x_15;
goto block_9;
}
else
{
x_2 = x_10;
x_3 = x_13;
goto block_9;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_fileStem(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_unsigned_to_nat(46u);
x_5 = l_Char_ofNat(x_4);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = l_String_revPosOfAux(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_dec(x_3);
return x_2;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_nat_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_2);
x_12 = lean_string_utf8_extract(x_3, x_10, x_9);
lean_dec(x_9);
lean_dec(x_3);
lean_ctor_set(x_7, 0, x_12);
return x_7;
}
else
{
lean_free_object(x_7);
lean_dec(x_9);
lean_dec(x_3);
return x_2;
}
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_nat_dec_eq(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_2);
x_16 = lean_string_utf8_extract(x_3, x_14, x_13);
lean_dec(x_13);
lean_dec(x_3);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
else
{
lean_dec(x_13);
lean_dec(x_3);
return x_2;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_extension(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_2) == 0)
{
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_unsigned_to_nat(46u);
x_5 = l_Char_ofNat(x_4);
x_6 = lean_string_utf8_byte_size(x_3);
lean_inc(x_6);
x_7 = l_String_revPosOfAux(x_3, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_3);
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
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = l_Char_utf8Size(x_5);
x_14 = lean_nat_add(x_10, x_13);
lean_dec(x_13);
lean_dec(x_10);
x_15 = lean_string_utf8_extract(x_3, x_14, x_6);
lean_dec(x_6);
lean_dec(x_14);
lean_dec(x_3);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; 
lean_free_object(x_7);
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
x_16 = lean_box(0);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_7, 0);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_nat_dec_eq(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = l_Char_utf8Size(x_5);
x_21 = lean_nat_add(x_17, x_20);
lean_dec(x_20);
lean_dec(x_17);
x_22 = lean_string_utf8_extract(x_3, x_21, x_6);
lean_dec(x_6);
lean_dec(x_21);
lean_dec(x_3);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
else
{
lean_object* x_24; 
lean_dec(x_17);
lean_dec(x_6);
lean_dec(x_3);
x_24 = lean_box(0);
return x_24;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_parent(x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = l_System_FilePath_join(x_4, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withFileName___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_withFileName(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_fileName(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_instDecidableEqPos(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked(".", 1, 1);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_System_FilePath_withFileName(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_System_FilePath_withFileName(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_addExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_addExtension(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
lean_inc(x_1);
x_3 = l_System_FilePath_fileStem(x_1);
if (lean_obj_tag(x_3) == 0)
{
return x_1;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_string_utf8_byte_size(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = l_instDecidableEqPos(x_5, x_6);
lean_dec(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_mk_string_unchecked(".", 1, 1);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_10 = lean_string_append(x_9, x_2);
x_11 = l_System_FilePath_withFileName(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
return x_11;
}
else
{
lean_object* x_12; 
x_12 = l_System_FilePath_withFileName(x_1, x_4);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_System_FilePath_withExtension___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_FilePath_withExtension(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_FilePath_components(lean_object* x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_System_FilePath_normalize(x_1);
x_3 = l_System_FilePath_pathSeparator;
x_4 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_4);
x_5 = lean_string_push(x_4, x_3);
x_6 = lean_string_dec_eq(x_5, x_4);
lean_dec(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_box(0);
x_9 = l_String_splitOnAux(x_2, x_5, x_7, x_7, x_7, x_8);
lean_dec(x_5);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_5);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_System_mkFilePath(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = l_System_FilePath_pathSeparator;
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_string_push(x_3, x_2);
x_5 = l_String_intercalate(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
static lean_object* _init_l_System_instCoeStringFilePath() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_System_instCoeStringFilePath___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_System_instCoeStringFilePath___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_instCoeStringFilePath___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
static uint32_t _init_l_System_SearchPath_separator() {
_start:
{
uint8_t x_1; 
x_1 = l_System_Platform_isWindows;
if (x_1 == 0)
{
lean_object* x_2; uint32_t x_3; 
x_2 = lean_unsigned_to_nat(58u);
x_3 = l_Char_ofNat(x_2);
return x_3;
}
else
{
lean_object* x_4; uint32_t x_5; 
x_4 = lean_unsigned_to_nat(59u);
x_5 = l_Char_ofNat(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___System_SearchPath_parse_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; uint32_t x_7; uint8_t x_8; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = l_System_SearchPath_separator;
x_8 = l_instDecidableEqChar(x_7, x_6);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_string_utf8_next(x_1, x_3);
x_12 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
lean_inc(x_11);
x_2 = x_11;
x_3 = x_11;
x_4 = x_13;
goto _start;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_4);
x_17 = l_List_reverse___redArg(x_16);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___System_SearchPath_parse_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___System_SearchPath_parse_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___System_SearchPath_parse_spec__2(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l_String_split___at___System_SearchPath_parse_spec__0(x_1);
x_3 = lean_box(0);
x_4 = l_List_mapTR_loop___at___System_SearchPath_parse_spec__2(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___System_SearchPath_parse_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___System_SearchPath_parse_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___System_SearchPath_parse_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___System_SearchPath_parse_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_parse___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_SearchPath_parse(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___System_SearchPath_toString_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_System_SearchPath_toString(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_2 = l_System_SearchPath_separator;
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_string_push(x_3, x_2);
x_5 = lean_box(0);
x_6 = l_List_mapTR_loop___at___System_SearchPath_toString_spec__0(x_1, x_5);
x_7 = l_String_intercalate(x_4, x_6);
lean_dec(x_4);
return x_7;
}
}
lean_object* initialize_Init_System_Platform(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_System_Platform(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_instInhabitedFilePath = _init_l_System_instInhabitedFilePath();
lean_mark_persistent(l_System_instInhabitedFilePath);
l_System_instHashableFilePath = _init_l_System_instHashableFilePath();
lean_mark_persistent(l_System_instHashableFilePath);
l_System_instReprFilePath = _init_l_System_instReprFilePath();
lean_mark_persistent(l_System_instReprFilePath);
l_System_instToStringFilePath = _init_l_System_instToStringFilePath();
lean_mark_persistent(l_System_instToStringFilePath);
l_System_FilePath_pathSeparator = _init_l_System_FilePath_pathSeparator();
l_System_FilePath_pathSeparators = _init_l_System_FilePath_pathSeparators();
lean_mark_persistent(l_System_FilePath_pathSeparators);
l_System_FilePath_extSeparator = _init_l_System_FilePath_extSeparator();
l_System_FilePath_exeExtension = _init_l_System_FilePath_exeExtension();
lean_mark_persistent(l_System_FilePath_exeExtension);
l_System_FilePath_instDiv = _init_l_System_FilePath_instDiv();
lean_mark_persistent(l_System_FilePath_instDiv);
l_System_FilePath_instHDivString = _init_l_System_FilePath_instHDivString();
lean_mark_persistent(l_System_FilePath_instHDivString);
l_System_instCoeStringFilePath = _init_l_System_instCoeStringFilePath();
lean_mark_persistent(l_System_instCoeStringFilePath);
l_System_SearchPath_separator = _init_l_System_SearchPath_separator();
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
