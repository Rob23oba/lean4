// Lean compiler output
// Module: Init.System.Uri
// Imports: Init.Data.String.Extra Init.Data.Nat.Linear Init.System.FilePath
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri(lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
uint8_t lean_byte_array_fget(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_System_FilePath_normalize(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object*);
lean_object* l_hexDigitRepr(lean_object*);
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_letterf;
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object*);
uint8_t lean_uint8_add(uint8_t, uint8_t);
lean_object* lean_string_utf8_set(lean_object*, lean_object*, uint32_t);
lean_object* lean_byte_array_push(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_string_validate_utf8(lean_object*);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_nine;
size_t lean_usize_of_nat(lean_object*);
uint32_t l_Char_toLower(uint32_t);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint32_t l_Char_toUpper(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
extern lean_object* l_ByteArray_empty;
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___System_Uri_fileUriToPath_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___System_Uri_fileUriToPath_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint8_mod(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_String_foldlAux___at___System_Uri_escapeUri_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_pathToUri___lam__0(lean_object*, lean_object*);
uint8_t lean_byte_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Char_toUpper___boxed(lean_object*);
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_letterF;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_letterA;
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_lettera;
lean_object* lean_string_from_utf8_unchecked(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object*);
lean_object* l_String_modify(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_pathToUri___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_rfc3986ReservedChars;
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_mapAux___at___System_Uri_pathToUri_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f___boxed(lean_object*);
lean_object* lean_string_to_utf8(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
uint8_t lean_uint8_shift_right(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_System_Uri_UriEscape_zero;
LEAN_EXPORT lean_object* l_System_Uri_escapeUri___boxed(lean_object*);
uint8_t lean_uint8_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___System_Uri_UriEscape_decodeUri_spec__1(lean_object*);
lean_object* lean_uint8_to_nat(uint8_t);
uint8_t l_Substring_beq(lean_object*, lean_object*);
uint8_t l_List_elem___at___System_FilePath_normalize_spec__0(uint32_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___System_Uri_UriEscape_decodeUri_spec__0(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(uint8_t);
extern uint8_t l_System_Platform_isWindows;
lean_object* lean_byte_array_size(lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___System_Uri_escapeUri_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object*);
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri___boxed(lean_object*);
static uint8_t _init_l_System_Uri_UriEscape_zero() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_unsigned_to_nat(48u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_uint8_of_nat(x_3);
lean_dec(x_3);
return x_4;
}
}
static uint8_t _init_l_System_Uri_UriEscape_nine() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_unsigned_to_nat(57u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_uint8_of_nat(x_3);
lean_dec(x_3);
return x_4;
}
}
static uint8_t _init_l_System_Uri_UriEscape_lettera() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_unsigned_to_nat(97u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_uint8_of_nat(x_3);
lean_dec(x_3);
return x_4;
}
}
static uint8_t _init_l_System_Uri_UriEscape_letterf() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_unsigned_to_nat(102u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_uint8_of_nat(x_3);
lean_dec(x_3);
return x_4;
}
}
static uint8_t _init_l_System_Uri_UriEscape_letterA() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_unsigned_to_nat(65u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_uint8_of_nat(x_3);
lean_dec(x_3);
return x_4;
}
}
static uint8_t _init_l_System_Uri_UriEscape_letterF() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint8_t x_4; 
x_1 = lean_unsigned_to_nat(70u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_uint32_to_nat(x_2);
x_4 = lean_uint8_of_nat(x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(uint8_t x_1) {
_start:
{
lean_object* x_38; uint32_t x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; 
x_38 = lean_unsigned_to_nat(48u);
x_39 = l_Char_ofNat(x_38);
x_40 = lean_uint32_to_nat(x_39);
x_41 = lean_uint8_of_nat(x_40);
lean_dec(x_40);
x_42 = lean_uint8_dec_le(x_41, x_1);
if (x_42 == 0)
{
goto block_37;
}
else
{
lean_object* x_43; uint32_t x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; 
x_43 = lean_unsigned_to_nat(57u);
x_44 = l_Char_ofNat(x_43);
x_45 = lean_uint32_to_nat(x_44);
x_46 = lean_uint8_of_nat(x_45);
lean_dec(x_45);
x_47 = lean_uint8_dec_le(x_1, x_46);
if (x_47 == 0)
{
goto block_37;
}
else
{
uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_uint8_sub(x_1, x_41);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
block_20:
{
lean_object* x_2; uint32_t x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; 
x_2 = lean_unsigned_to_nat(65u);
x_3 = l_Char_ofNat(x_2);
x_4 = lean_uint32_to_nat(x_3);
x_5 = lean_uint8_of_nat(x_4);
lean_dec(x_4);
x_6 = lean_uint8_dec_le(x_5, x_1);
if (x_6 == 0)
{
lean_object* x_7; 
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint32_t x_9; lean_object* x_10; uint8_t x_11; uint8_t x_12; 
x_8 = lean_unsigned_to_nat(70u);
x_9 = l_Char_ofNat(x_8);
x_10 = lean_uint32_to_nat(x_9);
x_11 = lean_uint8_of_nat(x_10);
lean_dec(x_10);
x_12 = lean_uint8_dec_le(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
return x_13;
}
else
{
uint8_t x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_uint8_sub(x_1, x_5);
x_15 = lean_unsigned_to_nat(10u);
x_16 = lean_uint8_of_nat(x_15);
x_17 = lean_uint8_add(x_14, x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
}
}
block_37:
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(97u);
x_22 = l_Char_ofNat(x_21);
x_23 = lean_uint32_to_nat(x_22);
x_24 = lean_uint8_of_nat(x_23);
lean_dec(x_23);
x_25 = lean_uint8_dec_le(x_24, x_1);
if (x_25 == 0)
{
goto block_20;
}
else
{
lean_object* x_26; uint32_t x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(102u);
x_27 = l_Char_ofNat(x_26);
x_28 = lean_uint32_to_nat(x_27);
x_29 = lean_uint8_of_nat(x_28);
lean_dec(x_28);
x_30 = lean_uint8_dec_le(x_1, x_29);
if (x_30 == 0)
{
goto block_20;
}
else
{
uint8_t x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; lean_object* x_35; lean_object* x_36; 
x_31 = lean_uint8_sub(x_1, x_24);
x_32 = lean_unsigned_to_nat(10u);
x_33 = lean_uint8_of_nat(x_32);
x_34 = lean_uint8_add(x_31, x_33);
x_35 = lean_box(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___System_Uri_UriEscape_decodeUri_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint32_t x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_8 = lean_string_to_utf8(x_1);
x_9 = lean_byte_array_size(x_8);
x_10 = lean_unsigned_to_nat(37u);
x_11 = l_Char_ofNat(x_10);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_nat_dec_lt(x_13, x_9);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_9);
lean_dec(x_8);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_23; 
x_16 = lean_uint32_to_nat(x_11);
x_17 = lean_uint8_of_nat(x_16);
lean_dec(x_16);
x_18 = lean_byte_array_fget(x_8, x_13);
x_23 = lean_uint8_dec_eq(x_18, x_17);
if (x_23 == 0)
{
lean_dec(x_9);
lean_dec(x_8);
goto block_22;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_add(x_13, x_24);
x_26 = lean_nat_dec_lt(x_25, x_9);
if (x_26 == 0)
{
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
goto block_22;
}
else
{
uint8_t x_27; lean_object* x_28; 
x_27 = lean_byte_array_fget(x_8, x_25);
lean_dec(x_25);
x_28 = l_System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_9);
lean_dec(x_8);
x_29 = lean_byte_array_push(x_12, x_18);
x_30 = lean_byte_array_push(x_29, x_27);
x_31 = lean_unsigned_to_nat(2u);
x_32 = lean_nat_add(x_13, x_31);
lean_dec(x_13);
x_3 = x_30;
x_4 = x_32;
goto block_7;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
lean_dec(x_28);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_add(x_13, x_34);
x_36 = lean_nat_dec_lt(x_35, x_9);
lean_dec(x_9);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_33);
lean_dec(x_13);
lean_dec(x_8);
x_37 = lean_byte_array_push(x_12, x_18);
x_38 = lean_byte_array_push(x_37, x_27);
x_3 = x_38;
x_4 = x_35;
goto block_7;
}
else
{
uint8_t x_39; lean_object* x_40; 
x_39 = lean_byte_array_fget(x_8, x_35);
lean_dec(x_35);
lean_dec(x_8);
x_40 = l_System_Uri_UriEscape_decodeUri_hexDigitToUInt8_x3f(x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_33);
x_41 = lean_byte_array_push(x_12, x_18);
x_42 = lean_byte_array_push(x_41, x_27);
x_43 = lean_byte_array_push(x_42, x_39);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_add(x_13, x_44);
lean_dec(x_13);
x_3 = x_43;
x_4 = x_45;
goto block_7;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_46 = lean_ctor_get(x_40, 0);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_unsigned_to_nat(4u);
x_48 = lean_uint8_of_nat(x_47);
x_49 = lean_unbox(x_33);
lean_dec(x_33);
x_50 = lean_uint8_shift_left(x_49, x_48);
x_51 = lean_unbox(x_46);
lean_dec(x_46);
x_52 = lean_uint8_add(x_50, x_51);
x_53 = lean_byte_array_push(x_12, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_add(x_13, x_54);
lean_dec(x_13);
x_3 = x_53;
x_4 = x_55;
goto block_7;
}
}
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_byte_array_push(x_12, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_add(x_13, x_20);
lean_dec(x_13);
x_3 = x_19;
x_4 = x_21;
goto block_7;
}
}
block_7:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___System_Uri_UriEscape_decodeUri_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = l_ByteArray_empty;
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = l_Lean_Loop_forIn_loop___at___System_Uri_UriEscape_decodeUri_spec__0(x_1, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_string_validate_utf8(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("Init.Data.String.Extra", 22, 22);
x_9 = lean_mk_string_unchecked("String.fromUTF8!", 16, 16);
x_10 = lean_unsigned_to_nat(128u);
x_11 = lean_unsigned_to_nat(47u);
x_12 = lean_mk_string_unchecked("invalid UTF-8 string", 20, 20);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___System_Uri_UriEscape_decodeUri_spec__1(x_13);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_string_from_utf8_unchecked(x_6);
lean_dec(x_6);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at___System_Uri_UriEscape_decodeUri_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Loop_forIn_loop___at___System_Uri_UriEscape_decodeUri_spec__0(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_decodeUri___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_Uri_UriEscape_decodeUri(x_1);
lean_dec(x_1);
return x_2;
}
}
static lean_object* _init_l_System_Uri_UriEscape_rfc3986ReservedChars() {
_start:
{
lean_object* x_1; uint32_t x_2; lean_object* x_3; uint32_t x_4; lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; uint32_t x_12; lean_object* x_13; uint32_t x_14; lean_object* x_15; uint32_t x_16; lean_object* x_17; uint32_t x_18; lean_object* x_19; uint32_t x_20; lean_object* x_21; uint32_t x_22; lean_object* x_23; uint32_t x_24; lean_object* x_25; uint32_t x_26; lean_object* x_27; uint32_t x_28; lean_object* x_29; uint32_t x_30; lean_object* x_31; uint32_t x_32; lean_object* x_33; uint32_t x_34; lean_object* x_35; uint32_t x_36; lean_object* x_37; uint32_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_1 = lean_unsigned_to_nat(59u);
x_2 = l_Char_ofNat(x_1);
x_3 = lean_unsigned_to_nat(58u);
x_4 = l_Char_ofNat(x_3);
x_5 = lean_unsigned_to_nat(63u);
x_6 = l_Char_ofNat(x_5);
x_7 = lean_unsigned_to_nat(35u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_unsigned_to_nat(91u);
x_10 = l_Char_ofNat(x_9);
x_11 = lean_unsigned_to_nat(93u);
x_12 = l_Char_ofNat(x_11);
x_13 = lean_unsigned_to_nat(64u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_unsigned_to_nat(38u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_unsigned_to_nat(61u);
x_18 = l_Char_ofNat(x_17);
x_19 = lean_unsigned_to_nat(43u);
x_20 = l_Char_ofNat(x_19);
x_21 = lean_unsigned_to_nat(36u);
x_22 = l_Char_ofNat(x_21);
x_23 = lean_unsigned_to_nat(44u);
x_24 = l_Char_ofNat(x_23);
x_25 = lean_unsigned_to_nat(33u);
x_26 = l_Char_ofNat(x_25);
x_27 = lean_unsigned_to_nat(39u);
x_28 = l_Char_ofNat(x_27);
x_29 = lean_unsigned_to_nat(40u);
x_30 = l_Char_ofNat(x_29);
x_31 = lean_unsigned_to_nat(41u);
x_32 = l_Char_ofNat(x_31);
x_33 = lean_unsigned_to_nat(42u);
x_34 = l_Char_ofNat(x_33);
x_35 = lean_unsigned_to_nat(37u);
x_36 = l_Char_ofNat(x_35);
x_37 = lean_unsigned_to_nat(32u);
x_38 = l_Char_ofNat(x_37);
x_39 = lean_box(0);
x_40 = lean_box_uint32(x_38);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
x_42 = lean_box_uint32(x_36);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
x_44 = lean_box_uint32(x_34);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
x_46 = lean_box_uint32(x_32);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_48 = lean_box_uint32(x_30);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_box_uint32(x_28);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_box_uint32(x_26);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_box_uint32(x_24);
x_55 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_53);
x_56 = lean_box_uint32(x_22);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
x_58 = lean_box_uint32(x_20);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
x_60 = lean_box_uint32(x_18);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_box_uint32(x_16);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_box_uint32(x_14);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_63);
x_66 = lean_box_uint32(x_12);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_65);
x_68 = lean_box_uint32(x_10);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_67);
x_70 = lean_box_uint32(x_8);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_69);
x_72 = lean_box_uint32(x_6);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_box_uint32(x_4);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_box_uint32(x_2);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = lean_string_utf8_at_end(x_2, x_1);
if (x_3 == 0)
{
uint32_t x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_string_utf8_get(x_2, x_1);
x_5 = l_Char_toUpper(x_4);
x_6 = lean_string_utf8_set(x_2, x_1, x_5);
x_7 = lean_string_utf8_next(x_6, x_1);
lean_dec(x_1);
x_1 = x_7;
x_2 = x_6;
goto _start;
}
else
{
lean_dec(x_1);
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(uint8_t x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; lean_object* x_4; uint8_t x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_unsigned_to_nat(16u);
x_3 = lean_uint8_of_nat(x_2);
x_4 = lean_unsigned_to_nat(4u);
x_5 = lean_uint8_of_nat(x_4);
x_6 = lean_uint8_shift_right(x_1, x_5);
x_7 = lean_uint8_mod(x_1, x_3);
x_8 = lean_uint8_to_nat(x_6);
x_9 = l_hexDigitRepr(x_8);
lean_dec(x_8);
x_10 = lean_uint8_to_nat(x_7);
x_11 = l_hexDigitRepr(x_10);
lean_dec(x_10);
x_12 = lean_string_append(x_9, x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = l_String_mapAux___at___System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex_spec__0(x_13, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_byte_array_uget(x_1, x_2);
x_7 = lean_mk_string_unchecked("%", 1, 1);
x_8 = lean_string_append(x_4, x_7);
lean_dec(x_7);
x_9 = l_System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(x_6);
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
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar(uint32_t x_1) {
_start:
{
uint8_t x_2; lean_object* x_24; uint8_t x_25; 
x_24 = l_System_Uri_UriEscape_rfc3986ReservedChars;
x_25 = l_List_elem___at___System_FilePath_normalize_spec__0(x_1, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(32u);
x_27 = l_Char_ofNat(x_26);
x_28 = lean_uint32_dec_lt(x_1, x_27);
x_2 = x_28;
goto block_23;
}
else
{
x_2 = x_25;
goto block_23;
}
block_23:
{
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_uint32_to_nat(x_1);
x_4 = lean_unsigned_to_nat(127u);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = lean_mk_string_unchecked("", 0, 0);
lean_inc(x_6);
x_7 = lean_string_push(x_6, x_1);
x_8 = lean_string_to_utf8(x_7);
lean_dec(x_7);
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_byte_array_size(x_8);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_8);
return x_6;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_10, x_10);
if (x_12 == 0)
{
lean_dec(x_10);
lean_dec(x_8);
return x_6;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_9);
x_14 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_15 = l_ByteArray_foldlMUnsafe_fold___at___System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(x_8, x_13, x_14, x_6);
lean_dec(x_8);
return x_15;
}
}
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_mk_string_unchecked("", 0, 0);
x_17 = lean_string_push(x_16, x_1);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_mk_string_unchecked("%", 1, 1);
x_19 = lean_uint32_to_nat(x_1);
x_20 = lean_uint8_of_nat(x_19);
lean_dec(x_19);
x_21 = l_System_Uri_UriEscape_uriEscapeAsciiChar_uInt8ToHex(x_20);
x_22 = lean_string_append(x_18, x_21);
lean_dec(x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_ByteArray_foldlMUnsafe_fold___at___System_Uri_UriEscape_uriEscapeAsciiChar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_ByteArray_foldlMUnsafe_fold___at___System_Uri_UriEscape_uriEscapeAsciiChar_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_System_Uri_UriEscape_uriEscapeAsciiChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_System_Uri_UriEscape_uriEscapeAsciiChar(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___System_Uri_escapeUri_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_nat_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_6; uint32_t x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = l_System_Uri_UriEscape_uriEscapeAsciiChar(x_7);
x_9 = lean_string_append(x_4, x_8);
lean_dec(x_8);
x_3 = x_6;
x_4 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_escapeUri(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_foldlAux___at___System_Uri_escapeUri_spec__0(x_1, x_3, x_4, x_2);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___System_Uri_escapeUri_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___System_Uri_escapeUri_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_System_Uri_escapeUri___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_Uri_escapeUri(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_Uri_UriEscape_decodeUri(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_System_Uri_unescapeUri___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_System_Uri_unescapeUri(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_mapAux___at___System_Uri_pathToUri_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; uint8_t x_8; 
x_8 = lean_string_utf8_at_end(x_2, x_1);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get(x_2, x_1);
x_10 = lean_unsigned_to_nat(92u);
x_11 = l_Char_ofNat(x_10);
x_12 = l_instDecidableEqChar(x_9, x_11);
if (x_12 == 0)
{
x_3 = x_9;
goto block_7;
}
else
{
lean_object* x_13; uint32_t x_14; 
x_13 = lean_unsigned_to_nat(47u);
x_14 = l_Char_ofNat(x_13);
x_3 = x_14;
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
LEAN_EXPORT lean_object* l_System_Uri_pathToUri___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_string_utf8_byte_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_String_foldlAux___at___System_Uri_escapeUri_spec__0(x_1, x_4, x_5, x_3);
lean_dec(x_4);
x_7 = lean_mk_string_unchecked("/", 1, 1);
x_8 = lean_string_utf8_byte_size(x_6);
lean_inc(x_6);
x_9 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_5);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Substring_nextn(x_9, x_10, x_5);
lean_dec(x_9);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_string_utf8_byte_size(x_7);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_13);
x_15 = l_Substring_beq(x_12, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_mk_string_unchecked("file:///", 8, 8);
x_17 = lean_string_append(x_16, x_6);
lean_dec(x_6);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_mk_string_unchecked("file://", 7, 7);
x_19 = lean_string_append(x_18, x_6);
lean_dec(x_6);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_pathToUri(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_8; uint8_t x_9; uint8_t x_20; 
x_8 = l_System_FilePath_normalize(x_1);
x_20 = l_System_Platform_isWindows;
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_System_Uri_pathToUri___lam__0(x_8, x_21);
lean_dec(x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_string_length(x_8);
x_25 = lean_nat_dec_le(x_23, x_24);
lean_dec(x_24);
if (x_25 == 0)
{
x_9 = x_25;
goto block_19;
}
else
{
lean_object* x_26; lean_object* x_27; uint32_t x_28; uint32_t x_29; uint8_t x_30; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_unsigned_to_nat(65u);
x_28 = lean_uint32_of_nat(x_27);
x_29 = lean_string_utf8_get(x_8, x_26);
x_30 = lean_uint32_dec_le(x_28, x_29);
if (x_30 == 0)
{
x_9 = x_30;
goto block_19;
}
else
{
lean_object* x_31; uint32_t x_32; uint8_t x_33; 
x_31 = lean_unsigned_to_nat(90u);
x_32 = lean_uint32_of_nat(x_31);
x_33 = lean_uint32_dec_le(x_29, x_32);
x_9 = x_33;
goto block_19;
}
}
}
block_7:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_mapAux___at___System_Uri_pathToUri_spec__0(x_3, x_2);
x_5 = lean_box(0);
x_6 = l_System_Uri_pathToUri___lam__0(x_4, x_5);
lean_dec(x_4);
return x_6;
}
block_19:
{
if (x_9 == 0)
{
x_2 = x_8;
goto block_7;
}
else
{
lean_object* x_10; uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_string_utf8_get(x_8, x_10);
x_12 = lean_unsigned_to_nat(58u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_11, x_13);
if (x_14 == 0)
{
x_2 = x_8;
goto block_7;
}
else
{
lean_object* x_15; uint32_t x_16; uint32_t x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_string_utf8_get(x_8, x_15);
x_17 = l_Char_toLower(x_16);
x_18 = lean_string_utf8_set(x_8, x_15, x_17);
x_2 = x_18;
goto block_7;
}
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_pathToUri___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_System_Uri_pathToUri___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___System_Uri_fileUriToPath_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_1);
lean_inc(x_1);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_unsigned_to_nat(7u);
x_9 = l_Substring_nextn(x_7, x_8, x_5);
lean_dec(x_7);
x_10 = lean_mk_string_unchecked("file://", 7, 7);
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = lean_nat_dec_lt(x_4, x_3);
if (x_12 == 0)
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_4;
}
else
{
uint32_t x_13; lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_13 = lean_string_utf8_get(x_2, x_4);
x_14 = lean_unsigned_to_nat(47u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_13, x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_17, 1, x_5);
lean_ctor_set(x_17, 2, x_9);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_5);
lean_ctor_set(x_18, 2, x_11);
x_19 = l_Substring_beq(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_20; 
x_20 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_20;
goto _start;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_System_Uri_fileUriToPath_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_2 = lean_mk_string_unchecked("file://", 7, 7);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_string_utf8_byte_size(x_1);
lean_inc(x_1);
x_5 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
x_6 = lean_unsigned_to_nat(7u);
x_7 = l_Substring_nextn(x_5, x_6, x_3);
lean_dec(x_5);
lean_inc(x_1);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_string_utf8_byte_size(x_2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_3);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_beq(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_1);
x_12 = lean_box(0);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_36; lean_object* x_39; uint8_t x_40; uint8_t x_49; uint8_t x_65; 
x_13 = l_System_Uri_UriEscape_decodeUri(x_1);
x_14 = lean_string_utf8_byte_size(x_13);
lean_inc(x_14);
lean_inc(x_13);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_3);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Substring_nextn(x_15, x_6, x_3);
lean_dec(x_15);
x_17 = lean_string_utf8_extract(x_13, x_16, x_14);
lean_dec(x_14);
lean_dec(x_16);
lean_dec(x_13);
x_18 = lean_string_utf8_byte_size(x_17);
x_19 = l_Substring_takeWhileAux___at___System_Uri_fileUriToPath_x3f_spec__0(x_1, x_17, x_18, x_3);
x_20 = lean_string_utf8_extract(x_17, x_19, x_18);
lean_dec(x_18);
lean_dec(x_19);
lean_dec(x_17);
x_65 = l_System_Platform_isWindows;
if (x_65 == 0)
{
x_49 = x_65;
goto block_64;
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_string_length(x_20);
x_68 = lean_nat_dec_le(x_66, x_67);
lean_dec(x_67);
x_49 = x_68;
goto block_64;
}
block_35:
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_string_utf8_get(x_20, x_21);
x_23 = lean_unsigned_to_nat(58u);
x_24 = l_Char_ofNat(x_23);
x_25 = l_instDecidableEqChar(x_22, x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_26, 0, x_20);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_string_utf8_byte_size(x_20);
lean_inc(x_28);
lean_inc(x_20);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_3);
lean_ctor_set(x_29, 2, x_28);
x_30 = l_Substring_nextn(x_29, x_27, x_3);
lean_dec(x_29);
x_31 = lean_string_utf8_extract(x_20, x_30, x_28);
lean_dec(x_28);
lean_dec(x_30);
lean_dec(x_20);
x_32 = lean_alloc_closure((void*)(l_Char_toUpper___boxed), 1, 0);
x_33 = l_String_modify(x_31, x_3, x_32);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
return x_34;
}
}
block_38:
{
if (x_36 == 0)
{
lean_object* x_37; 
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_20);
return x_37;
}
else
{
goto block_35;
}
}
block_48:
{
if (x_40 == 0)
{
lean_object* x_41; uint32_t x_42; uint32_t x_43; uint8_t x_44; 
x_41 = lean_unsigned_to_nat(97u);
x_42 = lean_uint32_of_nat(x_41);
x_43 = lean_string_utf8_get(x_20, x_39);
x_44 = lean_uint32_dec_le(x_42, x_43);
if (x_44 == 0)
{
x_36 = x_44;
goto block_38;
}
else
{
lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(122u);
x_46 = lean_uint32_of_nat(x_45);
x_47 = lean_uint32_dec_le(x_43, x_46);
x_36 = x_47;
goto block_38;
}
}
else
{
goto block_35;
}
}
block_64:
{
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_20);
return x_50;
}
else
{
uint32_t x_51; lean_object* x_52; uint32_t x_53; uint8_t x_54; 
x_51 = lean_string_utf8_get(x_20, x_3);
x_52 = lean_unsigned_to_nat(47u);
x_53 = l_Char_ofNat(x_52);
x_54 = l_instDecidableEqChar(x_51, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_55, 0, x_20);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; uint32_t x_58; uint32_t x_59; uint8_t x_60; 
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_unsigned_to_nat(65u);
x_58 = lean_uint32_of_nat(x_57);
x_59 = lean_string_utf8_get(x_20, x_56);
x_60 = lean_uint32_dec_le(x_58, x_59);
if (x_60 == 0)
{
x_39 = x_56;
x_40 = x_60;
goto block_48;
}
else
{
lean_object* x_61; uint32_t x_62; uint8_t x_63; 
x_61 = lean_unsigned_to_nat(90u);
x_62 = lean_uint32_of_nat(x_61);
x_63 = lean_uint32_dec_le(x_59, x_62);
x_39 = x_56;
x_40 = x_63;
goto block_48;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Substring_takeWhileAux___at___System_Uri_fileUriToPath_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Substring_takeWhileAux___at___System_Uri_fileUriToPath_x3f_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
lean_object* initialize_Init_Data_String_Extra(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin, lean_object*);
lean_object* initialize_Init_System_FilePath(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_System_Uri(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Extra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_FilePath(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_System_Uri_UriEscape_zero = _init_l_System_Uri_UriEscape_zero();
l_System_Uri_UriEscape_nine = _init_l_System_Uri_UriEscape_nine();
l_System_Uri_UriEscape_lettera = _init_l_System_Uri_UriEscape_lettera();
l_System_Uri_UriEscape_letterf = _init_l_System_Uri_UriEscape_letterf();
l_System_Uri_UriEscape_letterA = _init_l_System_Uri_UriEscape_letterA();
l_System_Uri_UriEscape_letterF = _init_l_System_Uri_UriEscape_letterF();
l_System_Uri_UriEscape_rfc3986ReservedChars = _init_l_System_Uri_UriEscape_rfc3986ReservedChars();
lean_mark_persistent(l_System_Uri_UriEscape_rfc3986ReservedChars);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
