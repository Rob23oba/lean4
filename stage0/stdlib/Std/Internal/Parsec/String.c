// Lean compiler output
// Module: Std.Internal.Parsec.String
// Imports: Std.Internal.Parsec.Basic
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__2___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos;
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__2(lean_object*);
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__5(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object*);
lean_object* l_String_Iterator_forward(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__5___boxed(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__3___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__3(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__1(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_next(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_5);
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_inc(x_6);
lean_dec(x_1);
x_8 = lean_string_utf8_next(x_6, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_get(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_string_utf8_byte_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__4(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_1);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_string_utf8_next_fast(x_4, x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_6);
return x_1;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_string_utf8_next_fast(x_7, x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
}
}
LEAN_EXPORT uint32_t l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_string_utf8_get_fast(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__1), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__2___boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__3___boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__4), 2, 0);
x_6 = lean_alloc_closure((void*)(l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__5___boxed), 2, 0);
x_7 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_3);
lean_ctor_set(x_7, 3, x_4);
lean_ctor_set(x_7, 4, x_5);
lean_ctor_set(x_7, 5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__2___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__2(x_1);
lean_dec(x_1);
x_3 = lean_box_uint32(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__3___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__3(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__5___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = l_Std_Internal_Parsec_String_instInputIteratorCharPos___lam__5(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box_uint32(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_apply_1(x_1, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
x_10 = lean_mk_string_unchecked("offset ", 7, 7);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_unsigned_to_nat(120u);
x_15 = lean_format_pretty(x_13, x_14, x_3, x_3);
x_16 = lean_string_append(x_10, x_15);
lean_dec(x_15);
x_17 = lean_mk_string_unchecked(": ", 2, 2);
x_18 = lean_string_append(x_16, x_17);
lean_dec(x_17);
x_19 = lean_string_append(x_18, x_9);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_Parser_run(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_Internal_Parsec_String_Parser_run___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_23; uint8_t x_24; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_length(x_1);
lean_inc(x_2);
x_6 = l_String_Iterator_forward(x_2, x_5);
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
x_23 = lean_string_dec_eq(x_3, x_17);
lean_dec(x_17);
x_24 = l_instDecidableNot___redArg(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_nat_dec_lt(x_18, x_4);
x_19 = x_25;
goto block_22;
}
else
{
x_19 = x_24;
goto block_22;
}
block_16:
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
x_9 = lean_mk_string_unchecked("expected: ", 10, 10);
x_10 = lean_string_append(x_9, x_1);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_2, 1);
lean_dec(x_13);
x_14 = lean_ctor_get(x_2, 0);
lean_dec(x_14);
lean_ctor_set(x_2, 1, x_7);
lean_ctor_set(x_2, 0, x_6);
return x_2;
}
else
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_7);
return x_15;
}
}
}
block_22:
{
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_string_utf8_extract(x_3, x_4, x_18);
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
x_7 = x_20;
goto block_16;
}
else
{
lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_4);
lean_dec(x_3);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_7 = x_21;
goto block_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pstring___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_String_pstring(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_String_pstring(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 1);
lean_dec(x_5);
x_6 = lean_box(0);
lean_ctor_set(x_3, 1, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_3);
if (x_10 == 0)
{
return x_3;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_3);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipString___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Internal_Parsec_String_skipString(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = l_instDecidableEqChar(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_mk_string_unchecked("expected: '", 11, 11);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = lean_string_push(x_12, x_1);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("'", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_21);
x_22 = lean_box_uint32(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_24 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box_uint32(x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_pchar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_String_pchar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar(uint32_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_mk_string_unchecked("unexpected end of input", 23, 23);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
uint32_t x_9; uint8_t x_10; 
x_9 = lean_string_utf8_get_fast(x_3, x_4);
x_10 = l_instDecidableEqChar(x_9, x_1);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_mk_string_unchecked("expected: '", 11, 11);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = lean_string_push(x_12, x_1);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("'", 1, 1);
x_16 = lean_string_append(x_14, x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_2, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_2, 0);
lean_dec(x_20);
x_21 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_2, 1, x_21);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_2);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_24 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_skipChar___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; 
x_3 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_4 = l_Std_Internal_Parsec_String_skipChar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
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
uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_11 = lean_string_utf8_get_fast(x_5, x_6);
x_12 = lean_unsigned_to_nat(48u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_dec_le(x_13, x_11);
if (x_14 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(57u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_uint32_dec_le(x_11, x_16);
if (x_17 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
x_21 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_21);
x_22 = lean_box_uint32(x_11);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_24 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_box_uint32(x_11);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
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
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(uint32_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint32_t x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_uint32_to_nat(x_1);
x_3 = lean_unsigned_to_nat(48u);
x_4 = l_Char_ofNat(x_3);
x_5 = lean_uint32_to_nat(x_4);
x_6 = lean_nat_sub(x_2, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; lean_object* x_3; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitToNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_string_utf8_byte_size(x_3);
x_6 = lean_nat_dec_lt(x_4, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_1);
return x_7;
}
else
{
uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_string_utf8_get(x_3, x_4);
x_9 = lean_unsigned_to_nat(48u);
x_10 = l_Char_ofNat(x_9);
x_11 = lean_uint32_dec_le(x_10, x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_1);
return x_12;
}
else
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(57u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_uint32_dec_le(x_8, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_4);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_1);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_1);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_18 = lean_ctor_get(x_1, 1);
lean_dec(x_18);
x_19 = lean_ctor_get(x_1, 0);
lean_dec(x_19);
x_20 = lean_uint32_to_nat(x_8);
x_21 = lean_uint32_to_nat(x_10);
x_22 = lean_nat_sub(x_20, x_21);
lean_dec(x_21);
lean_dec(x_20);
x_23 = lean_unsigned_to_nat(10u);
x_24 = lean_nat_mul(x_2, x_23);
lean_dec(x_2);
x_25 = lean_nat_add(x_24, x_22);
lean_dec(x_22);
lean_dec(x_24);
x_26 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
lean_ctor_set(x_1, 1, x_26);
x_2 = x_25;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_28 = lean_uint32_to_nat(x_8);
x_29 = lean_uint32_to_nat(x_10);
x_30 = lean_nat_sub(x_28, x_29);
lean_dec(x_29);
lean_dec(x_28);
x_31 = lean_unsigned_to_nat(10u);
x_32 = lean_nat_mul(x_2, x_31);
lean_dec(x_2);
x_33 = lean_nat_add(x_32, x_30);
lean_dec(x_30);
lean_dec(x_32);
x_34 = lean_string_utf8_next_fast(x_3, x_4);
lean_dec(x_4);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
x_1 = x_35;
x_2 = x_33;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_2, x_1);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_ctor_set(x_3, 1, x_5);
lean_ctor_set(x_3, 0, x_6);
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_3);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_digits(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
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
uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_11 = lean_string_utf8_get_fast(x_5, x_6);
x_12 = lean_unsigned_to_nat(48u);
x_13 = l_Char_ofNat(x_12);
x_14 = lean_uint32_dec_le(x_13, x_11);
if (x_14 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(57u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_uint32_dec_le(x_11, x_16);
if (x_17 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
goto block_4;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_1);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_ctor_get(x_1, 1);
lean_dec(x_19);
x_20 = lean_ctor_get(x_1, 0);
lean_dec(x_20);
x_21 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
lean_ctor_set(x_1, 1, x_21);
x_22 = lean_uint32_to_nat(x_11);
x_23 = lean_uint32_to_nat(x_13);
x_24 = lean_nat_sub(x_22, x_23);
lean_dec(x_23);
lean_dec(x_22);
x_25 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_1, x_24);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_25, 1);
lean_ctor_set(x_25, 1, x_27);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 0);
x_30 = lean_ctor_get(x_25, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_25);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_32 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_uint32_to_nat(x_11);
x_35 = lean_uint32_to_nat(x_13);
x_36 = lean_nat_sub(x_34, x_35);
lean_dec(x_35);
lean_dec(x_34);
x_37 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_digitsCore_go(x_33, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_37)) {
 lean_ctor_release(x_37, 0);
 lean_ctor_release(x_37, 1);
 x_40 = x_37;
} else {
 lean_dec_ref(x_37);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_38);
return x_41;
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
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_hexDigit(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
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
uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_40; uint32_t x_41; uint8_t x_42; 
x_11 = lean_string_utf8_get_fast(x_5, x_6);
x_12 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_40 = lean_unsigned_to_nat(48u);
x_41 = l_Char_ofNat(x_40);
x_42 = lean_uint32_dec_le(x_41, x_11);
if (x_42 == 0)
{
goto block_39;
}
else
{
lean_object* x_43; uint32_t x_44; uint8_t x_45; 
x_43 = lean_unsigned_to_nat(57u);
x_44 = l_Char_ofNat(x_43);
x_45 = lean_uint32_dec_le(x_11, x_44);
if (x_45 == 0)
{
goto block_39;
}
else
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_1);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_1, 1);
lean_dec(x_47);
x_48 = lean_ctor_get(x_1, 0);
lean_dec(x_48);
x_49 = lean_box_uint32(x_11);
lean_ctor_set(x_1, 1, x_49);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_50 = lean_box_uint32(x_11);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_13);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
block_26:
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(65u);
x_15 = l_Char_ofNat(x_14);
x_16 = lean_uint32_dec_le(x_15, x_11);
if (x_16 == 0)
{
lean_dec(x_13);
goto block_4;
}
else
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(70u);
x_18 = l_Char_ofNat(x_17);
x_19 = lean_uint32_dec_le(x_11, x_18);
if (x_19 == 0)
{
lean_dec(x_13);
goto block_4;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_box_uint32(x_11);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_box_uint32(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
block_39:
{
lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(97u);
x_28 = l_Char_ofNat(x_27);
x_29 = lean_uint32_dec_le(x_28, x_11);
if (x_29 == 0)
{
goto block_26;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(102u);
x_31 = l_Char_ofNat(x_30);
x_32 = lean_uint32_dec_le(x_11, x_31);
if (x_32 == 0)
{
goto block_26;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_1, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_36 = lean_box_uint32(x_11);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_box_uint32(x_11);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("hex digit expected", 18, 18);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_asciiLetter(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
x_7 = lean_string_utf8_byte_size(x_5);
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
uint32_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_27; uint32_t x_28; uint8_t x_29; 
x_11 = lean_string_utf8_get_fast(x_5, x_6);
x_12 = lean_string_utf8_next_fast(x_5, x_6);
lean_dec(x_6);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_27 = lean_unsigned_to_nat(65u);
x_28 = l_Char_ofNat(x_27);
x_29 = lean_uint32_dec_le(x_28, x_11);
if (x_29 == 0)
{
goto block_26;
}
else
{
lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_30 = lean_unsigned_to_nat(90u);
x_31 = l_Char_ofNat(x_30);
x_32 = lean_uint32_dec_le(x_11, x_31);
if (x_32 == 0)
{
goto block_26;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_1);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_1, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_1, 0);
lean_dec(x_35);
x_36 = lean_box_uint32(x_11);
lean_ctor_set(x_1, 1, x_36);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_box_uint32(x_11);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_26:
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(97u);
x_15 = l_Char_ofNat(x_14);
x_16 = lean_uint32_dec_le(x_15, x_11);
if (x_16 == 0)
{
lean_dec(x_13);
goto block_4;
}
else
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(122u);
x_18 = l_Char_ofNat(x_17);
x_19 = lean_uint32_dec_le(x_11, x_18);
if (x_19 == 0)
{
lean_dec(x_13);
goto block_4;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_1);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_1, 1);
lean_dec(x_21);
x_22 = lean_ctor_get(x_1, 0);
lean_dec(x_22);
x_23 = lean_box_uint32(x_11);
lean_ctor_set(x_1, 1, x_23);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_1);
x_24 = lean_box_uint32(x_11);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_13);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_mk_string_unchecked("ASCII letter expected", 21, 21);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_8; uint8_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
x_8 = lean_string_utf8_byte_size(x_2);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
uint32_t x_10; lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_10 = lean_string_utf8_get_fast(x_2, x_3);
x_11 = lean_unsigned_to_nat(9u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_10, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(10u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_10, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(13u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_10, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(32u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_10, x_21);
if (x_22 == 0)
{
lean_dec(x_3);
lean_dec(x_2);
return x_1;
}
else
{
lean_dec(x_1);
goto block_7;
}
}
else
{
lean_dec(x_1);
goto block_7;
}
}
else
{
lean_dec(x_1);
goto block_7;
}
}
else
{
lean_dec(x_1);
goto block_7;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_string_utf8_next_fast(x_2, x_3);
lean_dec(x_3);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_4);
x_1 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_ws(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = l___private_Std_Internal_Parsec_String_0__Std_Internal_Parsec_String_skipWs(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Internal_Parsec_String_take(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_26; uint8_t x_27; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_5 = l_String_Iterator_forward(x_2, x_1);
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_5, 1);
lean_inc(x_21);
x_26 = lean_string_dec_eq(x_3, x_20);
lean_dec(x_20);
x_27 = l_instDecidableNot___redArg(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
x_28 = lean_nat_dec_lt(x_21, x_4);
x_22 = x_28;
goto block_25;
}
else
{
x_22 = x_27;
goto block_25;
}
block_19:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_string_length(x_6);
x_8 = lean_nat_dec_eq(x_7, x_1);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_mk_string_unchecked("expected: ", 10, 10);
x_10 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_11 = lean_string_append(x_9, x_10);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked(" codepoints", 11, 11);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_2);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
uint8_t x_15; 
lean_dec(x_1);
x_15 = !lean_is_exclusive(x_2);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_2, 1);
lean_dec(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_dec(x_17);
lean_ctor_set(x_2, 1, x_6);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_18; 
lean_dec(x_2);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_5);
lean_ctor_set(x_18, 1, x_6);
return x_18;
}
}
}
block_25:
{
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_string_utf8_extract(x_3, x_4, x_21);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
x_6 = x_23;
goto block_19;
}
else
{
lean_object* x_24; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_mk_string_unchecked("", 0, 0);
x_6 = x_24;
goto block_19;
}
}
}
}
lean_object* initialize_Std_Internal_Parsec_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Internal_Parsec_String(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Parsec_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Internal_Parsec_String_instInputIteratorCharPos = _init_l_Std_Internal_Parsec_String_instInputIteratorCharPos();
lean_mark_persistent(l_Std_Internal_Parsec_String_instInputIteratorCharPos);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
