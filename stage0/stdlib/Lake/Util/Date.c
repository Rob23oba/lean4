// Lean compiler output
// Module: Lake.Util.Date
// Imports: Init.Data.Ord
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
uint8_t l_Ord_instDecidableRelLe___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_zpad(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___Lake_lpad_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Date_ofString_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___Lake_lpad_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instLE;
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Date_ofString_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lpad(lean_object*, uint32_t, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l_String_split___at___Lake_Date_ofString_x3f_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_reprDate___redArg____x40_Lake_Util_Date___hyg_372_(lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_ofValid_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instToString;
LEAN_EXPORT lean_object* l_String_split___at___Lake_Date_ofString_x3f_spec__0(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instInhabitedDate;
LEAN_EXPORT lean_object* l_Lake_Date_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instLT;
LEAN_EXPORT lean_object* l_Lake_Date_maxDay(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprDate;
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rpad___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_reprDate____x40_Lake_Util_Date___hyg_372_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMax;
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_reprDate____x40_Lake_Util_Date___hyg_372____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_zpad___boxed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_mod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMin;
LEAN_EXPORT uint8_t l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_rpad(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_decEqDate____x40_Lake_Util_Date___hyg_91____boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Util_Date_0__Lake_decEqDate____x40_Lake_Util_Date___hyg_91_(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f(lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_lpad___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instOrdDate;
LEAN_EXPORT lean_object* l_Lake_Date_maxDay___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___Lake_lpad_spec__0(uint32_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_2, x_6);
lean_dec(x_2);
x_8 = lean_string_push(x_3, x_1);
x_2 = x_7;
x_3 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_lpad(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_mk_string_unchecked("", 0, 0);
x_5 = lean_string_length(x_1);
x_6 = lean_nat_sub(x_3, x_5);
lean_dec(x_5);
x_7 = l_Nat_repeatTR_loop___at___Lake_lpad_spec__0(x_2, x_6, x_4);
x_8 = lean_string_append(x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Nat_repeatTR_loop___at___Lake_lpad_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_5 = l_Nat_repeatTR_loop___at___Lake_lpad_spec__0(x_4, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_lpad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lake_lpad(x_1, x_4, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_rpad(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_string_length(x_1);
x_5 = lean_nat_sub(x_3, x_4);
lean_dec(x_4);
x_6 = l_Nat_repeatTR_loop___at___Lake_lpad_spec__0(x_2, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_rpad___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lake_rpad(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_zpad(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint32_t x_5; lean_object* x_6; 
x_3 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_4 = lean_unsigned_to_nat(48u);
x_5 = l_Char_ofNat(x_4);
x_6 = l_Lake_lpad(x_3, x_5, x_2);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_zpad___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_zpad(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instInhabitedDate() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Date_0__Lake_decEqDate____x40_Lake_Util_Date___hyg_91_(lean_object* x_1, lean_object* x_2) {
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
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_decEqDate____x40_Lake_Util_Date___hyg_91____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Util_Date_0__Lake_decEqDate____x40_Lake_Util_Date___hyg_91_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqDate(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Lake_Util_Date_0__Lake_decEqDate____x40_Lake_Util_Date___hyg_91_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqDate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_instDecidableEqDate(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
x_9 = lean_nat_dec_lt(x_3, x_6);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_nat_dec_eq(x_3, x_6);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(2);
x_12 = lean_unbox(x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_4, x_7);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_nat_dec_eq(x_4, x_7);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(2);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_lt(x_5, x_8);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = lean_nat_dec_eq(x_5, x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(2);
x_20 = lean_unbox(x_19);
return x_20;
}
else
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
return x_22;
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_box(0);
x_24 = lean_unbox(x_23);
return x_24;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_instOrdDate() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_reprDate___redArg____x40_Lake_Util_Date___hyg_372_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("year", 4, 4);
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
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
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
x_25 = lean_mk_string_unchecked("month", 5, 5);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_8);
x_28 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_8);
x_29 = lean_unsigned_to_nat(9u);
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
x_40 = lean_mk_string_unchecked("day", 3, 3);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_8);
x_44 = lean_unsigned_to_nat(7u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
lean_dec(x_1);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
x_49 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_unbox(x_16);
lean_ctor_set_uint8(x_50, sizeof(void*)*1, x_51);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_43);
lean_ctor_set(x_52, 1, x_50);
x_53 = lean_mk_string_unchecked(" }", 2, 2);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_to_int(x_54);
x_56 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_56, 0, x_2);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_52);
x_58 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_58, 0, x_53);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_55);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_unbox(x_16);
lean_ctor_set_uint8(x_61, sizeof(void*)*1, x_62);
return x_61;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_reprDate____x40_Lake_Util_Date___hyg_372_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Date_0__Lake_reprDate___redArg____x40_Lake_Util_Date___hyg_372_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Util_Date_0__Lake_reprDate____x40_Lake_Util_Date___hyg_372____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Util_Date_0__Lake_reprDate____x40_Lake_Util_Date___hyg_372_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instReprDate() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Date_0__Lake_reprDate____x40_Lake_Util_Date___hyg_372____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Date_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lake_Date_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMin___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lake_Date_instMin() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293____boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_Date_instMin___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_instMax___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
static lean_object* _init_l_Lake_Date_instMax() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Util_Date_0__Lake_ordDate____x40_Lake_Util_Date___hyg_293____boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_Date_instMax___lam__0), 3, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(7u);
x_6 = lean_nat_dec_le(x_2, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(31u);
x_8 = lean_nat_mod(x_2, x_3);
x_9 = lean_nat_sub(x_7, x_8);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_unsigned_to_nat(30u);
x_11 = lean_nat_mod(x_2, x_3);
x_12 = lean_nat_add(x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_unsigned_to_nat(4u);
x_14 = lean_nat_mod(x_1, x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_14, x_15);
lean_dec(x_14);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_unsigned_to_nat(28u);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; 
x_18 = lean_unsigned_to_nat(100u);
x_19 = lean_nat_mod(x_1, x_18);
x_20 = lean_nat_dec_eq(x_19, x_15);
lean_dec(x_19);
x_21 = l_instDecidableNot___redArg(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_unsigned_to_nat(400u);
x_23 = lean_nat_mod(x_1, x_22);
x_24 = lean_nat_dec_eq(x_23, x_15);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_unsigned_to_nat(28u);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_unsigned_to_nat(29u);
return x_26;
}
}
else
{
lean_object* x_27; 
x_27 = lean_unsigned_to_nat(29u);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Date_maxDay___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Date_maxDay(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofValid_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_dec_le(x_4, x_2);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_unsigned_to_nat(12u);
x_8 = lean_nat_dec_le(x_2, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
return x_9;
}
else
{
uint8_t x_10; 
x_10 = lean_nat_dec_le(x_4, x_3);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lake_Date_maxDay(x_1, x_2);
x_13 = lean_nat_dec_le(x_3, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_3);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_15);
return x_16;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Date_ofString_x3f_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_1, x_3);
if (x_5 == 0)
{
uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_string_utf8_get(x_1, x_3);
x_7 = lean_unsigned_to_nat(45u);
x_8 = l_Char_ofNat(x_7);
x_9 = l_instDecidableEqChar(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_string_utf8_next(x_1, x_3);
x_13 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_4);
lean_inc(x_12);
x_2 = x_12;
x_3 = x_12;
x_4 = x_14;
goto _start;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_string_utf8_extract(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_4);
x_18 = l_List_reverse___redArg(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_Date_ofString_x3f_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_box(0);
x_4 = l_String_splitAux___at___String_split___at___Lake_Date_ofString_x3f_spec__0_spec__0(x_1, x_2, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lake_Date_ofString_x3f_spec__0(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_ctor_get(x_4, 0);
lean_inc(x_10);
lean_dec(x_4);
x_11 = lean_ctor_get(x_6, 0);
lean_inc(x_11);
lean_dec(x_6);
x_12 = l_String_toNat_x3f(x_9);
lean_dec(x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_10);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_String_toNat_x3f(x_10);
lean_dec(x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_11);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_String_toNat_x3f(x_11);
lean_dec(x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_14);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lake_Date_ofValid_x3f(x_14, x_17, x_20);
return x_21;
}
}
}
}
else
{
lean_object* x_22; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
x_22 = lean_box(0);
return x_22;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_splitAux___at___String_split___at___Lake_Date_ofString_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_splitAux___at___String_split___at___Lake_Date_ofString_x3f_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_String_split___at___Lake_Date_ofString_x3f_spec__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_String_split___at___Lake_Date_ofString_x3f_spec__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_ofString_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Date_ofString_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Date_toString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_unsigned_to_nat(4u);
x_4 = l_Lake_zpad(x_2, x_3);
x_5 = lean_mk_string_unchecked("-", 1, 1);
x_6 = lean_string_append(x_4, x_5);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(2u);
x_9 = l_Lake_zpad(x_7, x_8);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_10, x_5);
lean_dec(x_5);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lake_zpad(x_12, x_8);
x_14 = lean_string_append(x_11, x_13);
lean_dec(x_13);
return x_14;
}
}
static lean_object* _init_l_Lake_Date_instToString() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Date_toString), 1, 0);
return x_1;
}
}
lean_object* initialize_Init_Data_Ord(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Date(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Ord(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instInhabitedDate = _init_l_Lake_instInhabitedDate();
lean_mark_persistent(l_Lake_instInhabitedDate);
l_Lake_instOrdDate = _init_l_Lake_instOrdDate();
lean_mark_persistent(l_Lake_instOrdDate);
l_Lake_instReprDate = _init_l_Lake_instReprDate();
lean_mark_persistent(l_Lake_instReprDate);
l_Lake_Date_instLT = _init_l_Lake_Date_instLT();
lean_mark_persistent(l_Lake_Date_instLT);
l_Lake_Date_instLE = _init_l_Lake_Date_instLE();
lean_mark_persistent(l_Lake_Date_instLE);
l_Lake_Date_instMin = _init_l_Lake_Date_instMin();
lean_mark_persistent(l_Lake_Date_instMin);
l_Lake_Date_instMax = _init_l_Lake_Date_instMax();
lean_mark_persistent(l_Lake_Date_instMax);
l_Lake_Date_instToString = _init_l_Lake_Date_instToString();
lean_mark_persistent(l_Lake_Date_instToString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
