// Lean compiler output
// Module: Std.Time.Zoned.TimeZone
// Imports: Std.Time.Zoned.Offset
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
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_GMT;
lean_object* l_String_quote(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone___redArg____x40_Std_Time_Zoned_TimeZone___hyg_54_(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_decEqTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_152____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_54_(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
lean_object* l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instReprTimeZone;
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_TimeZone_0__Std_Time_decEqTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_152_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone___redArg____x40_Std_Time_Zoned_TimeZone___hyg_54____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Std_Time_TimeZone_Offset_zero;
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_UTC;
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_54____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object*, lean_object*);
lean_object* l_Std_Time_TimeZone_Offset_ofHours(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedTimeZone;
static lean_object* _init_l_Std_Time_instInhabitedTimeZone() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_nat_to_int(x_1);
x_3 = lean_mk_string_unchecked("", 0, 0);
x_4 = lean_box(0);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone___redArg____x40_Std_Time_Zoned_TimeZone___hyg_54_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_76; 
x_2 = lean_mk_string_unchecked("{ ", 2, 2);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("offset", 6, 6);
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
x_10 = lean_unsigned_to_nat(10u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_ctor_get(x_1, 0);
x_13 = l___private_Std_Time_Zoned_Offset_0__Std_Time_TimeZone_reprOffset___redArg____x40_Std_Time_Zoned_Offset___hyg_187_(x_12);
x_14 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_16, 0, x_14);
x_17 = lean_unbox(x_15);
lean_ctor_set_uint8(x_16, sizeof(void*)*1, x_17);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_16);
x_19 = lean_mk_string_unchecked(",", 1, 1);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_20);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("name", 4, 4);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_8);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_8);
x_28 = lean_unsigned_to_nat(8u);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_ctor_get(x_1, 1);
x_31 = l_String_quote(x_30);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_unbox(x_15);
lean_ctor_set_uint8(x_34, sizeof(void*)*1, x_35);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_27);
lean_ctor_set(x_36, 1, x_34);
lean_inc(x_20);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_20);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_22);
x_39 = lean_mk_string_unchecked("abbreviation", 12, 12);
x_40 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_8);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = lean_unsigned_to_nat(16u);
x_44 = lean_nat_to_int(x_43);
x_45 = lean_ctor_get(x_1, 2);
x_46 = l_String_quote(x_45);
x_47 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_unbox(x_15);
lean_ctor_set_uint8(x_49, sizeof(void*)*1, x_50);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_49);
x_52 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_20);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_22);
x_54 = lean_mk_string_unchecked("isDST", 5, 5);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_8);
x_58 = lean_unsigned_to_nat(9u);
x_59 = lean_nat_to_int(x_58);
x_76 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_mk_string_unchecked("false", 5, 5);
x_78 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_60 = x_78;
goto block_75;
}
else
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_mk_string_unchecked("true", 4, 4);
x_80 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_60 = x_80;
goto block_75;
}
block_75:
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_unbox(x_15);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_57);
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
x_74 = lean_unbox(x_15);
lean_ctor_set_uint8(x_73, sizeof(void*)*1, x_74);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_54_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone___redArg____x40_Std_Time_Zoned_TimeZone___hyg_54_(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone___redArg____x40_Std_Time_Zoned_TimeZone___hyg_54____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone___redArg____x40_Std_Time_Zoned_TimeZone___hyg_54_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_54____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_54_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static lean_object* _init_l_Std_Time_instReprTimeZone() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Std_Time_Zoned_TimeZone_0__Std_Time_reprTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_54____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Std_Time_Zoned_TimeZone_0__Std_Time_decEqTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_152_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*3);
x_11 = lean_int_dec_eq(x_3, x_7);
if (x_11 == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_string_dec_eq(x_4, x_8);
if (x_12 == 0)
{
return x_12;
}
else
{
uint8_t x_13; 
x_13 = lean_string_dec_eq(x_5, x_9);
if (x_13 == 0)
{
return x_13;
}
else
{
if (x_6 == 0)
{
if (x_10 == 0)
{
return x_13;
}
else
{
return x_6;
}
}
else
{
return x_10;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Time_Zoned_TimeZone_0__Std_Time_decEqTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_152____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Std_Time_Zoned_TimeZone_0__Std_Time_decEqTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_152_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqTimeZone(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l___private_Std_Time_Zoned_TimeZone_0__Std_Time_decEqTimeZone____x40_Std_Time_Zoned_TimeZone___hyg_152_(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqTimeZone___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_instDecidableEqTimeZone(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Std_Time_TimeZone_UTC() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_1 = l_Std_Time_TimeZone_Offset_zero;
x_2 = lean_mk_string_unchecked("UTC", 3, 3);
x_3 = lean_box(0);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_2);
x_5 = lean_unbox(x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*3, x_5);
return x_4;
}
}
static lean_object* _init_l_Std_Time_TimeZone_GMT() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_1 = l_Std_Time_TimeZone_Offset_zero;
x_2 = lean_mk_string_unchecked("Greenwich Mean Time", 19, 19);
x_3 = lean_mk_string_unchecked("GMT", 3, 3);
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 2, x_3);
x_6 = lean_unbox(x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_6);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Std_Time_TimeZone_Offset_ofHours(x_3);
x_6 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_2);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofHours___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Std_Time_TimeZone_ofHours(x_1, x_2, x_3, x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 2, x_2);
lean_ctor_set_uint8(x_5, sizeof(void*)*3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_ofSeconds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_4);
lean_dec(x_4);
x_6 = l_Std_Time_TimeZone_ofSeconds(x_1, x_2, x_3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_TimeZone_toSeconds___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Time_TimeZone_toSeconds(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Std_Time_Zoned_Offset(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Zoned_TimeZone(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Time_Zoned_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Time_instInhabitedTimeZone = _init_l_Std_Time_instInhabitedTimeZone();
lean_mark_persistent(l_Std_Time_instInhabitedTimeZone);
l_Std_Time_instReprTimeZone = _init_l_Std_Time_instReprTimeZone();
lean_mark_persistent(l_Std_Time_instReprTimeZone);
l_Std_Time_TimeZone_UTC = _init_l_Std_Time_TimeZone_UTC();
lean_mark_persistent(l_Std_Time_TimeZone_UTC);
l_Std_Time_TimeZone_GMT = _init_l_Std_Time_TimeZone_GMT();
lean_mark_persistent(l_Std_Time_TimeZone_GMT);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
