// Lean compiler output
// Module: Lean.Data.Format
// Imports: Lean.Data.Options
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
lean_object* lean_format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_68__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Std_Format_pretty_x27_spec__0(lean_object*, lean_object*);
lean_object* l_String_quote(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToFormatKVMap;
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_29__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_instToFormatName__lean___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getUnicode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_format_unicode;
LEAN_EXPORT lean_object* l_Std_Format_format_indent;
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__1(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT uint8_t l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_initFn____x40_Lean_Data_Format___hyg_68_(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getIndent___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_format_width;
LEAN_EXPORT lean_object* l_Std_Format_initFn____x40_Lean_Data_Format___hyg_29_(lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_initFn____x40_Lean_Data_Format___hyg_107_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue;
LEAN_EXPORT uint8_t l_Std_Format_getUnicode(lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_29__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getIndent(lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getWidth(lean_object*);
lean_object* l_Lean_KVMap_findCore(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getWidth___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean;
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__0___boxed(lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_formatKVMap_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_68__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue;
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Std_Format_pretty_x27_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Format_getWidth(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("format", 6, 6);
x_3 = lean_mk_string_unchecked("width", 5, 5);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(120u);
x_6 = l_Lean_KVMap_findCore(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
else
{
lean_dec(x_7);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_getWidth___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_getWidth(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Format_getIndent(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("format", 6, 6);
x_3 = lean_mk_string_unchecked("indent", 6, 6);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = l_Lean_KVMap_findCore(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
return x_5;
}
else
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_7) == 3)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
return x_8;
}
else
{
lean_dec(x_7);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_getIndent___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Std_Format_getIndent(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Std_Format_getUnicode(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = lean_mk_string_unchecked("format", 6, 6);
x_3 = lean_mk_string_unchecked("unicode", 7, 7);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = l_Lean_KVMap_findCore(x_1, x_4);
lean_dec(x_4);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_5);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_5);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_getUnicode___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Std_Format_getUnicode(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_29__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
lean_ctor_set(x_9, 2, x_7);
lean_ctor_set(x_9, 3, x_8);
lean_inc(x_1);
x_10 = lean_register_option(x_1, x_9, x_4);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
lean_inc(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_1);
lean_ctor_set(x_13, 1, x_5);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_5);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn____x40_Lean_Data_Format___hyg_29_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("format", 6, 6);
x_3 = lean_mk_string_unchecked("width", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(120u);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("indentation", 11, 11);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Std", 3, 3);
x_10 = lean_mk_string_unchecked("Format", 6, 6);
x_11 = l_Lean_Name_mkStr4(x_9, x_10, x_2, x_3);
x_12 = l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_29__spec__0(x_4, x_8, x_11, x_1);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_29__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_29__spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_68__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_alloc_ctor(1, 0, 1);
x_7 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_ctor_get(x_2, 1);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_inc(x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
lean_inc(x_1);
x_11 = lean_register_option(x_1, x_10, x_4);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_inc(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_11, 0, x_14);
return x_11;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn____x40_Lean_Data_Format___hyg_68_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("format", 6, 6);
x_3 = lean_mk_string_unchecked("unicode", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("unicode characters", 18, 18);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Std", 3, 3);
x_10 = lean_mk_string_unchecked("Format", 6, 6);
x_11 = l_Lean_Name_mkStr4(x_9, x_10, x_2, x_3);
x_12 = l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_68__spec__0(x_4, x_8, x_11, x_1);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_68__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_68__spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Format_initFn____x40_Lean_Data_Format___hyg_107_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("format", 6, 6);
x_3 = lean_mk_string_unchecked("indent", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("indentation", 11, 11);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Std", 3, 3);
x_10 = lean_mk_string_unchecked("Format", 6, 6);
x_11 = l_Lean_Name_mkStr4(x_9, x_10, x_2, x_3);
x_12 = l_Lean_Option_register___at___Std_Format_initFn____x40_Lean_Data_Format___hyg_29__spec__0(x_4, x_8, x_11, x_1);
lean_dec(x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Std_Format_pretty_x27_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Lean_KVMap_findCore(x_1, x_3);
if (lean_obj_tag(x_5) == 0)
{
lean_inc(x_4);
return x_4;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
if (lean_obj_tag(x_6) == 3)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_6);
lean_inc(x_4);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Std_Format_format_width;
x_4 = l_Lean_Option_get___at___Std_Format_pretty_x27_spec__0(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_format_pretty(x_1, x_4, x_5, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___Std_Format_pretty_x27_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Option_get___at___Std_Format_pretty_x27_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Format_pretty_x27___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_Format_pretty_x27(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_instToFormatName__lean___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
x_5 = l_Lean_Name_toString(x_2, x_4, x_1);
x_6 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_instToFormatName__lean() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatName__lean___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_instToFormatName__lean___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatDataValue___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
uint8_t x_3; 
lean_dec(x_1);
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_String_quote(x_4);
lean_dec(x_4);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_5);
return x_2;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_String_quote(x_6);
lean_dec(x_6);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
case 1:
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = lean_ctor_get_uint8(x_2, 0);
lean_dec(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_mk_string_unchecked("false", 5, 5);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_mk_string_unchecked("true", 4, 4);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
case 2:
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_2);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_ctor_get(x_2, 0);
x_16 = lean_mk_string_unchecked("`", 1, 1);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_16);
x_17 = lean_box(1);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Name_toString(x_15, x_18, x_1);
x_20 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_2);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("`", 1, 1);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(1);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_Name_toString(x_22, x_26, x_1);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
x_29 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
case 3:
{
uint8_t x_30; 
lean_dec(x_1);
x_30 = !lean_is_exclusive(x_2);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_2, 0);
x_32 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
lean_ctor_set(x_2, 0, x_32);
return x_2;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_2, 0);
lean_inc(x_33);
lean_dec(x_2);
x_34 = l___private_Init_Data_Repr_0__Nat_reprFast(x_33);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
return x_35;
}
}
case 4:
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_2);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_2, 0);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_nat_to_int(x_38);
x_40 = lean_int_dec_lt(x_37, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_nat_abs(x_37);
lean_dec(x_37);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_41);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_42);
return x_2;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_43 = lean_nat_abs(x_37);
lean_dec(x_37);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_sub(x_43, x_44);
lean_dec(x_43);
x_46 = lean_mk_string_unchecked("-", 1, 1);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_45, x_47);
lean_dec(x_45);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_48);
x_50 = lean_string_append(x_46, x_49);
lean_dec(x_49);
lean_ctor_set_tag(x_2, 3);
lean_ctor_set(x_2, 0, x_50);
return x_2;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
lean_dec(x_2);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_nat_to_int(x_52);
x_54 = lean_int_dec_lt(x_51, x_53);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_nat_abs(x_51);
lean_dec(x_51);
x_56 = l___private_Init_Data_Repr_0__Nat_reprFast(x_55);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_58 = lean_nat_abs(x_51);
lean_dec(x_51);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_nat_sub(x_58, x_59);
lean_dec(x_58);
x_61 = lean_mk_string_unchecked("-", 1, 1);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_add(x_60, x_62);
lean_dec(x_60);
x_64 = l___private_Init_Data_Repr_0__Nat_reprFast(x_63);
x_65 = lean_string_append(x_61, x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
default: 
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_71; 
lean_dec(x_1);
x_67 = lean_ctor_get(x_2, 0);
lean_inc(x_67);
lean_dec(x_2);
x_68 = lean_box(0);
x_69 = lean_box(0);
x_70 = lean_unbox(x_69);
x_71 = l_Lean_Syntax_formatStx(x_67, x_68, x_70);
return x_71;
}
}
}
}
static lean_object* _init_l_Lean_instToFormatDataValue() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_instToFormatDataValue___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_instToFormatProdNameDataValue___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = l_Lean_Name_toString(x_5, x_8, x_1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked(" := ", 4, 4);
x_12 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_12);
lean_ctor_set(x_3, 0, x_10);
switch (lean_obj_tag(x_6)) {
case 0:
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = l_String_quote(x_14);
lean_dec(x_14);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 0, x_15);
x_16 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_6, 0);
lean_inc(x_17);
lean_dec(x_6);
x_18 = l_String_quote(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
case 1:
{
uint8_t x_21; 
lean_dec(x_2);
x_21 = lean_ctor_get_uint8(x_6, 0);
lean_dec(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_mk_string_unchecked("false", 5, 5);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_mk_string_unchecked("true", 4, 4);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_3);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
case 2:
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_6);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_mk_string_unchecked("`", 1, 1);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 0, x_30);
x_31 = lean_unbox(x_7);
x_32 = l_Lean_Name_toString(x_29, x_31, x_2);
x_33 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_3);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_ctor_get(x_6, 0);
lean_inc(x_36);
lean_dec(x_6);
x_37 = lean_mk_string_unchecked("`", 1, 1);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unbox(x_7);
x_40 = l_Lean_Name_toString(x_36, x_39, x_2);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_38);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_43, 0, x_3);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
case 3:
{
uint8_t x_44; 
lean_dec(x_2);
x_44 = !lean_is_exclusive(x_6);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_6, 0);
x_46 = l___private_Init_Data_Repr_0__Nat_reprFast(x_45);
lean_ctor_set(x_6, 0, x_46);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_6);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_6, 0);
lean_inc(x_48);
lean_dec(x_6);
x_49 = l___private_Init_Data_Repr_0__Nat_reprFast(x_48);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_51, 0, x_3);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
case 4:
{
uint8_t x_52; 
lean_dec(x_2);
x_52 = !lean_is_exclusive(x_6);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_6, 0);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_nat_to_int(x_54);
x_56 = lean_int_dec_lt(x_53, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_nat_abs(x_53);
lean_dec(x_53);
x_58 = l___private_Init_Data_Repr_0__Nat_reprFast(x_57);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 0, x_58);
x_59 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_59, 0, x_3);
lean_ctor_set(x_59, 1, x_6);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_60 = lean_nat_abs(x_53);
lean_dec(x_53);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_sub(x_60, x_61);
lean_dec(x_60);
x_63 = lean_mk_string_unchecked("-", 1, 1);
x_64 = lean_unsigned_to_nat(1u);
x_65 = lean_nat_add(x_62, x_64);
lean_dec(x_62);
x_66 = l___private_Init_Data_Repr_0__Nat_reprFast(x_65);
x_67 = lean_string_append(x_63, x_66);
lean_dec(x_66);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 0, x_67);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_3);
lean_ctor_set(x_68, 1, x_6);
return x_68;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_69 = lean_ctor_get(x_6, 0);
lean_inc(x_69);
lean_dec(x_6);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_to_int(x_70);
x_72 = lean_int_dec_lt(x_69, x_71);
lean_dec(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_nat_abs(x_69);
lean_dec(x_69);
x_74 = l___private_Init_Data_Repr_0__Nat_reprFast(x_73);
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_74);
x_76 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_76, 0, x_3);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_nat_abs(x_69);
lean_dec(x_69);
x_78 = lean_unsigned_to_nat(1u);
x_79 = lean_nat_sub(x_77, x_78);
lean_dec(x_77);
x_80 = lean_mk_string_unchecked("-", 1, 1);
x_81 = lean_unsigned_to_nat(1u);
x_82 = lean_nat_add(x_79, x_81);
lean_dec(x_79);
x_83 = l___private_Init_Data_Repr_0__Nat_reprFast(x_82);
x_84 = lean_string_append(x_80, x_83);
lean_dec(x_83);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_86, 0, x_3);
lean_ctor_set(x_86, 1, x_85);
return x_86;
}
}
}
default: 
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; lean_object* x_92; 
lean_dec(x_2);
x_87 = lean_ctor_get(x_6, 0);
lean_inc(x_87);
lean_dec(x_6);
x_88 = lean_box(0);
x_89 = lean_box(0);
x_90 = lean_unbox(x_89);
x_91 = l_Lean_Syntax_formatStx(x_87, x_88, x_90);
x_92 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_92, 0, x_3);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_93 = lean_ctor_get(x_3, 0);
x_94 = lean_ctor_get(x_3, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_3);
x_95 = lean_box(1);
x_96 = lean_unbox(x_95);
x_97 = l_Lean_Name_toString(x_93, x_96, x_1);
x_98 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_99 = lean_mk_string_unchecked(" := ", 4, 4);
x_100 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_100);
switch (lean_obj_tag(x_94)) {
case 0:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_2);
x_102 = lean_ctor_get(x_94, 0);
lean_inc(x_102);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_103 = x_94;
} else {
 lean_dec_ref(x_94);
 x_103 = lean_box(0);
}
x_104 = l_String_quote(x_102);
lean_dec(x_102);
if (lean_is_scalar(x_103)) {
 x_105 = lean_alloc_ctor(3, 1, 0);
} else {
 x_105 = x_103;
 lean_ctor_set_tag(x_105, 3);
}
lean_ctor_set(x_105, 0, x_104);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_101);
lean_ctor_set(x_106, 1, x_105);
return x_106;
}
case 1:
{
uint8_t x_107; 
lean_dec(x_2);
x_107 = lean_ctor_get_uint8(x_94, 0);
lean_dec(x_94);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; 
x_108 = lean_mk_string_unchecked("false", 5, 5);
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_110, 0, x_101);
lean_ctor_set(x_110, 1, x_109);
return x_110;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_mk_string_unchecked("true", 4, 4);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_101);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
case 2:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_114 = lean_ctor_get(x_94, 0);
lean_inc(x_114);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_115 = x_94;
} else {
 lean_dec_ref(x_94);
 x_115 = lean_box(0);
}
x_116 = lean_mk_string_unchecked("`", 1, 1);
if (lean_is_scalar(x_115)) {
 x_117 = lean_alloc_ctor(3, 1, 0);
} else {
 x_117 = x_115;
 lean_ctor_set_tag(x_117, 3);
}
lean_ctor_set(x_117, 0, x_116);
x_118 = lean_unbox(x_95);
x_119 = l_Lean_Name_toString(x_114, x_118, x_2);
x_120 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_120, 0, x_119);
x_121 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_122, 0, x_101);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
case 3:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_2);
x_123 = lean_ctor_get(x_94, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_124 = x_94;
} else {
 lean_dec_ref(x_94);
 x_124 = lean_box(0);
}
x_125 = l___private_Init_Data_Repr_0__Nat_reprFast(x_123);
if (lean_is_scalar(x_124)) {
 x_126 = lean_alloc_ctor(3, 1, 0);
} else {
 x_126 = x_124;
}
lean_ctor_set(x_126, 0, x_125);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_101);
lean_ctor_set(x_127, 1, x_126);
return x_127;
}
case 4:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
lean_dec(x_2);
x_128 = lean_ctor_get(x_94, 0);
lean_inc(x_128);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 x_129 = x_94;
} else {
 lean_dec_ref(x_94);
 x_129 = lean_box(0);
}
x_130 = lean_unsigned_to_nat(0u);
x_131 = lean_nat_to_int(x_130);
x_132 = lean_int_dec_lt(x_128, x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_nat_abs(x_128);
lean_dec(x_128);
x_134 = l___private_Init_Data_Repr_0__Nat_reprFast(x_133);
if (lean_is_scalar(x_129)) {
 x_135 = lean_alloc_ctor(3, 1, 0);
} else {
 x_135 = x_129;
 lean_ctor_set_tag(x_135, 3);
}
lean_ctor_set(x_135, 0, x_134);
x_136 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_136, 0, x_101);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_137 = lean_nat_abs(x_128);
lean_dec(x_128);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_nat_sub(x_137, x_138);
lean_dec(x_137);
x_140 = lean_mk_string_unchecked("-", 1, 1);
x_141 = lean_unsigned_to_nat(1u);
x_142 = lean_nat_add(x_139, x_141);
lean_dec(x_139);
x_143 = l___private_Init_Data_Repr_0__Nat_reprFast(x_142);
x_144 = lean_string_append(x_140, x_143);
lean_dec(x_143);
if (lean_is_scalar(x_129)) {
 x_145 = lean_alloc_ctor(3, 1, 0);
} else {
 x_145 = x_129;
 lean_ctor_set_tag(x_145, 3);
}
lean_ctor_set(x_145, 0, x_144);
x_146 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_146, 0, x_101);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
default: 
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_2);
x_147 = lean_ctor_get(x_94, 0);
lean_inc(x_147);
lean_dec(x_94);
x_148 = lean_box(0);
x_149 = lean_box(0);
x_150 = lean_unbox(x_149);
x_151 = l_Lean_Syntax_formatStx(x_147, x_148, x_150);
x_152 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_152, 0, x_101);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
}
static lean_object* _init_l_Lean_instToFormatProdNameDataValue() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
lean_inc(x_1);
x_2 = lean_alloc_closure((void*)(l_Lean_instToFormatProdNameDataValue___lam__2), 3, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_1);
return x_2;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_7 = lean_ctor_get(x_3, 1);
x_8 = lean_ctor_get(x_5, 0);
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_alloc_closure((void*)(l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0___boxed), 1, 0);
lean_inc(x_1);
lean_ctor_set_tag(x_5, 5);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set(x_5, 0, x_2);
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
lean_inc(x_10);
x_13 = l_Lean_Name_toString(x_8, x_12, x_10);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_mk_string_unchecked(" := ", 4, 4);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_16);
lean_ctor_set(x_3, 0, x_14);
switch (lean_obj_tag(x_9)) {
case 0:
{
uint8_t x_17; 
lean_dec(x_10);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = l_String_quote(x_18);
lean_dec(x_18);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 0, x_19);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_3);
lean_ctor_set(x_20, 1, x_9);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_20);
x_2 = x_21;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_9, 0);
lean_inc(x_23);
lean_dec(x_9);
x_24 = l_String_quote(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_26, 0, x_3);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_26);
x_2 = x_27;
x_3 = x_7;
goto _start;
}
}
case 1:
{
uint8_t x_29; 
lean_dec(x_10);
x_29 = lean_ctor_get_uint8(x_9, 0);
lean_dec(x_9);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_mk_string_unchecked("false", 5, 5);
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_32, 0, x_3);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
x_2 = x_33;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_mk_string_unchecked("true", 4, 4);
x_36 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_37, 0, x_3);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_37);
x_2 = x_38;
x_3 = x_7;
goto _start;
}
}
case 2:
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_9);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_9, 0);
x_42 = lean_mk_string_unchecked("`", 1, 1);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 0, x_42);
x_43 = lean_unbox(x_11);
x_44 = l_Lean_Name_toString(x_41, x_43, x_10);
x_45 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_45, 0, x_44);
x_46 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_46, 0, x_9);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_47, 0, x_3);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_48, 0, x_5);
lean_ctor_set(x_48, 1, x_47);
x_2 = x_48;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_50 = lean_ctor_get(x_9, 0);
lean_inc(x_50);
lean_dec(x_9);
x_51 = lean_mk_string_unchecked("`", 1, 1);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_unbox(x_11);
x_54 = l_Lean_Name_toString(x_50, x_53, x_10);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_52);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_3);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_57);
x_2 = x_58;
x_3 = x_7;
goto _start;
}
}
case 3:
{
uint8_t x_60; 
lean_dec(x_10);
x_60 = !lean_is_exclusive(x_9);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_9, 0);
x_62 = l___private_Init_Data_Repr_0__Nat_reprFast(x_61);
lean_ctor_set(x_9, 0, x_62);
x_63 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_63, 0, x_3);
lean_ctor_set(x_63, 1, x_9);
x_64 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_64, 0, x_5);
lean_ctor_set(x_64, 1, x_63);
x_2 = x_64;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_66 = lean_ctor_get(x_9, 0);
lean_inc(x_66);
lean_dec(x_9);
x_67 = l___private_Init_Data_Repr_0__Nat_reprFast(x_66);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_69, 0, x_3);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_70, 0, x_5);
lean_ctor_set(x_70, 1, x_69);
x_2 = x_70;
x_3 = x_7;
goto _start;
}
}
case 4:
{
uint8_t x_72; 
lean_dec(x_10);
x_72 = !lean_is_exclusive(x_9);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_ctor_get(x_9, 0);
x_74 = lean_unsigned_to_nat(0u);
x_75 = lean_nat_to_int(x_74);
x_76 = lean_int_dec_lt(x_73, x_75);
lean_dec(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_nat_abs(x_73);
lean_dec(x_73);
x_78 = l___private_Init_Data_Repr_0__Nat_reprFast(x_77);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 0, x_78);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_3);
lean_ctor_set(x_79, 1, x_9);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_5);
lean_ctor_set(x_80, 1, x_79);
x_2 = x_80;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_82 = lean_nat_abs(x_73);
lean_dec(x_73);
x_83 = lean_unsigned_to_nat(1u);
x_84 = lean_nat_sub(x_82, x_83);
lean_dec(x_82);
x_85 = lean_mk_string_unchecked("-", 1, 1);
x_86 = lean_unsigned_to_nat(1u);
x_87 = lean_nat_add(x_84, x_86);
lean_dec(x_84);
x_88 = l___private_Init_Data_Repr_0__Nat_reprFast(x_87);
x_89 = lean_string_append(x_85, x_88);
lean_dec(x_88);
lean_ctor_set_tag(x_9, 3);
lean_ctor_set(x_9, 0, x_89);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_3);
lean_ctor_set(x_90, 1, x_9);
x_91 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_91, 0, x_5);
lean_ctor_set(x_91, 1, x_90);
x_2 = x_91;
x_3 = x_7;
goto _start;
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_93 = lean_ctor_get(x_9, 0);
lean_inc(x_93);
lean_dec(x_9);
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_nat_to_int(x_94);
x_96 = lean_int_dec_lt(x_93, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_97 = lean_nat_abs(x_93);
lean_dec(x_93);
x_98 = l___private_Init_Data_Repr_0__Nat_reprFast(x_97);
x_99 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_100, 0, x_3);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_5);
lean_ctor_set(x_101, 1, x_100);
x_2 = x_101;
x_3 = x_7;
goto _start;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_nat_abs(x_93);
lean_dec(x_93);
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_sub(x_103, x_104);
lean_dec(x_103);
x_106 = lean_mk_string_unchecked("-", 1, 1);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_105, x_107);
lean_dec(x_105);
x_109 = l___private_Init_Data_Repr_0__Nat_reprFast(x_108);
x_110 = lean_string_append(x_106, x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_111, 0, x_110);
x_112 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_112, 0, x_3);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_113, 0, x_5);
lean_ctor_set(x_113, 1, x_112);
x_2 = x_113;
x_3 = x_7;
goto _start;
}
}
}
default: 
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_10);
x_115 = lean_ctor_get(x_9, 0);
lean_inc(x_115);
lean_dec(x_9);
x_116 = lean_box(0);
x_117 = lean_box(0);
x_118 = lean_unbox(x_117);
x_119 = l_Lean_Syntax_formatStx(x_115, x_116, x_118);
x_120 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_120, 0, x_3);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_121, 0, x_5);
lean_ctor_set(x_121, 1, x_120);
x_2 = x_121;
x_3 = x_7;
goto _start;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_123 = lean_ctor_get(x_3, 1);
x_124 = lean_ctor_get(x_5, 0);
x_125 = lean_ctor_get(x_5, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_5);
x_126 = lean_alloc_closure((void*)(l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0___boxed), 1, 0);
lean_inc(x_1);
x_127 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_127, 0, x_2);
lean_ctor_set(x_127, 1, x_1);
x_128 = lean_box(1);
x_129 = lean_unbox(x_128);
lean_inc(x_126);
x_130 = l_Lean_Name_toString(x_124, x_129, x_126);
x_131 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_mk_string_unchecked(" := ", 4, 4);
x_133 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 1, x_133);
lean_ctor_set(x_3, 0, x_131);
switch (lean_obj_tag(x_125)) {
case 0:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_126);
x_134 = lean_ctor_get(x_125, 0);
lean_inc(x_134);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_135 = x_125;
} else {
 lean_dec_ref(x_125);
 x_135 = lean_box(0);
}
x_136 = l_String_quote(x_134);
lean_dec(x_134);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(3, 1, 0);
} else {
 x_137 = x_135;
 lean_ctor_set_tag(x_137, 3);
}
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_138, 0, x_3);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_139, 0, x_127);
lean_ctor_set(x_139, 1, x_138);
x_2 = x_139;
x_3 = x_123;
goto _start;
}
case 1:
{
uint8_t x_141; 
lean_dec(x_126);
x_141 = lean_ctor_get_uint8(x_125, 0);
lean_dec(x_125);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_142 = lean_mk_string_unchecked("false", 5, 5);
x_143 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_143, 0, x_142);
x_144 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_144, 0, x_3);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_145, 0, x_127);
lean_ctor_set(x_145, 1, x_144);
x_2 = x_145;
x_3 = x_123;
goto _start;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_147 = lean_mk_string_unchecked("true", 4, 4);
x_148 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_148, 0, x_147);
x_149 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_149, 0, x_3);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_150, 0, x_127);
lean_ctor_set(x_150, 1, x_149);
x_2 = x_150;
x_3 = x_123;
goto _start;
}
}
case 2:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_152 = lean_ctor_get(x_125, 0);
lean_inc(x_152);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_153 = x_125;
} else {
 lean_dec_ref(x_125);
 x_153 = lean_box(0);
}
x_154 = lean_mk_string_unchecked("`", 1, 1);
if (lean_is_scalar(x_153)) {
 x_155 = lean_alloc_ctor(3, 1, 0);
} else {
 x_155 = x_153;
 lean_ctor_set_tag(x_155, 3);
}
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_unbox(x_128);
x_157 = l_Lean_Name_toString(x_152, x_156, x_126);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_159, 0, x_155);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_160, 0, x_3);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_127);
lean_ctor_set(x_161, 1, x_160);
x_2 = x_161;
x_3 = x_123;
goto _start;
}
case 3:
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
lean_dec(x_126);
x_163 = lean_ctor_get(x_125, 0);
lean_inc(x_163);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_164 = x_125;
} else {
 lean_dec_ref(x_125);
 x_164 = lean_box(0);
}
x_165 = l___private_Init_Data_Repr_0__Nat_reprFast(x_163);
if (lean_is_scalar(x_164)) {
 x_166 = lean_alloc_ctor(3, 1, 0);
} else {
 x_166 = x_164;
}
lean_ctor_set(x_166, 0, x_165);
x_167 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_167, 0, x_3);
lean_ctor_set(x_167, 1, x_166);
x_168 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_168, 0, x_127);
lean_ctor_set(x_168, 1, x_167);
x_2 = x_168;
x_3 = x_123;
goto _start;
}
case 4:
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; uint8_t x_174; 
lean_dec(x_126);
x_170 = lean_ctor_get(x_125, 0);
lean_inc(x_170);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 x_171 = x_125;
} else {
 lean_dec_ref(x_125);
 x_171 = lean_box(0);
}
x_172 = lean_unsigned_to_nat(0u);
x_173 = lean_nat_to_int(x_172);
x_174 = lean_int_dec_lt(x_170, x_173);
lean_dec(x_173);
if (x_174 == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
x_175 = lean_nat_abs(x_170);
lean_dec(x_170);
x_176 = l___private_Init_Data_Repr_0__Nat_reprFast(x_175);
if (lean_is_scalar(x_171)) {
 x_177 = lean_alloc_ctor(3, 1, 0);
} else {
 x_177 = x_171;
 lean_ctor_set_tag(x_177, 3);
}
lean_ctor_set(x_177, 0, x_176);
x_178 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_178, 0, x_3);
lean_ctor_set(x_178, 1, x_177);
x_179 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_179, 0, x_127);
lean_ctor_set(x_179, 1, x_178);
x_2 = x_179;
x_3 = x_123;
goto _start;
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_181 = lean_nat_abs(x_170);
lean_dec(x_170);
x_182 = lean_unsigned_to_nat(1u);
x_183 = lean_nat_sub(x_181, x_182);
lean_dec(x_181);
x_184 = lean_mk_string_unchecked("-", 1, 1);
x_185 = lean_unsigned_to_nat(1u);
x_186 = lean_nat_add(x_183, x_185);
lean_dec(x_183);
x_187 = l___private_Init_Data_Repr_0__Nat_reprFast(x_186);
x_188 = lean_string_append(x_184, x_187);
lean_dec(x_187);
if (lean_is_scalar(x_171)) {
 x_189 = lean_alloc_ctor(3, 1, 0);
} else {
 x_189 = x_171;
 lean_ctor_set_tag(x_189, 3);
}
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_190, 0, x_3);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_191, 0, x_127);
lean_ctor_set(x_191, 1, x_190);
x_2 = x_191;
x_3 = x_123;
goto _start;
}
}
default: 
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
lean_dec(x_126);
x_193 = lean_ctor_get(x_125, 0);
lean_inc(x_193);
lean_dec(x_125);
x_194 = lean_box(0);
x_195 = lean_box(0);
x_196 = lean_unbox(x_195);
x_197 = l_Lean_Syntax_formatStx(x_193, x_194, x_196);
x_198 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_198, 0, x_3);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_199, 0, x_127);
lean_ctor_set(x_199, 1, x_198);
x_2 = x_199;
x_3 = x_123;
goto _start;
}
}
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_201 = lean_ctor_get(x_3, 0);
x_202 = lean_ctor_get(x_3, 1);
lean_inc(x_202);
lean_inc(x_201);
lean_dec(x_3);
x_203 = lean_ctor_get(x_201, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_201, 1);
lean_inc(x_204);
if (lean_is_exclusive(x_201)) {
 lean_ctor_release(x_201, 0);
 lean_ctor_release(x_201, 1);
 x_205 = x_201;
} else {
 lean_dec_ref(x_201);
 x_205 = lean_box(0);
}
x_206 = lean_alloc_closure((void*)(l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0___boxed), 1, 0);
lean_inc(x_1);
if (lean_is_scalar(x_205)) {
 x_207 = lean_alloc_ctor(5, 2, 0);
} else {
 x_207 = x_205;
 lean_ctor_set_tag(x_207, 5);
}
lean_ctor_set(x_207, 0, x_2);
lean_ctor_set(x_207, 1, x_1);
x_208 = lean_box(1);
x_209 = lean_unbox(x_208);
lean_inc(x_206);
x_210 = l_Lean_Name_toString(x_203, x_209, x_206);
x_211 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_mk_string_unchecked(" := ", 4, 4);
x_213 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_213, 0, x_212);
x_214 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_214, 0, x_211);
lean_ctor_set(x_214, 1, x_213);
switch (lean_obj_tag(x_204)) {
case 0:
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; 
lean_dec(x_206);
x_215 = lean_ctor_get(x_204, 0);
lean_inc(x_215);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_216 = x_204;
} else {
 lean_dec_ref(x_204);
 x_216 = lean_box(0);
}
x_217 = l_String_quote(x_215);
lean_dec(x_215);
if (lean_is_scalar(x_216)) {
 x_218 = lean_alloc_ctor(3, 1, 0);
} else {
 x_218 = x_216;
 lean_ctor_set_tag(x_218, 3);
}
lean_ctor_set(x_218, 0, x_217);
x_219 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_219, 0, x_214);
lean_ctor_set(x_219, 1, x_218);
x_220 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_220, 0, x_207);
lean_ctor_set(x_220, 1, x_219);
x_2 = x_220;
x_3 = x_202;
goto _start;
}
case 1:
{
uint8_t x_222; 
lean_dec(x_206);
x_222 = lean_ctor_get_uint8(x_204, 0);
lean_dec(x_204);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_mk_string_unchecked("false", 5, 5);
x_224 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_224, 0, x_223);
x_225 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_225, 0, x_214);
lean_ctor_set(x_225, 1, x_224);
x_226 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_226, 0, x_207);
lean_ctor_set(x_226, 1, x_225);
x_2 = x_226;
x_3 = x_202;
goto _start;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_228 = lean_mk_string_unchecked("true", 4, 4);
x_229 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_229, 0, x_228);
x_230 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_230, 0, x_214);
lean_ctor_set(x_230, 1, x_229);
x_231 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_231, 0, x_207);
lean_ctor_set(x_231, 1, x_230);
x_2 = x_231;
x_3 = x_202;
goto _start;
}
}
case 2:
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_233 = lean_ctor_get(x_204, 0);
lean_inc(x_233);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_234 = x_204;
} else {
 lean_dec_ref(x_204);
 x_234 = lean_box(0);
}
x_235 = lean_mk_string_unchecked("`", 1, 1);
if (lean_is_scalar(x_234)) {
 x_236 = lean_alloc_ctor(3, 1, 0);
} else {
 x_236 = x_234;
 lean_ctor_set_tag(x_236, 3);
}
lean_ctor_set(x_236, 0, x_235);
x_237 = lean_unbox(x_208);
x_238 = l_Lean_Name_toString(x_233, x_237, x_206);
x_239 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_240, 0, x_236);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_241, 0, x_214);
lean_ctor_set(x_241, 1, x_240);
x_242 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_242, 0, x_207);
lean_ctor_set(x_242, 1, x_241);
x_2 = x_242;
x_3 = x_202;
goto _start;
}
case 3:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
lean_dec(x_206);
x_244 = lean_ctor_get(x_204, 0);
lean_inc(x_244);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_245 = x_204;
} else {
 lean_dec_ref(x_204);
 x_245 = lean_box(0);
}
x_246 = l___private_Init_Data_Repr_0__Nat_reprFast(x_244);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(3, 1, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
x_248 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_248, 0, x_214);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_249, 0, x_207);
lean_ctor_set(x_249, 1, x_248);
x_2 = x_249;
x_3 = x_202;
goto _start;
}
case 4:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_dec(x_206);
x_251 = lean_ctor_get(x_204, 0);
lean_inc(x_251);
if (lean_is_exclusive(x_204)) {
 lean_ctor_release(x_204, 0);
 x_252 = x_204;
} else {
 lean_dec_ref(x_204);
 x_252 = lean_box(0);
}
x_253 = lean_unsigned_to_nat(0u);
x_254 = lean_nat_to_int(x_253);
x_255 = lean_int_dec_lt(x_251, x_254);
lean_dec(x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_256 = lean_nat_abs(x_251);
lean_dec(x_251);
x_257 = l___private_Init_Data_Repr_0__Nat_reprFast(x_256);
if (lean_is_scalar(x_252)) {
 x_258 = lean_alloc_ctor(3, 1, 0);
} else {
 x_258 = x_252;
 lean_ctor_set_tag(x_258, 3);
}
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_259, 0, x_214);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_260, 0, x_207);
lean_ctor_set(x_260, 1, x_259);
x_2 = x_260;
x_3 = x_202;
goto _start;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_262 = lean_nat_abs(x_251);
lean_dec(x_251);
x_263 = lean_unsigned_to_nat(1u);
x_264 = lean_nat_sub(x_262, x_263);
lean_dec(x_262);
x_265 = lean_mk_string_unchecked("-", 1, 1);
x_266 = lean_unsigned_to_nat(1u);
x_267 = lean_nat_add(x_264, x_266);
lean_dec(x_264);
x_268 = l___private_Init_Data_Repr_0__Nat_reprFast(x_267);
x_269 = lean_string_append(x_265, x_268);
lean_dec(x_268);
if (lean_is_scalar(x_252)) {
 x_270 = lean_alloc_ctor(3, 1, 0);
} else {
 x_270 = x_252;
 lean_ctor_set_tag(x_270, 3);
}
lean_ctor_set(x_270, 0, x_269);
x_271 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_271, 0, x_214);
lean_ctor_set(x_271, 1, x_270);
x_272 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_272, 0, x_207);
lean_ctor_set(x_272, 1, x_271);
x_2 = x_272;
x_3 = x_202;
goto _start;
}
}
default: 
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_dec(x_206);
x_274 = lean_ctor_get(x_204, 0);
lean_inc(x_274);
lean_dec(x_204);
x_275 = lean_box(0);
x_276 = lean_box(0);
x_277 = lean_unbox(x_276);
x_278 = l_Lean_Syntax_formatStx(x_274, x_275, x_277);
x_279 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_279, 0, x_214);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_280, 0, x_207);
lean_ctor_set(x_280, 1, x_279);
x_2 = x_280;
x_3 = x_202;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Format_joinSep___at___Lean_formatKVMap_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
lean_dec(x_2);
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
uint8_t x_5; 
lean_dec(x_2);
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
lean_dec(x_7);
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = lean_ctor_get(x_6, 1);
x_11 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
lean_inc(x_11);
x_14 = l_Lean_Name_toString(x_9, x_13, x_11);
x_15 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_mk_string_unchecked(" := ", 4, 4);
x_17 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set_tag(x_6, 5);
lean_ctor_set(x_6, 1, x_17);
lean_ctor_set(x_6, 0, x_15);
switch (lean_obj_tag(x_10)) {
case 0:
{
uint8_t x_18; 
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_10);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_10, 0);
x_20 = l_String_quote(x_19);
lean_dec(x_19);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 0, x_20);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_10, 0);
lean_inc(x_21);
lean_dec(x_10);
x_22 = l_String_quote(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_23);
return x_1;
}
}
case 1:
{
uint8_t x_24; 
lean_dec(x_11);
x_24 = lean_ctor_get_uint8(x_10, 0);
lean_dec(x_10);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_mk_string_unchecked("false", 5, 5);
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_26);
return x_1;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_mk_string_unchecked("true", 4, 4);
x_28 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_28);
return x_1;
}
}
case 2:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_mk_string_unchecked("`", 1, 1);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 0, x_31);
x_32 = lean_unbox(x_12);
x_33 = l_Lean_Name_toString(x_30, x_32, x_11);
x_34 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_34);
lean_ctor_set(x_1, 0, x_10);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_1);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_36 = lean_ctor_get(x_10, 0);
lean_inc(x_36);
lean_dec(x_10);
x_37 = lean_mk_string_unchecked("`", 1, 1);
x_38 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_39 = lean_unbox(x_12);
x_40 = l_Lean_Name_toString(x_36, x_39, x_11);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_41);
lean_ctor_set(x_1, 0, x_38);
x_42 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_42, 0, x_6);
lean_ctor_set(x_42, 1, x_1);
return x_42;
}
}
case 3:
{
uint8_t x_43; 
lean_dec(x_11);
x_43 = !lean_is_exclusive(x_10);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_10, 0);
x_45 = l___private_Init_Data_Repr_0__Nat_reprFast(x_44);
lean_ctor_set(x_10, 0, x_45);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_10, 0);
lean_inc(x_46);
lean_dec(x_10);
x_47 = l___private_Init_Data_Repr_0__Nat_reprFast(x_46);
x_48 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_48);
return x_1;
}
}
case 4:
{
uint8_t x_49; 
lean_dec(x_11);
x_49 = !lean_is_exclusive(x_10);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_10, 0);
x_51 = lean_unsigned_to_nat(0u);
x_52 = lean_nat_to_int(x_51);
x_53 = lean_int_dec_lt(x_50, x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_nat_abs(x_50);
lean_dec(x_50);
x_55 = l___private_Init_Data_Repr_0__Nat_reprFast(x_54);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 0, x_55);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_nat_abs(x_50);
lean_dec(x_50);
x_57 = lean_unsigned_to_nat(1u);
x_58 = lean_nat_sub(x_56, x_57);
lean_dec(x_56);
x_59 = lean_mk_string_unchecked("-", 1, 1);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_nat_add(x_58, x_60);
lean_dec(x_58);
x_62 = l___private_Init_Data_Repr_0__Nat_reprFast(x_61);
x_63 = lean_string_append(x_59, x_62);
lean_dec(x_62);
lean_ctor_set_tag(x_10, 3);
lean_ctor_set(x_10, 0, x_63);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_10);
return x_1;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_64 = lean_ctor_get(x_10, 0);
lean_inc(x_64);
lean_dec(x_10);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_to_int(x_65);
x_67 = lean_int_dec_lt(x_64, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_nat_abs(x_64);
lean_dec(x_64);
x_69 = l___private_Init_Data_Repr_0__Nat_reprFast(x_68);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_70);
return x_1;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_nat_abs(x_64);
lean_dec(x_64);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_sub(x_71, x_72);
lean_dec(x_71);
x_74 = lean_mk_string_unchecked("-", 1, 1);
x_75 = lean_unsigned_to_nat(1u);
x_76 = lean_nat_add(x_73, x_75);
lean_dec(x_73);
x_77 = l___private_Init_Data_Repr_0__Nat_reprFast(x_76);
x_78 = lean_string_append(x_74, x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_79);
return x_1;
}
}
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; 
lean_dec(x_11);
x_80 = lean_ctor_get(x_10, 0);
lean_inc(x_80);
lean_dec(x_10);
x_81 = lean_box(0);
x_82 = lean_box(0);
x_83 = lean_unbox(x_82);
x_84 = l_Lean_Syntax_formatStx(x_80, x_81, x_83);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_84);
return x_1;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_85 = lean_ctor_get(x_6, 0);
x_86 = lean_ctor_get(x_6, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_6);
x_87 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_88 = lean_box(1);
x_89 = lean_unbox(x_88);
lean_inc(x_87);
x_90 = l_Lean_Name_toString(x_85, x_89, x_87);
x_91 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_91, 0, x_90);
x_92 = lean_mk_string_unchecked(" := ", 4, 4);
x_93 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
switch (lean_obj_tag(x_86)) {
case 0:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_87);
x_95 = lean_ctor_get(x_86, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_96 = x_86;
} else {
 lean_dec_ref(x_86);
 x_96 = lean_box(0);
}
x_97 = l_String_quote(x_95);
lean_dec(x_95);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(3, 1, 0);
} else {
 x_98 = x_96;
 lean_ctor_set_tag(x_98, 3);
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_98);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
case 1:
{
uint8_t x_99; 
lean_dec(x_87);
x_99 = lean_ctor_get_uint8(x_86, 0);
lean_dec(x_86);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_mk_string_unchecked("false", 5, 5);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_101);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_mk_string_unchecked("true", 4, 4);
x_103 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_103);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
}
case 2:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_105 = x_86;
} else {
 lean_dec_ref(x_86);
 x_105 = lean_box(0);
}
x_106 = lean_mk_string_unchecked("`", 1, 1);
if (lean_is_scalar(x_105)) {
 x_107 = lean_alloc_ctor(3, 1, 0);
} else {
 x_107 = x_105;
 lean_ctor_set_tag(x_107, 3);
}
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_unbox(x_88);
x_109 = l_Lean_Name_toString(x_104, x_108, x_87);
x_110 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_110);
lean_ctor_set(x_1, 0, x_107);
x_111 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_111, 0, x_94);
lean_ctor_set(x_111, 1, x_1);
return x_111;
}
case 3:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_87);
x_112 = lean_ctor_get(x_86, 0);
lean_inc(x_112);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_113 = x_86;
} else {
 lean_dec_ref(x_86);
 x_113 = lean_box(0);
}
x_114 = l___private_Init_Data_Repr_0__Nat_reprFast(x_112);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(3, 1, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_115);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
case 4:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
lean_dec(x_87);
x_116 = lean_ctor_get(x_86, 0);
lean_inc(x_116);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 x_117 = x_86;
} else {
 lean_dec_ref(x_86);
 x_117 = lean_box(0);
}
x_118 = lean_unsigned_to_nat(0u);
x_119 = lean_nat_to_int(x_118);
x_120 = lean_int_dec_lt(x_116, x_119);
lean_dec(x_119);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_121 = lean_nat_abs(x_116);
lean_dec(x_116);
x_122 = l___private_Init_Data_Repr_0__Nat_reprFast(x_121);
if (lean_is_scalar(x_117)) {
 x_123 = lean_alloc_ctor(3, 1, 0);
} else {
 x_123 = x_117;
 lean_ctor_set_tag(x_123, 3);
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_123);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_124 = lean_nat_abs(x_116);
lean_dec(x_116);
x_125 = lean_unsigned_to_nat(1u);
x_126 = lean_nat_sub(x_124, x_125);
lean_dec(x_124);
x_127 = lean_mk_string_unchecked("-", 1, 1);
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_add(x_126, x_128);
lean_dec(x_126);
x_130 = l___private_Init_Data_Repr_0__Nat_reprFast(x_129);
x_131 = lean_string_append(x_127, x_130);
lean_dec(x_130);
if (lean_is_scalar(x_117)) {
 x_132 = lean_alloc_ctor(3, 1, 0);
} else {
 x_132 = x_117;
 lean_ctor_set_tag(x_132, 3);
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_132);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
}
default: 
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
lean_dec(x_87);
x_133 = lean_ctor_get(x_86, 0);
lean_inc(x_133);
lean_dec(x_86);
x_134 = lean_box(0);
x_135 = lean_box(0);
x_136 = lean_unbox(x_135);
x_137 = l_Lean_Syntax_formatStx(x_133, x_134, x_136);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_137);
lean_ctor_set(x_1, 0, x_94);
return x_1;
}
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
lean_dec(x_1);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_141 = x_138;
} else {
 lean_dec_ref(x_138);
 x_141 = lean_box(0);
}
x_142 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_143 = lean_box(1);
x_144 = lean_unbox(x_143);
lean_inc(x_142);
x_145 = l_Lean_Name_toString(x_139, x_144, x_142);
x_146 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_mk_string_unchecked(" := ", 4, 4);
x_148 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_148, 0, x_147);
if (lean_is_scalar(x_141)) {
 x_149 = lean_alloc_ctor(5, 2, 0);
} else {
 x_149 = x_141;
 lean_ctor_set_tag(x_149, 5);
}
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
switch (lean_obj_tag(x_140)) {
case 0:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_142);
x_150 = lean_ctor_get(x_140, 0);
lean_inc(x_150);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_151 = x_140;
} else {
 lean_dec_ref(x_140);
 x_151 = lean_box(0);
}
x_152 = l_String_quote(x_150);
lean_dec(x_150);
if (lean_is_scalar(x_151)) {
 x_153 = lean_alloc_ctor(3, 1, 0);
} else {
 x_153 = x_151;
 lean_ctor_set_tag(x_153, 3);
}
lean_ctor_set(x_153, 0, x_152);
x_154 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_154, 0, x_149);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
case 1:
{
uint8_t x_155; 
lean_dec(x_142);
x_155 = lean_ctor_get_uint8(x_140, 0);
lean_dec(x_140);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_mk_string_unchecked("false", 5, 5);
x_157 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_157, 0, x_156);
x_158 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_158, 0, x_149);
lean_ctor_set(x_158, 1, x_157);
return x_158;
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_159 = lean_mk_string_unchecked("true", 4, 4);
x_160 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_160, 0, x_159);
x_161 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_161, 0, x_149);
lean_ctor_set(x_161, 1, x_160);
return x_161;
}
}
case 2:
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = lean_ctor_get(x_140, 0);
lean_inc(x_162);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_163 = x_140;
} else {
 lean_dec_ref(x_140);
 x_163 = lean_box(0);
}
x_164 = lean_mk_string_unchecked("`", 1, 1);
if (lean_is_scalar(x_163)) {
 x_165 = lean_alloc_ctor(3, 1, 0);
} else {
 x_165 = x_163;
 lean_ctor_set_tag(x_165, 3);
}
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_unbox(x_143);
x_167 = l_Lean_Name_toString(x_162, x_166, x_142);
x_168 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_168, 0, x_167);
x_169 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_169, 0, x_165);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_170, 0, x_149);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
case 3:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
lean_dec(x_142);
x_171 = lean_ctor_get(x_140, 0);
lean_inc(x_171);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_172 = x_140;
} else {
 lean_dec_ref(x_140);
 x_172 = lean_box(0);
}
x_173 = l___private_Init_Data_Repr_0__Nat_reprFast(x_171);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(3, 1, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_175, 0, x_149);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
case 4:
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
lean_dec(x_142);
x_176 = lean_ctor_get(x_140, 0);
lean_inc(x_176);
if (lean_is_exclusive(x_140)) {
 lean_ctor_release(x_140, 0);
 x_177 = x_140;
} else {
 lean_dec_ref(x_140);
 x_177 = lean_box(0);
}
x_178 = lean_unsigned_to_nat(0u);
x_179 = lean_nat_to_int(x_178);
x_180 = lean_int_dec_lt(x_176, x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_181 = lean_nat_abs(x_176);
lean_dec(x_176);
x_182 = l___private_Init_Data_Repr_0__Nat_reprFast(x_181);
if (lean_is_scalar(x_177)) {
 x_183 = lean_alloc_ctor(3, 1, 0);
} else {
 x_183 = x_177;
 lean_ctor_set_tag(x_183, 3);
}
lean_ctor_set(x_183, 0, x_182);
x_184 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_184, 0, x_149);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_185 = lean_nat_abs(x_176);
lean_dec(x_176);
x_186 = lean_unsigned_to_nat(1u);
x_187 = lean_nat_sub(x_185, x_186);
lean_dec(x_185);
x_188 = lean_mk_string_unchecked("-", 1, 1);
x_189 = lean_unsigned_to_nat(1u);
x_190 = lean_nat_add(x_187, x_189);
lean_dec(x_187);
x_191 = l___private_Init_Data_Repr_0__Nat_reprFast(x_190);
x_192 = lean_string_append(x_188, x_191);
lean_dec(x_191);
if (lean_is_scalar(x_177)) {
 x_193 = lean_alloc_ctor(3, 1, 0);
} else {
 x_193 = x_177;
 lean_ctor_set_tag(x_193, 3);
}
lean_ctor_set(x_193, 0, x_192);
x_194 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_194, 0, x_149);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
default: 
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; uint8_t x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_142);
x_195 = lean_ctor_get(x_140, 0);
lean_inc(x_195);
lean_dec(x_140);
x_196 = lean_box(0);
x_197 = lean_box(0);
x_198 = lean_unbox(x_197);
x_199 = l_Lean_Syntax_formatStx(x_195, x_196, x_198);
x_200 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_200, 0, x_149);
lean_ctor_set(x_200, 1, x_199);
return x_200;
}
}
}
}
else
{
uint8_t x_201; 
x_201 = !lean_is_exclusive(x_1);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_ctor_get(x_1, 0);
x_203 = lean_ctor_get(x_1, 1);
lean_dec(x_203);
x_204 = !lean_is_exclusive(x_202);
if (x_204 == 0)
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; uint8_t x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_205 = lean_ctor_get(x_202, 0);
x_206 = lean_ctor_get(x_202, 1);
x_207 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_208 = lean_box(1);
x_209 = lean_unbox(x_208);
lean_inc(x_207);
x_210 = l_Lean_Name_toString(x_205, x_209, x_207);
x_211 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_211, 0, x_210);
x_212 = lean_mk_string_unchecked(" := ", 4, 4);
x_213 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set_tag(x_202, 5);
lean_ctor_set(x_202, 1, x_213);
lean_ctor_set(x_202, 0, x_211);
switch (lean_obj_tag(x_206)) {
case 0:
{
uint8_t x_214; 
lean_dec(x_207);
x_214 = !lean_is_exclusive(x_206);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_206, 0);
x_216 = l_String_quote(x_215);
lean_dec(x_215);
lean_ctor_set_tag(x_206, 3);
lean_ctor_set(x_206, 0, x_216);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_206);
x_217 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_206, 0);
lean_inc(x_218);
lean_dec(x_206);
x_219 = l_String_quote(x_218);
lean_dec(x_218);
x_220 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_220, 0, x_219);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_220);
x_221 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_221;
}
}
case 1:
{
uint8_t x_222; 
lean_dec(x_207);
x_222 = lean_ctor_get_uint8(x_206, 0);
lean_dec(x_206);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_mk_string_unchecked("false", 5, 5);
x_224 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_224);
x_225 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; 
x_226 = lean_mk_string_unchecked("true", 4, 4);
x_227 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_227, 0, x_226);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_227);
x_228 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_228;
}
}
case 2:
{
uint8_t x_229; 
x_229 = !lean_is_exclusive(x_206);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; uint8_t x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_230 = lean_ctor_get(x_206, 0);
x_231 = lean_mk_string_unchecked("`", 1, 1);
lean_ctor_set_tag(x_206, 3);
lean_ctor_set(x_206, 0, x_231);
x_232 = lean_unbox(x_208);
x_233 = l_Lean_Name_toString(x_230, x_232, x_207);
x_234 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_234);
lean_ctor_set(x_1, 0, x_206);
x_235 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_235, 0, x_202);
lean_ctor_set(x_235, 1, x_1);
x_236 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_235, x_4);
return x_236;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_237 = lean_ctor_get(x_206, 0);
lean_inc(x_237);
lean_dec(x_206);
x_238 = lean_mk_string_unchecked("`", 1, 1);
x_239 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_239, 0, x_238);
x_240 = lean_unbox(x_208);
x_241 = l_Lean_Name_toString(x_237, x_240, x_207);
x_242 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_242, 0, x_241);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_242);
lean_ctor_set(x_1, 0, x_239);
x_243 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_243, 0, x_202);
lean_ctor_set(x_243, 1, x_1);
x_244 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_243, x_4);
return x_244;
}
}
case 3:
{
uint8_t x_245; 
lean_dec(x_207);
x_245 = !lean_is_exclusive(x_206);
if (x_245 == 0)
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_206, 0);
x_247 = l___private_Init_Data_Repr_0__Nat_reprFast(x_246);
lean_ctor_set(x_206, 0, x_247);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_206);
x_248 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_248;
}
else
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_249 = lean_ctor_get(x_206, 0);
lean_inc(x_249);
lean_dec(x_206);
x_250 = l___private_Init_Data_Repr_0__Nat_reprFast(x_249);
x_251 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_251, 0, x_250);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_251);
x_252 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_252;
}
}
case 4:
{
uint8_t x_253; 
lean_dec(x_207);
x_253 = !lean_is_exclusive(x_206);
if (x_253 == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; uint8_t x_257; 
x_254 = lean_ctor_get(x_206, 0);
x_255 = lean_unsigned_to_nat(0u);
x_256 = lean_nat_to_int(x_255);
x_257 = lean_int_dec_lt(x_254, x_256);
lean_dec(x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_258 = lean_nat_abs(x_254);
lean_dec(x_254);
x_259 = l___private_Init_Data_Repr_0__Nat_reprFast(x_258);
lean_ctor_set_tag(x_206, 3);
lean_ctor_set(x_206, 0, x_259);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_206);
x_260 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_260;
}
else
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_261 = lean_nat_abs(x_254);
lean_dec(x_254);
x_262 = lean_unsigned_to_nat(1u);
x_263 = lean_nat_sub(x_261, x_262);
lean_dec(x_261);
x_264 = lean_mk_string_unchecked("-", 1, 1);
x_265 = lean_unsigned_to_nat(1u);
x_266 = lean_nat_add(x_263, x_265);
lean_dec(x_263);
x_267 = l___private_Init_Data_Repr_0__Nat_reprFast(x_266);
x_268 = lean_string_append(x_264, x_267);
lean_dec(x_267);
lean_ctor_set_tag(x_206, 3);
lean_ctor_set(x_206, 0, x_268);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_206);
x_269 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_269;
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; 
x_270 = lean_ctor_get(x_206, 0);
lean_inc(x_270);
lean_dec(x_206);
x_271 = lean_unsigned_to_nat(0u);
x_272 = lean_nat_to_int(x_271);
x_273 = lean_int_dec_lt(x_270, x_272);
lean_dec(x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_274 = lean_nat_abs(x_270);
lean_dec(x_270);
x_275 = l___private_Init_Data_Repr_0__Nat_reprFast(x_274);
x_276 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_276);
x_277 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_277;
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; 
x_278 = lean_nat_abs(x_270);
lean_dec(x_270);
x_279 = lean_unsigned_to_nat(1u);
x_280 = lean_nat_sub(x_278, x_279);
lean_dec(x_278);
x_281 = lean_mk_string_unchecked("-", 1, 1);
x_282 = lean_unsigned_to_nat(1u);
x_283 = lean_nat_add(x_280, x_282);
lean_dec(x_280);
x_284 = l___private_Init_Data_Repr_0__Nat_reprFast(x_283);
x_285 = lean_string_append(x_281, x_284);
lean_dec(x_284);
x_286 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_286);
x_287 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_287;
}
}
}
default: 
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_207);
x_288 = lean_ctor_get(x_206, 0);
lean_inc(x_288);
lean_dec(x_206);
x_289 = lean_box(0);
x_290 = lean_box(0);
x_291 = lean_unbox(x_290);
x_292 = l_Lean_Syntax_formatStx(x_288, x_289, x_291);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_292);
x_293 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_293;
}
}
}
else
{
lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; uint8_t x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
x_294 = lean_ctor_get(x_202, 0);
x_295 = lean_ctor_get(x_202, 1);
lean_inc(x_295);
lean_inc(x_294);
lean_dec(x_202);
x_296 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_297 = lean_box(1);
x_298 = lean_unbox(x_297);
lean_inc(x_296);
x_299 = l_Lean_Name_toString(x_294, x_298, x_296);
x_300 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_300, 0, x_299);
x_301 = lean_mk_string_unchecked(" := ", 4, 4);
x_302 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_303 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_302);
switch (lean_obj_tag(x_295)) {
case 0:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_296);
x_304 = lean_ctor_get(x_295, 0);
lean_inc(x_304);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_305 = x_295;
} else {
 lean_dec_ref(x_295);
 x_305 = lean_box(0);
}
x_306 = l_String_quote(x_304);
lean_dec(x_304);
if (lean_is_scalar(x_305)) {
 x_307 = lean_alloc_ctor(3, 1, 0);
} else {
 x_307 = x_305;
 lean_ctor_set_tag(x_307, 3);
}
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_307);
lean_ctor_set(x_1, 0, x_303);
x_308 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_308;
}
case 1:
{
uint8_t x_309; 
lean_dec(x_296);
x_309 = lean_ctor_get_uint8(x_295, 0);
lean_dec(x_295);
if (x_309 == 0)
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_mk_string_unchecked("false", 5, 5);
x_311 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_311, 0, x_310);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_311);
lean_ctor_set(x_1, 0, x_303);
x_312 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_312;
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_313 = lean_mk_string_unchecked("true", 4, 4);
x_314 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_314);
lean_ctor_set(x_1, 0, x_303);
x_315 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_315;
}
}
case 2:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_316 = lean_ctor_get(x_295, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_317 = x_295;
} else {
 lean_dec_ref(x_295);
 x_317 = lean_box(0);
}
x_318 = lean_mk_string_unchecked("`", 1, 1);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(3, 1, 0);
} else {
 x_319 = x_317;
 lean_ctor_set_tag(x_319, 3);
}
lean_ctor_set(x_319, 0, x_318);
x_320 = lean_unbox(x_297);
x_321 = l_Lean_Name_toString(x_316, x_320, x_296);
x_322 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_322);
lean_ctor_set(x_1, 0, x_319);
x_323 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_323, 0, x_303);
lean_ctor_set(x_323, 1, x_1);
x_324 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_323, x_4);
return x_324;
}
case 3:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
lean_dec(x_296);
x_325 = lean_ctor_get(x_295, 0);
lean_inc(x_325);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_326 = x_295;
} else {
 lean_dec_ref(x_295);
 x_326 = lean_box(0);
}
x_327 = l___private_Init_Data_Repr_0__Nat_reprFast(x_325);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(3, 1, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_328);
lean_ctor_set(x_1, 0, x_303);
x_329 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_329;
}
case 4:
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; uint8_t x_334; 
lean_dec(x_296);
x_330 = lean_ctor_get(x_295, 0);
lean_inc(x_330);
if (lean_is_exclusive(x_295)) {
 lean_ctor_release(x_295, 0);
 x_331 = x_295;
} else {
 lean_dec_ref(x_295);
 x_331 = lean_box(0);
}
x_332 = lean_unsigned_to_nat(0u);
x_333 = lean_nat_to_int(x_332);
x_334 = lean_int_dec_lt(x_330, x_333);
lean_dec(x_333);
if (x_334 == 0)
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_335 = lean_nat_abs(x_330);
lean_dec(x_330);
x_336 = l___private_Init_Data_Repr_0__Nat_reprFast(x_335);
if (lean_is_scalar(x_331)) {
 x_337 = lean_alloc_ctor(3, 1, 0);
} else {
 x_337 = x_331;
 lean_ctor_set_tag(x_337, 3);
}
lean_ctor_set(x_337, 0, x_336);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_337);
lean_ctor_set(x_1, 0, x_303);
x_338 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_338;
}
else
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
x_339 = lean_nat_abs(x_330);
lean_dec(x_330);
x_340 = lean_unsigned_to_nat(1u);
x_341 = lean_nat_sub(x_339, x_340);
lean_dec(x_339);
x_342 = lean_mk_string_unchecked("-", 1, 1);
x_343 = lean_unsigned_to_nat(1u);
x_344 = lean_nat_add(x_341, x_343);
lean_dec(x_341);
x_345 = l___private_Init_Data_Repr_0__Nat_reprFast(x_344);
x_346 = lean_string_append(x_342, x_345);
lean_dec(x_345);
if (lean_is_scalar(x_331)) {
 x_347 = lean_alloc_ctor(3, 1, 0);
} else {
 x_347 = x_331;
 lean_ctor_set_tag(x_347, 3);
}
lean_ctor_set(x_347, 0, x_346);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_347);
lean_ctor_set(x_1, 0, x_303);
x_348 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_348;
}
}
default: 
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; uint8_t x_352; lean_object* x_353; lean_object* x_354; 
lean_dec(x_296);
x_349 = lean_ctor_get(x_295, 0);
lean_inc(x_349);
lean_dec(x_295);
x_350 = lean_box(0);
x_351 = lean_box(0);
x_352 = lean_unbox(x_351);
x_353 = l_Lean_Syntax_formatStx(x_349, x_350, x_352);
lean_ctor_set_tag(x_1, 5);
lean_ctor_set(x_1, 1, x_353);
lean_ctor_set(x_1, 0, x_303);
x_354 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_1, x_4);
return x_354;
}
}
}
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; uint8_t x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_355 = lean_ctor_get(x_1, 0);
lean_inc(x_355);
lean_dec(x_1);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_358 = x_355;
} else {
 lean_dec_ref(x_355);
 x_358 = lean_box(0);
}
x_359 = lean_alloc_closure((void*)(l_Lean_instToFormatName__lean___lam__0___boxed), 1, 0);
x_360 = lean_box(1);
x_361 = lean_unbox(x_360);
lean_inc(x_359);
x_362 = l_Lean_Name_toString(x_356, x_361, x_359);
x_363 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_363, 0, x_362);
x_364 = lean_mk_string_unchecked(" := ", 4, 4);
x_365 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_365, 0, x_364);
if (lean_is_scalar(x_358)) {
 x_366 = lean_alloc_ctor(5, 2, 0);
} else {
 x_366 = x_358;
 lean_ctor_set_tag(x_366, 5);
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_365);
switch (lean_obj_tag(x_357)) {
case 0:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_359);
x_367 = lean_ctor_get(x_357, 0);
lean_inc(x_367);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_368 = x_357;
} else {
 lean_dec_ref(x_357);
 x_368 = lean_box(0);
}
x_369 = l_String_quote(x_367);
lean_dec(x_367);
if (lean_is_scalar(x_368)) {
 x_370 = lean_alloc_ctor(3, 1, 0);
} else {
 x_370 = x_368;
 lean_ctor_set_tag(x_370, 3);
}
lean_ctor_set(x_370, 0, x_369);
x_371 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_371, 0, x_366);
lean_ctor_set(x_371, 1, x_370);
x_372 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_371, x_4);
return x_372;
}
case 1:
{
uint8_t x_373; 
lean_dec(x_359);
x_373 = lean_ctor_get_uint8(x_357, 0);
lean_dec(x_357);
if (x_373 == 0)
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_374 = lean_mk_string_unchecked("false", 5, 5);
x_375 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_376, 0, x_366);
lean_ctor_set(x_376, 1, x_375);
x_377 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_376, x_4);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_378 = lean_mk_string_unchecked("true", 4, 4);
x_379 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_379, 0, x_378);
x_380 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_380, 0, x_366);
lean_ctor_set(x_380, 1, x_379);
x_381 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_380, x_4);
return x_381;
}
}
case 2:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_382 = lean_ctor_get(x_357, 0);
lean_inc(x_382);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_383 = x_357;
} else {
 lean_dec_ref(x_357);
 x_383 = lean_box(0);
}
x_384 = lean_mk_string_unchecked("`", 1, 1);
if (lean_is_scalar(x_383)) {
 x_385 = lean_alloc_ctor(3, 1, 0);
} else {
 x_385 = x_383;
 lean_ctor_set_tag(x_385, 3);
}
lean_ctor_set(x_385, 0, x_384);
x_386 = lean_unbox(x_360);
x_387 = l_Lean_Name_toString(x_382, x_386, x_359);
x_388 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_388, 0, x_387);
x_389 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_389, 0, x_385);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_390, 0, x_366);
lean_ctor_set(x_390, 1, x_389);
x_391 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_390, x_4);
return x_391;
}
case 3:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; 
lean_dec(x_359);
x_392 = lean_ctor_get(x_357, 0);
lean_inc(x_392);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_393 = x_357;
} else {
 lean_dec_ref(x_357);
 x_393 = lean_box(0);
}
x_394 = l___private_Init_Data_Repr_0__Nat_reprFast(x_392);
if (lean_is_scalar(x_393)) {
 x_395 = lean_alloc_ctor(3, 1, 0);
} else {
 x_395 = x_393;
}
lean_ctor_set(x_395, 0, x_394);
x_396 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_396, 0, x_366);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_396, x_4);
return x_397;
}
case 4:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
lean_dec(x_359);
x_398 = lean_ctor_get(x_357, 0);
lean_inc(x_398);
if (lean_is_exclusive(x_357)) {
 lean_ctor_release(x_357, 0);
 x_399 = x_357;
} else {
 lean_dec_ref(x_357);
 x_399 = lean_box(0);
}
x_400 = lean_unsigned_to_nat(0u);
x_401 = lean_nat_to_int(x_400);
x_402 = lean_int_dec_lt(x_398, x_401);
lean_dec(x_401);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; 
x_403 = lean_nat_abs(x_398);
lean_dec(x_398);
x_404 = l___private_Init_Data_Repr_0__Nat_reprFast(x_403);
if (lean_is_scalar(x_399)) {
 x_405 = lean_alloc_ctor(3, 1, 0);
} else {
 x_405 = x_399;
 lean_ctor_set_tag(x_405, 3);
}
lean_ctor_set(x_405, 0, x_404);
x_406 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_406, 0, x_366);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_406, x_4);
return x_407;
}
else
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; 
x_408 = lean_nat_abs(x_398);
lean_dec(x_398);
x_409 = lean_unsigned_to_nat(1u);
x_410 = lean_nat_sub(x_408, x_409);
lean_dec(x_408);
x_411 = lean_mk_string_unchecked("-", 1, 1);
x_412 = lean_unsigned_to_nat(1u);
x_413 = lean_nat_add(x_410, x_412);
lean_dec(x_410);
x_414 = l___private_Init_Data_Repr_0__Nat_reprFast(x_413);
x_415 = lean_string_append(x_411, x_414);
lean_dec(x_414);
if (lean_is_scalar(x_399)) {
 x_416 = lean_alloc_ctor(3, 1, 0);
} else {
 x_416 = x_399;
 lean_ctor_set_tag(x_416, 3);
}
lean_ctor_set(x_416, 0, x_415);
x_417 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_417, 0, x_366);
lean_ctor_set(x_417, 1, x_416);
x_418 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_417, x_4);
return x_418;
}
}
default: 
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; uint8_t x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_359);
x_419 = lean_ctor_get(x_357, 0);
lean_inc(x_419);
lean_dec(x_357);
x_420 = lean_box(0);
x_421 = lean_box(0);
x_422 = lean_unbox(x_421);
x_423 = l_Lean_Syntax_formatStx(x_419, x_420, x_422);
x_424 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_424, 0, x_366);
lean_ctor_set(x_424, 1, x_423);
x_425 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0(x_2, x_424, x_4);
return x_425;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_formatKVMap(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_2 = lean_mk_string_unchecked(", ", 2, 2);
x_3 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Std_Format_joinSep___at___Lean_formatKVMap_spec__0(x_1, x_3);
x_5 = lean_mk_string_unchecked("[", 1, 1);
x_6 = lean_mk_string_unchecked("]", 1, 1);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_5);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
x_11 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_11, 0, x_6);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_List_foldl___at___Std_Format_joinSep___at___Lean_formatKVMap_spec__0_spec__0___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instToFormatKVMap() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_formatKVMap), 1, 0);
return x_1;
}
}
lean_object* initialize_Lean_Data_Options(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Format(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Data_Options(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Std_Format_initFn____x40_Lean_Data_Format___hyg_29_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_width = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_width);
lean_dec_ref(res);
}if (builtin) {res = l_Std_Format_initFn____x40_Lean_Data_Format___hyg_68_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_unicode = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_unicode);
lean_dec_ref(res);
}if (builtin) {res = l_Std_Format_initFn____x40_Lean_Data_Format___hyg_107_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Std_Format_format_indent = lean_io_result_get_value(res);
lean_mark_persistent(l_Std_Format_format_indent);
lean_dec_ref(res);
}l_Lean_instToFormatName__lean = _init_l_Lean_instToFormatName__lean();
lean_mark_persistent(l_Lean_instToFormatName__lean);
l_Lean_instToFormatDataValue = _init_l_Lean_instToFormatDataValue();
lean_mark_persistent(l_Lean_instToFormatDataValue);
l_Lean_instToFormatProdNameDataValue = _init_l_Lean_instToFormatProdNameDataValue();
lean_mark_persistent(l_Lean_instToFormatProdNameDataValue);
l_Lean_instToFormatKVMap = _init_l_Lean_instToFormatKVMap();
lean_mark_persistent(l_Lean_instToFormatKVMap);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
