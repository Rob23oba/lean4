// Lean compiler output
// Module: Lake.Toml.Data.Value
// Imports: Init.Data.Float Lake.Toml.Data.Dict Lake.Toml.Data.DateTime
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
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object*);
lean_object* l_Lake_Toml_RBDict_mkEmpty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineTable_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineArray_spec__0(size_t, size_t, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_empty;
uint8_t l___private_Lake_Toml_Data_DateTime_0__Lake_Toml_decEqDateTime____x40_Lake_Toml_Data_DateTime___hyg_1023_(lean_object*, lean_object*);
lean_object* l_Lake_lpad(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable_appendKeyval___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_Toml_ppString_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_RBDict_empty(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable_appendKeyval(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142_(lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_nat_to_int(lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_Name_quickCmp___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___redArg(lean_object*, lean_object*);
lean_object* lean_string_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_DateTime_toString(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineArray_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppString___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4_spec__4(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Nat_toDigits(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_abs(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instToStringValue;
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lake_Toml_ppTable_spec__3(uint8_t, lean_object*, size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_float_to_string(double);
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_instInhabitedValue;
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_Toml_ppString_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
uint8_t lean_float_beq(double, double);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object*);
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_Toml_ppSimpleKey_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey___boxed(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lake_Toml_ppTable_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_instBEqValue;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineTable_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0(lean_object*, size_t, size_t, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object*);
uint32_t l_Char_ofNat(lean_object*);
static lean_object* _init_l_Lake_Toml_instInhabitedValue() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_8 = lean_array_fget(x_1, x_7);
x_9 = lean_array_fget(x_2, x_7);
x_10 = l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142_(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 1)
{
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_sub(x_3, x_6);
lean_dec(x_3);
x_11 = lean_array_fget(x_1, x_7);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_array_fget(x_2, x_7);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_name_eq(x_12, x_15);
lean_dec(x_15);
lean_dec(x_12);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_13);
x_8 = x_17;
goto block_10;
}
else
{
uint8_t x_18; 
x_18 = l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142_(x_13, x_16);
x_8 = x_18;
goto block_10;
}
block_10:
{
if (x_8 == 0)
{
lean_dec(x_7);
return x_8;
}
else
{
x_3 = x_7;
goto _start;
}
}
}
}
}
LEAN_EXPORT uint8_t l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___redArg(x_1, x_2, x_4);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_array_get_size(x_3);
x_6 = lean_array_get_size(x_4);
x_7 = lean_nat_dec_eq(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_dec(x_5);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___redArg(x_3, x_4, x_5);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_Syntax_structEq(x_3, x_5);
if (x_7 == 0)
{
lean_dec(x_6);
lean_dec(x_4);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_string_dec_eq(x_4, x_6);
lean_dec(x_6);
lean_dec(x_4);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Syntax_structEq(x_11, x_13);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_int_dec_eq(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_19; double x_20; lean_object* x_21; double x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get_float(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get_float(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_23 = l_Lean_Syntax_structEq(x_19, x_21);
if (x_23 == 0)
{
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_float_beq(x_20, x_22);
return x_24;
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_2);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_27; uint8_t x_28; lean_object* x_29; uint8_t x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
lean_dec(x_2);
x_31 = l_Lean_Syntax_structEq(x_27, x_29);
if (x_31 == 0)
{
return x_31;
}
else
{
if (x_28 == 0)
{
if (x_30 == 0)
{
return x_31;
}
else
{
return x_28;
}
}
else
{
return x_30;
}
}
}
else
{
lean_object* x_32; uint8_t x_33; 
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_box(0);
x_33 = lean_unbox(x_32);
return x_33;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_ctor_get(x_2, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
lean_dec(x_2);
x_38 = l_Lean_Syntax_structEq(x_34, x_36);
if (x_38 == 0)
{
lean_dec(x_37);
lean_dec(x_35);
return x_38;
}
else
{
uint8_t x_39; 
x_39 = l___private_Lake_Toml_Data_DateTime_0__Lake_Toml_decEqDateTime____x40_Lake_Toml_Data_DateTime___hyg_1023_(x_35, x_37);
return x_39;
}
}
else
{
lean_object* x_40; uint8_t x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_unbox(x_40);
return x_41;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_42 = lean_ctor_get(x_1, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
x_44 = lean_ctor_get(x_2, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_2, 1);
lean_inc(x_45);
lean_dec(x_2);
x_46 = l_Lean_Syntax_structEq(x_42, x_44);
if (x_46 == 0)
{
lean_dec(x_45);
lean_dec(x_43);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_47 = lean_array_get_size(x_43);
x_48 = lean_array_get_size(x_45);
x_49 = lean_nat_dec_eq(x_47, x_48);
lean_dec(x_48);
if (x_49 == 0)
{
lean_dec(x_47);
lean_dec(x_45);
lean_dec(x_43);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___redArg(x_43, x_45, x_47);
lean_dec(x_45);
lean_dec(x_43);
return x_50;
}
}
}
else
{
lean_object* x_51; uint8_t x_52; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_unbox(x_51);
return x_52;
}
}
default: 
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_2, 1);
lean_inc(x_56);
lean_dec(x_2);
x_57 = l_Lean_Syntax_structEq(x_53, x_55);
if (x_57 == 0)
{
lean_dec(x_56);
lean_dec(x_54);
return x_57;
}
else
{
uint8_t x_58; 
x_58 = l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___redArg(x_54, x_56);
lean_dec(x_56);
lean_dec(x_54);
return x_58;
}
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_2);
lean_dec(x_1);
x_59 = lean_box(0);
x_60 = lean_unbox(x_59);
return x_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Array_isEqvAux___at___Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1_spec__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lake_Toml_RBDict_beq___at_____private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142__spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_instBEqValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Toml_Data_Value_0__Lake_Toml_beqValue____x40_Lake_Toml_Data_Value___hyg_142____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_Table_empty() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
x_2 = l_Lake_Toml_RBDict_empty(lean_box(0), lean_box(0), x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Name_quickCmp___boxed), 2, 0);
x_3 = l_Lake_Toml_RBDict_mkEmpty(lean_box(0), lean_box(0), x_2, x_1);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Table_mkEmpty___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_Table_mkEmpty(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_table(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_ref___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_Value_ref(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_Toml_ppString_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
lean_object* x_6; uint32_t x_7; lean_object* x_8; uint32_t x_9; uint8_t x_10; 
x_6 = lean_string_utf8_next(x_1, x_3);
x_7 = lean_string_utf8_get(x_1, x_3);
lean_dec(x_3);
x_8 = lean_unsigned_to_nat(8u);
x_9 = l_Char_ofNat(x_8);
x_10 = l_instDecidableEqChar(x_7, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint32_t x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(9u);
x_12 = l_Char_ofNat(x_11);
x_13 = l_instDecidableEqChar(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(10u);
x_15 = l_Char_ofNat(x_14);
x_16 = l_instDecidableEqChar(x_7, x_15);
if (x_16 == 0)
{
lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_17 = lean_unsigned_to_nat(12u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_7, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(13u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_7, x_21);
if (x_22 == 0)
{
lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_23 = lean_unsigned_to_nat(34u);
x_24 = l_Char_ofNat(x_23);
x_25 = l_instDecidableEqChar(x_7, x_24);
if (x_25 == 0)
{
lean_object* x_26; uint32_t x_27; uint8_t x_28; 
x_26 = lean_unsigned_to_nat(92u);
x_27 = l_Char_ofNat(x_26);
x_28 = l_instDecidableEqChar(x_7, x_27);
if (x_28 == 0)
{
uint8_t x_29; lean_object* x_45; uint32_t x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(32u);
x_46 = lean_uint32_of_nat(x_45);
x_47 = lean_uint32_dec_lt(x_7, x_46);
if (x_47 == 0)
{
lean_object* x_48; uint32_t x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(127u);
x_49 = lean_uint32_of_nat(x_48);
x_50 = lean_uint32_dec_eq(x_7, x_49);
x_29 = x_50;
goto block_44;
}
else
{
x_29 = x_47;
goto block_44;
}
block_44:
{
if (x_29 == 0)
{
lean_object* x_30; 
x_30 = lean_string_push(x_4, x_7);
x_3 = x_6;
x_4 = x_30;
goto _start;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint32_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_32 = lean_mk_string_unchecked("\\u", 2, 2);
x_33 = lean_string_append(x_4, x_32);
lean_dec(x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint32_to_nat(x_7);
x_36 = l_Nat_toDigits(x_34, x_35);
x_37 = lean_string_mk(x_36);
x_38 = lean_unsigned_to_nat(48u);
x_39 = l_Char_ofNat(x_38);
x_40 = lean_unsigned_to_nat(4u);
x_41 = l_Lake_lpad(x_37, x_39, x_40);
lean_dec(x_37);
x_42 = lean_string_append(x_33, x_41);
lean_dec(x_41);
x_3 = x_6;
x_4 = x_42;
goto _start;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_mk_string_unchecked("\\\\", 2, 2);
x_52 = lean_string_append(x_4, x_51);
lean_dec(x_51);
x_3 = x_6;
x_4 = x_52;
goto _start;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_mk_string_unchecked("\\\"", 2, 2);
x_55 = lean_string_append(x_4, x_54);
lean_dec(x_54);
x_3 = x_6;
x_4 = x_55;
goto _start;
}
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_mk_string_unchecked("\\r", 2, 2);
x_58 = lean_string_append(x_4, x_57);
lean_dec(x_57);
x_3 = x_6;
x_4 = x_58;
goto _start;
}
}
else
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_mk_string_unchecked("\\f", 2, 2);
x_61 = lean_string_append(x_4, x_60);
lean_dec(x_60);
x_3 = x_6;
x_4 = x_61;
goto _start;
}
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_mk_string_unchecked("\\n", 2, 2);
x_64 = lean_string_append(x_4, x_63);
lean_dec(x_63);
x_3 = x_6;
x_4 = x_64;
goto _start;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_mk_string_unchecked("\\t", 2, 2);
x_67 = lean_string_append(x_4, x_66);
lean_dec(x_66);
x_3 = x_6;
x_4 = x_67;
goto _start;
}
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_mk_string_unchecked("\\b", 2, 2);
x_70 = lean_string_append(x_4, x_69);
lean_dec(x_69);
x_3 = x_6;
x_4 = x_70;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint32_t x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("\"", 1, 1);
x_3 = lean_string_utf8_byte_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = l_String_foldlAux___at___Lake_Toml_ppString_spec__0(x_1, x_3, x_4, x_2);
lean_dec(x_3);
x_6 = lean_unsigned_to_nat(34u);
x_7 = l_Char_ofNat(x_6);
x_8 = lean_string_push(x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_String_foldlAux___at___Lake_Toml_ppString_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_String_foldlAux___at___Lake_Toml_ppString_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppString___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_ppString(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at___Lake_Toml_ppSimpleKey_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_7; uint8_t x_8; 
x_7 = lean_nat_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
uint32_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_20; uint8_t x_28; lean_object* x_36; uint32_t x_37; uint8_t x_38; 
x_10 = lean_string_utf8_get(x_1, x_3);
x_36 = lean_unsigned_to_nat(65u);
x_37 = lean_uint32_of_nat(x_36);
x_38 = lean_uint32_dec_le(x_37, x_10);
if (x_38 == 0)
{
x_28 = x_38;
goto block_35;
}
else
{
lean_object* x_39; uint32_t x_40; uint8_t x_41; 
x_39 = lean_unsigned_to_nat(90u);
x_40 = lean_uint32_of_nat(x_39);
x_41 = lean_uint32_dec_le(x_10, x_40);
x_28 = x_41;
goto block_35;
}
block_19:
{
if (x_12 == 0)
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(95u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_10, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint32_t x_17; uint8_t x_18; 
x_16 = lean_unsigned_to_nat(45u);
x_17 = l_Char_ofNat(x_16);
x_18 = l_instDecidableEqChar(x_10, x_17);
x_8 = x_18;
goto block_9;
}
else
{
x_8 = x_15;
goto block_9;
}
}
else
{
if (x_11 == 0)
{
goto block_6;
}
else
{
lean_dec(x_3);
return x_11;
}
}
}
block_27:
{
if (x_20 == 0)
{
lean_object* x_21; uint32_t x_22; uint8_t x_23; 
x_21 = lean_unsigned_to_nat(48u);
x_22 = lean_uint32_of_nat(x_21);
x_23 = lean_uint32_dec_le(x_22, x_10);
if (x_23 == 0)
{
x_11 = x_20;
x_12 = x_23;
goto block_19;
}
else
{
lean_object* x_24; uint32_t x_25; uint8_t x_26; 
x_24 = lean_unsigned_to_nat(57u);
x_25 = lean_uint32_of_nat(x_24);
x_26 = lean_uint32_dec_le(x_10, x_25);
x_11 = x_20;
x_12 = x_26;
goto block_19;
}
}
else
{
goto block_6;
}
}
block_35:
{
if (x_28 == 0)
{
lean_object* x_29; uint32_t x_30; uint8_t x_31; 
x_29 = lean_unsigned_to_nat(97u);
x_30 = lean_uint32_of_nat(x_29);
x_31 = lean_uint32_dec_le(x_30, x_10);
if (x_31 == 0)
{
x_20 = x_31;
goto block_27;
}
else
{
lean_object* x_32; uint32_t x_33; uint8_t x_34; 
x_32 = lean_unsigned_to_nat(122u);
x_33 = lean_uint32_of_nat(x_32);
x_34 = lean_uint32_dec_le(x_10, x_33);
x_20 = x_34;
goto block_27;
}
}
else
{
goto block_6;
}
}
}
block_6:
{
lean_object* x_4; 
x_4 = lean_string_utf8_next(x_1, x_3);
lean_dec(x_3);
x_3 = x_4;
goto _start;
}
block_9:
{
if (x_8 == 0)
{
lean_dec(x_3);
return x_7;
}
else
{
goto block_6;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_string_utf8_byte_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = l_String_anyAux___at___Lake_Toml_ppSimpleKey_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
if (x_4 == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lake_Toml_ppString(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at___Lake_Toml_ppSimpleKey_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_String_anyAux___at___Lake_Toml_ppSimpleKey_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppSimpleKey___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_ppSimpleKey(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = l_Lean_Name_isAnonymous(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = l_Lake_Toml_ppKey(x_2);
x_6 = lean_mk_string_unchecked(".", 1, 1);
x_7 = lean_string_append(x_5, x_6);
lean_dec(x_6);
x_8 = l_Lake_Toml_ppSimpleKey(x_3);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
return x_9;
}
else
{
lean_object* x_10; 
x_10 = l_Lake_Toml_ppSimpleKey(x_3);
return x_10;
}
}
else
{
lean_object* x_11; 
x_11 = lean_mk_string_unchecked("", 0, 0);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppKey___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_ppKey(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineTable_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_3, x_2, x_8);
x_10 = l_Lake_Toml_ppKey(x_6);
lean_dec(x_6);
x_11 = lean_mk_string_unchecked(" = ", 3, 3);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
x_13 = l_Lake_Toml_Value_toString(x_7);
x_14 = lean_string_append(x_12, x_13);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_18 = lean_array_uset(x_9, x_2, x_14);
x_2 = x_17;
x_3 = x_18;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineTable(lean_object* x_1) {
_start:
{
lean_object* x_2; size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_array_size(x_2);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineTable_spec__0(x_3, x_5, x_2);
x_7 = lean_mk_string_unchecked("{", 1, 1);
x_8 = lean_mk_string_unchecked(", ", 2, 2);
x_9 = lean_array_to_list(x_6);
x_10 = l_String_intercalate(x_8, x_9);
lean_dec(x_8);
x_11 = lean_string_append(x_7, x_10);
lean_dec(x_10);
x_12 = lean_mk_string_unchecked("}", 1, 1);
x_13 = lean_string_append(x_11, x_12);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_Value_toString(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_3 = l_Lake_Toml_ppString(x_2);
lean_dec(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_nat_abs(x_4);
lean_dec(x_4);
x_9 = l___private_Init_Data_Repr_0__Nat_reprFast(x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_10 = lean_nat_abs(x_4);
lean_dec(x_4);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_mk_string_unchecked("-", 1, 1);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_12, x_14);
lean_dec(x_12);
x_16 = l___private_Init_Data_Repr_0__Nat_reprFast(x_15);
x_17 = lean_string_append(x_13, x_16);
lean_dec(x_16);
return x_17;
}
}
case 2:
{
double x_18; lean_object* x_19; 
x_18 = lean_ctor_get_float(x_1, sizeof(void*)*1);
lean_dec(x_1);
x_19 = lean_float_to_string(x_18);
return x_19;
}
case 3:
{
uint8_t x_20; 
x_20 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
lean_dec(x_1);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_mk_string_unchecked("false", 5, 5);
return x_21;
}
else
{
lean_object* x_22; 
x_22 = lean_mk_string_unchecked("true", 4, 4);
return x_22;
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
x_24 = l_Lake_Toml_DateTime_toString(x_23);
return x_24;
}
case 5:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lake_Toml_ppInlineArray(x_25);
return x_26;
}
default: 
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lake_Toml_ppInlineTable(x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineArray_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lake_Toml_Value_toString(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppInlineArray(lean_object* x_1) {
_start:
{
size_t x_2; lean_object* x_3; size_t x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_array_size(x_1);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_usize_of_nat(x_3);
x_5 = l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineArray_spec__0(x_2, x_4, x_1);
x_6 = lean_mk_string_unchecked("[", 1, 1);
x_7 = lean_mk_string_unchecked(", ", 2, 2);
x_8 = lean_array_to_list(x_5);
x_9 = l_String_intercalate(x_7, x_8);
lean_dec(x_7);
x_10 = lean_string_append(x_6, x_9);
lean_dec(x_9);
x_11 = lean_mk_string_unchecked("]", 1, 1);
x_12 = lean_string_append(x_10, x_11);
lean_dec(x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineTable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineTable_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineArray_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lake_Toml_ppInlineArray_spec__0(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_instToStringValue() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_Value_toString), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable_appendKeyval(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = l_Lake_Toml_ppKey(x_2);
x_5 = lean_mk_string_unchecked(" = ", 3, 3);
x_6 = lean_string_append(x_4, x_5);
lean_dec(x_5);
x_7 = l_Lake_Toml_Value_toString(x_3);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_mk_string_unchecked("\n", 1, 1);
x_10 = lean_string_append(x_8, x_9);
lean_dec(x_9);
x_11 = lean_string_append(x_1, x_10);
lean_dec(x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable_appendKeyval___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Toml_ppTable_appendKeyval(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lake_Toml_ppTable_appendKeyval(x_4, x_7, x_8);
lean_dec(x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_2 = x_12;
x_4 = x_9;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_18) == 6)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_string_unchecked("[[", 2, 2);
x_22 = l_Lake_Toml_ppKey(x_1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("]]\n", 3, 3);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_5, x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_20, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
x_12 = x_26;
goto block_16;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
x_12 = x_26;
goto block_16;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_20);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0(x_27, x_31, x_32, x_26);
lean_dec(x_27);
x_12 = x_33;
goto block_16;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_18);
lean_dec(x_5);
x_34 = lean_mk_string_unchecked("Lake.Toml.Data.Value", 20, 20);
x_35 = lean_mk_string_unchecked("Lake.Toml.ppTable", 17, 17);
x_36 = lean_unsigned_to_nat(121u);
x_37 = lean_unsigned_to_nat(17u);
x_38 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_Name_getString_x21_spec__0(x_39);
x_6 = x_40;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
block_16:
{
lean_object* x_13; uint32_t x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(10u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_string_push(x_12, x_14);
x_6 = x_15;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_3, x_4);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_18) == 6)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_mk_string_unchecked("[[", 2, 2);
x_22 = l_Lake_Toml_ppKey(x_1);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_mk_string_unchecked("]]\n", 3, 3);
x_25 = lean_string_append(x_23, x_24);
lean_dec(x_24);
x_26 = lean_string_append(x_5, x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_array_get_size(x_27);
x_29 = lean_nat_dec_lt(x_20, x_28);
if (x_29 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
x_12 = x_26;
goto block_16;
}
else
{
uint8_t x_30; 
x_30 = lean_nat_dec_le(x_28, x_28);
if (x_30 == 0)
{
lean_dec(x_28);
lean_dec(x_27);
x_12 = x_26;
goto block_16;
}
else
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_usize_of_nat(x_20);
x_32 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_33 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0(x_27, x_31, x_32, x_26);
lean_dec(x_27);
x_12 = x_33;
goto block_16;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_18);
lean_dec(x_5);
x_34 = lean_mk_string_unchecked("Lake.Toml.Data.Value", 20, 20);
x_35 = lean_mk_string_unchecked("Lake.Toml.ppTable", 17, 17);
x_36 = lean_unsigned_to_nat(121u);
x_37 = lean_unsigned_to_nat(17u);
x_38 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_Name_getString_x21_spec__0(x_39);
x_6 = x_40;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1_spec__1(x_1, x_2, x_9, x_4, x_6);
return x_10;
}
block_16:
{
lean_object* x_13; uint32_t x_14; lean_object* x_15; 
x_13 = lean_unsigned_to_nat(10u);
x_14 = l_Char_ofNat(x_13);
x_15 = lean_string_push(x_12, x_14);
x_6 = x_15;
goto block_11;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lake_Toml_ppTable_spec__3(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_array_uget(x_2, x_3);
if (lean_obj_tag(x_7) == 6)
{
lean_dec(x_7);
if (x_1 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
uint8_t x_12; 
x_12 = lean_unbox(x_6);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_7);
x_13 = lean_unbox(x_6);
return x_13;
}
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_20 = lean_array_uget(x_1, x_2);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 5:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Array_isEmpty___redArg(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_35; uint8_t x_57; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_24);
x_57 = lean_nat_dec_lt(x_26, x_27);
if (x_57 == 0)
{
x_35 = x_25;
goto block_56;
}
else
{
if (x_57 == 0)
{
x_35 = x_25;
goto block_56;
}
else
{
size_t x_58; size_t x_59; uint8_t x_60; 
x_58 = lean_usize_of_nat(x_26);
x_59 = lean_usize_of_nat(x_27);
x_60 = l_Array_anyMUnsafe_any___at___Lake_Toml_ppTable_spec__3(x_25, x_24, x_58, x_59);
x_35 = x_60;
goto block_56;
}
}
block_34:
{
uint8_t x_28; 
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_30 = lean_usize_of_nat(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1(x_22, x_24, x_30, x_31, x_13);
lean_dec(x_24);
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_23;
}
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
x_5 = x_33;
goto block_10;
}
}
}
block_56:
{
if (x_35 == 0)
{
goto block_34;
}
else
{
if (x_25 == 0)
{
uint8_t x_36; 
lean_dec(x_27);
lean_dec(x_23);
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_4, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_4, 0);
lean_dec(x_38);
x_39 = l_Lake_Toml_ppKey(x_22);
lean_dec(x_22);
x_40 = lean_mk_string_unchecked(" = ", 3, 3);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = l_Lake_Toml_ppInlineArray(x_24);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = lean_mk_string_unchecked("\n", 1, 1);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = lean_string_append(x_12, x_45);
lean_dec(x_45);
lean_ctor_set(x_4, 0, x_46);
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_4);
x_47 = l_Lake_Toml_ppKey(x_22);
lean_dec(x_22);
x_48 = lean_mk_string_unchecked(" = ", 3, 3);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = l_Lake_Toml_ppInlineArray(x_24);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("\n", 1, 1);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = lean_string_append(x_12, x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_13);
x_5 = x_55;
goto block_10;
}
}
else
{
goto block_34;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_24);
lean_dec(x_4);
x_61 = l_Lake_Toml_ppKey(x_22);
lean_dec(x_22);
x_62 = lean_mk_string_unchecked(" = []\n", 6, 6);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = lean_string_append(x_12, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_23)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_23;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_13);
x_5 = x_65;
goto block_10;
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_4);
x_66 = lean_ctor_get(x_20, 0);
lean_inc(x_66);
lean_dec(x_20);
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_dec(x_21);
x_68 = lean_mk_string_unchecked("[", 1, 1);
x_69 = l_Lake_Toml_ppKey(x_66);
lean_dec(x_66);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = lean_mk_string_unchecked("]\n", 2, 2);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_73 = lean_string_append(x_13, x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
lean_dec(x_67);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_get_size(x_74);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_dec(x_76);
lean_dec(x_74);
x_14 = x_73;
goto block_19;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_76, x_76);
if (x_78 == 0)
{
lean_dec(x_76);
lean_dec(x_74);
x_14 = x_73;
goto block_19;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
x_79 = lean_usize_of_nat(x_75);
x_80 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_81 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0(x_74, x_79, x_80, x_73);
lean_dec(x_74);
x_14 = x_81;
goto block_19;
}
}
}
default: 
{
uint8_t x_82; 
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_20);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_20, 0);
x_84 = lean_ctor_get(x_20, 1);
lean_dec(x_84);
x_85 = l_Lake_Toml_ppTable_appendKeyval(x_12, x_83, x_21);
lean_dec(x_83);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 0, x_85);
x_5 = x_20;
goto block_10;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
lean_dec(x_20);
x_87 = l_Lake_Toml_ppTable_appendKeyval(x_12, x_86, x_21);
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_13);
x_5 = x_88;
goto block_10;
}
}
}
block_19:
{
lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(10u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_string_push(x_14, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_5 = x_18;
goto block_10;
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_20 = lean_array_uget(x_1, x_2);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
switch (lean_obj_tag(x_21)) {
case 5:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
if (lean_is_exclusive(x_20)) {
 lean_ctor_release(x_20, 0);
 lean_ctor_release(x_20, 1);
 x_23 = x_20;
} else {
 lean_dec_ref(x_20);
 x_23 = lean_box(0);
}
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = l_Array_isEmpty___redArg(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; uint8_t x_35; uint8_t x_57; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_24);
x_57 = lean_nat_dec_lt(x_26, x_27);
if (x_57 == 0)
{
x_35 = x_25;
goto block_56;
}
else
{
if (x_57 == 0)
{
x_35 = x_25;
goto block_56;
}
else
{
size_t x_58; size_t x_59; uint8_t x_60; 
x_58 = lean_usize_of_nat(x_26);
x_59 = lean_usize_of_nat(x_27);
x_60 = l_Array_anyMUnsafe_any___at___Lake_Toml_ppTable_spec__3(x_25, x_24, x_58, x_59);
x_35 = x_60;
goto block_56;
}
}
block_34:
{
uint8_t x_28; 
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_13);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
x_30 = lean_usize_of_nat(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1(x_22, x_24, x_30, x_31, x_13);
lean_dec(x_24);
lean_dec(x_22);
if (lean_is_scalar(x_23)) {
 x_33 = lean_alloc_ctor(0, 2, 0);
} else {
 x_33 = x_23;
}
lean_ctor_set(x_33, 0, x_12);
lean_ctor_set(x_33, 1, x_32);
x_5 = x_33;
goto block_10;
}
}
}
block_56:
{
if (x_35 == 0)
{
goto block_34;
}
else
{
if (x_25 == 0)
{
uint8_t x_36; 
lean_dec(x_27);
lean_dec(x_23);
x_36 = !lean_is_exclusive(x_4);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_37 = lean_ctor_get(x_4, 1);
lean_dec(x_37);
x_38 = lean_ctor_get(x_4, 0);
lean_dec(x_38);
x_39 = l_Lake_Toml_ppKey(x_22);
lean_dec(x_22);
x_40 = lean_mk_string_unchecked(" = ", 3, 3);
x_41 = lean_string_append(x_39, x_40);
lean_dec(x_40);
x_42 = l_Lake_Toml_ppInlineArray(x_24);
x_43 = lean_string_append(x_41, x_42);
lean_dec(x_42);
x_44 = lean_mk_string_unchecked("\n", 1, 1);
x_45 = lean_string_append(x_43, x_44);
lean_dec(x_44);
x_46 = lean_string_append(x_12, x_45);
lean_dec(x_45);
lean_ctor_set(x_4, 0, x_46);
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_4);
x_47 = l_Lake_Toml_ppKey(x_22);
lean_dec(x_22);
x_48 = lean_mk_string_unchecked(" = ", 3, 3);
x_49 = lean_string_append(x_47, x_48);
lean_dec(x_48);
x_50 = l_Lake_Toml_ppInlineArray(x_24);
x_51 = lean_string_append(x_49, x_50);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("\n", 1, 1);
x_53 = lean_string_append(x_51, x_52);
lean_dec(x_52);
x_54 = lean_string_append(x_12, x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_13);
x_5 = x_55;
goto block_10;
}
}
else
{
goto block_34;
}
}
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_24);
lean_dec(x_4);
x_61 = l_Lake_Toml_ppKey(x_22);
lean_dec(x_22);
x_62 = lean_mk_string_unchecked(" = []\n", 6, 6);
x_63 = lean_string_append(x_61, x_62);
lean_dec(x_62);
x_64 = lean_string_append(x_12, x_63);
lean_dec(x_63);
if (lean_is_scalar(x_23)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_23;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_13);
x_5 = x_65;
goto block_10;
}
}
case 6:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
lean_dec(x_4);
x_66 = lean_ctor_get(x_20, 0);
lean_inc(x_66);
lean_dec(x_20);
x_67 = lean_ctor_get(x_21, 1);
lean_inc(x_67);
lean_dec(x_21);
x_68 = lean_mk_string_unchecked("[", 1, 1);
x_69 = l_Lake_Toml_ppKey(x_66);
lean_dec(x_66);
x_70 = lean_string_append(x_68, x_69);
lean_dec(x_69);
x_71 = lean_mk_string_unchecked("]\n", 2, 2);
x_72 = lean_string_append(x_70, x_71);
lean_dec(x_71);
x_73 = lean_string_append(x_13, x_72);
lean_dec(x_72);
x_74 = lean_ctor_get(x_67, 0);
lean_inc(x_74);
lean_dec(x_67);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_get_size(x_74);
x_77 = lean_nat_dec_lt(x_75, x_76);
if (x_77 == 0)
{
lean_dec(x_76);
lean_dec(x_74);
x_14 = x_73;
goto block_19;
}
else
{
uint8_t x_78; 
x_78 = lean_nat_dec_le(x_76, x_76);
if (x_78 == 0)
{
lean_dec(x_76);
lean_dec(x_74);
x_14 = x_73;
goto block_19;
}
else
{
size_t x_79; size_t x_80; lean_object* x_81; 
x_79 = lean_usize_of_nat(x_75);
x_80 = lean_usize_of_nat(x_76);
lean_dec(x_76);
x_81 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0(x_74, x_79, x_80, x_73);
lean_dec(x_74);
x_14 = x_81;
goto block_19;
}
}
}
default: 
{
uint8_t x_82; 
lean_dec(x_4);
x_82 = !lean_is_exclusive(x_20);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_20, 0);
x_84 = lean_ctor_get(x_20, 1);
lean_dec(x_84);
x_85 = l_Lake_Toml_ppTable_appendKeyval(x_12, x_83, x_21);
lean_dec(x_83);
lean_ctor_set(x_20, 1, x_13);
lean_ctor_set(x_20, 0, x_85);
x_5 = x_20;
goto block_10;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_20, 0);
lean_inc(x_86);
lean_dec(x_20);
x_87 = l_Lake_Toml_ppTable_appendKeyval(x_12, x_86, x_21);
lean_dec(x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_13);
x_5 = x_88;
goto block_10;
}
}
}
block_19:
{
lean_object* x_15; uint32_t x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(10u);
x_16 = l_Char_ofNat(x_15);
x_17 = lean_string_push(x_14, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
x_5 = x_18;
goto block_10;
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
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4_spec__4(x_1, x_8, x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_16; uint8_t x_17; 
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(0u);
x_16 = lean_array_get_size(x_3);
x_17 = lean_nat_dec_lt(x_4, x_16);
if (x_17 == 0)
{
lean_dec(x_16);
lean_inc(x_2);
x_5 = x_2;
x_6 = x_2;
goto block_15;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_16, x_16);
if (x_18 == 0)
{
lean_dec(x_16);
lean_inc(x_2);
x_5 = x_2;
x_6 = x_2;
goto block_15;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_inc(x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_2);
lean_ctor_set(x_19, 1, x_2);
x_20 = lean_usize_of_nat(x_4);
x_21 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_22 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4(x_3, x_20, x_21, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_5 = x_23;
x_6 = x_24;
goto block_15;
}
}
block_15:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_unsigned_to_nat(10u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_string_push(x_5, x_8);
x_10 = lean_string_append(x_9, x_6);
lean_dec(x_6);
x_11 = lean_string_utf8_byte_size(x_10);
x_12 = l_Substring_takeRightWhileAux___at___Lean_Syntax_isToken_spec__0(x_10, x_4, x_11);
x_13 = lean_string_utf8_extract(x_10, x_4, x_12);
lean_dec(x_12);
lean_dec(x_10);
x_14 = lean_string_push(x_13, x_8);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lake_Toml_ppTable_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lake_Toml_ppTable_spec__3(x_5, x_2, x_6, x_7);
lean_dec(x_2);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lake_Toml_ppTable_spec__4(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_ppTable___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_ppTable(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Init_Data_Float(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Data_Dict(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_Data_DateTime(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Data_Value(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Float(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_Dict(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_Data_DateTime(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_instInhabitedValue = _init_l_Lake_Toml_instInhabitedValue();
lean_mark_persistent(l_Lake_Toml_instInhabitedValue);
l_Lake_Toml_instBEqValue = _init_l_Lake_Toml_instBEqValue();
lean_mark_persistent(l_Lake_Toml_instBEqValue);
l_Lake_Toml_Table_empty = _init_l_Lake_Toml_Table_empty();
lean_mark_persistent(l_Lake_Toml_Table_empty);
l_Lake_Toml_instToStringValue = _init_l_Lake_Toml_instToStringValue();
lean_mark_persistent(l_Lake_Toml_instToStringValue);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
