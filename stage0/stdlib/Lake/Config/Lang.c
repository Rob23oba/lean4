// Lean compiler output
// Module: Lake.Config.Lang
// Imports: Init.Data.ToString.Basic
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
LEAN_EXPORT lean_object* l___private_Lake_Config_Lang_0__Lake_reprConfigLang____x40_Lake_Config_Lang___hyg_9_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instDecidableEqConfigLang___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_ConfigLang_ofNat(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Config_Lang_0__Lake_reprConfigLang____x40_Lake_Config_Lang___hyg_9____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringConfigLang;
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instDecidableEqConfigLang(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_instInhabitedConfigLang;
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension(uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx(uint8_t);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_ConfigLang_default;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprConfigLang;
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx(uint8_t x_1) {
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
LEAN_EXPORT lean_object* l_Lake_ConfigLang_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_ConfigLang_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lake_ConfigLang_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_ConfigLang_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ConfigLang_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_ConfigLang_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lake_ConfigLang_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Lang_0__Lake_reprConfigLang____x40_Lake_Config_Lang___hyg_9_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; 
if (x_1 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_unsigned_to_nat(1024u);
x_22 = lean_nat_dec_le(x_21, x_2);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(2u);
x_24 = lean_nat_to_int(x_23);
x_3 = x_24;
goto block_11;
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_to_int(x_25);
x_3 = x_26;
goto block_11;
}
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_unsigned_to_nat(1024u);
x_28 = lean_nat_dec_le(x_27, x_2);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_unsigned_to_nat(2u);
x_30 = lean_nat_to_int(x_29);
x_12 = x_30;
goto block_20;
}
else
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_to_int(x_31);
x_12 = x_32;
goto block_20;
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lake.ConfigLang.lean", 20, 20);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lake.ConfigLang.toml", 20, 20);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Config_Lang_0__Lake_reprConfigLang____x40_Lake_Config_Lang___hyg_9____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lake_Config_Lang_0__Lake_reprConfigLang____x40_Lake_Config_Lang___hyg_9_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_instReprConfigLang() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Config_Lang_0__Lake_reprConfigLang____x40_Lake_Config_Lang___hyg_9____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_ConfigLang_ofNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_dec_eq(x_1, x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(1);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake_ConfigLang_ofNat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_instDecidableEqConfigLang(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lake_ConfigLang_toCtorIdx(x_1);
x_4 = l_Lake_ConfigLang_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_instDecidableEqConfigLang___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lake_instDecidableEqConfigLang(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static uint8_t _init_l_Lake_ConfigLang_default() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(1);
x_2 = lean_unbox(x_1);
return x_2;
}
}
static uint8_t _init_l_Lake_instInhabitedConfigLang() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(1);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_mk_string_unchecked("lean", 4, 4);
x_3 = lean_string_dec_eq(x_1, x_2);
lean_dec(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_mk_string_unchecked("toml", 4, 4);
x_5 = lean_string_dec_eq(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_box(0);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_ofString_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ConfigLang_ofString_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("lean", 4, 4);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("toml", 4, 4);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_ConfigLang_fileExtension___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lake_ConfigLang_fileExtension(x_2);
return x_3;
}
}
static lean_object* _init_l_Lake_instToStringConfigLang() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_ConfigLang_fileExtension___boxed), 1, 0);
return x_1;
}
}
lean_object* initialize_Init_Data_ToString_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Config_Lang(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_instReprConfigLang = _init_l_Lake_instReprConfigLang();
lean_mark_persistent(l_Lake_instReprConfigLang);
l_Lake_ConfigLang_default = _init_l_Lake_ConfigLang_default();
l_Lake_instInhabitedConfigLang = _init_l_Lake_instInhabitedConfigLang();
l_Lake_instToStringConfigLang = _init_l_Lake_instToStringConfigLang();
lean_mark_persistent(l_Lake_instToStringConfigLang);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
