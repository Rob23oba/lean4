// Lean compiler output
// Module: Lake.Version
// Imports: Init.Data.ToString
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
LEAN_EXPORT lean_object* l_Lake_versionStringCore;
extern lean_object* l_Lean_githash;
LEAN_EXPORT lean_object* l_Lake_version_specialDesc;
LEAN_EXPORT lean_object* l_Lake_versionString;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
extern uint8_t l_Lean_version_isRelease;
lean_object* lean_string_utf8_byte_size(lean_object*);
extern lean_object* l_Lean_versionString;
LEAN_EXPORT lean_object* l_Lake_version_patch;
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_version_minor;
LEAN_EXPORT uint8_t l_Lake_version_isRelease;
uint8_t l_instDecidableNot___redArg(uint8_t);
LEAN_EXPORT lean_object* l_Lake_version_major;
lean_object* lean_string_append(lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lake_uiVersionString;
static lean_object* _init_l_Lake_version_major() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(5u);
return x_1;
}
}
static lean_object* _init_l_Lake_version_minor() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static lean_object* _init_l_Lake_version_patch() {
_start:
{
lean_object* x_1; 
x_1 = lean_unsigned_to_nat(0u);
return x_1;
}
}
static uint8_t _init_l_Lake_version_isRelease() {
_start:
{
uint8_t x_1; 
x_1 = l_Lean_version_isRelease;
return x_1;
}
}
static lean_object* _init_l_Lake_version_specialDesc() {
_start:
{
uint8_t x_1; uint8_t x_11; 
x_11 = l_Lean_version_isRelease;
if (x_11 == 0)
{
x_1 = x_11;
goto block_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = l_Lean_githash;
x_13 = lean_string_utf8_byte_size(x_12);
x_14 = lean_unsigned_to_nat(0u);
x_15 = l_instDecidableEqPos(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
x_1 = x_11;
goto block_10;
}
else
{
lean_object* x_16; 
x_16 = lean_mk_string_unchecked("src", 3, 3);
return x_16;
}
}
block_10:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("src", 3, 3);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = l_Lean_githash;
x_4 = lean_unsigned_to_nat(7u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_string_utf8_byte_size(x_3);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_3);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Substring_nextn(x_7, x_4, x_5);
lean_dec(x_7);
x_9 = lean_string_utf8_extract(x_3, x_5, x_8);
lean_dec(x_8);
return x_9;
}
}
}
}
static lean_object* _init_l_Lake_versionStringCore() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_unsigned_to_nat(5u);
x_2 = l___private_Init_Data_Repr_0__Nat_reprFast(x_1);
x_3 = lean_mk_string_unchecked(".", 1, 1);
x_4 = lean_string_append(x_2, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_7 = lean_string_append(x_4, x_6);
x_8 = lean_string_append(x_7, x_3);
lean_dec(x_3);
x_9 = lean_string_append(x_8, x_6);
lean_dec(x_6);
return x_9;
}
}
static lean_object* _init_l_Lake_versionString() {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; 
x_1 = l_Lake_version_specialDesc;
x_2 = lean_mk_string_unchecked("", 0, 0);
x_3 = lean_string_dec_eq(x_1, x_2);
lean_dec(x_2);
x_4 = l_instDecidableNot___redArg(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = l_Lake_versionStringCore;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = l_Lake_versionStringCore;
x_7 = lean_mk_string_unchecked("-", 1, 1);
x_8 = lean_string_append(x_6, x_7);
lean_dec(x_7);
x_9 = lean_string_append(x_8, x_1);
return x_9;
}
}
}
static lean_object* _init_l_Lake_uiVersionString() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("Lake version ", 13, 13);
x_2 = l_Lake_versionString;
x_3 = lean_string_append(x_1, x_2);
x_4 = lean_mk_string_unchecked(" (Lean version ", 15, 15);
x_5 = lean_string_append(x_3, x_4);
lean_dec(x_4);
x_6 = l_Lean_versionString;
x_7 = lean_string_append(x_5, x_6);
x_8 = lean_mk_string_unchecked(")", 1, 1);
x_9 = lean_string_append(x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
lean_object* initialize_Init_Data_ToString(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Version(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_version_major = _init_l_Lake_version_major();
lean_mark_persistent(l_Lake_version_major);
l_Lake_version_minor = _init_l_Lake_version_minor();
lean_mark_persistent(l_Lake_version_minor);
l_Lake_version_patch = _init_l_Lake_version_patch();
lean_mark_persistent(l_Lake_version_patch);
l_Lake_version_isRelease = _init_l_Lake_version_isRelease();
l_Lake_version_specialDesc = _init_l_Lake_version_specialDesc();
lean_mark_persistent(l_Lake_version_specialDesc);
l_Lake_versionStringCore = _init_l_Lake_versionStringCore();
lean_mark_persistent(l_Lake_versionStringCore);
l_Lake_versionString = _init_l_Lake_versionString();
lean_mark_persistent(l_Lake_versionString);
l_Lake_uiVersionString = _init_l_Lake_uiVersionString();
lean_mark_persistent(l_Lake_uiVersionString);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
