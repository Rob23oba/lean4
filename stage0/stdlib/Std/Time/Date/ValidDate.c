// Lean compiler output
// Module: Std.Time.Date.ValidDate
// Imports: Std.Internal.Rat Std.Time.Date.Unit.Day Std.Time.Date.Unit.Month
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
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_days(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal___boxed(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate(uint8_t);
uint8_t l_instDecidableEqProd___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instOrdValidDate___lam__0(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Time_Month_instOrdinalDecidableEq___boxed(lean_object*, lean_object*);
lean_object* l_Std_Time_Month_Ordinal_cumulativeDays(uint8_t, lean_object*);
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate(uint8_t, lean_object*, lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
lean_object* l_Std_Time_Day_instOrdinalDecidableEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___boxed(lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate(uint8_t);
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate(uint8_t x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_unsigned_to_nat(11u);
x_5 = lean_nat_to_int(x_4);
x_6 = lean_int_add(x_3, x_5);
lean_dec(x_5);
x_7 = lean_int_sub(x_6, x_3);
lean_dec(x_6);
x_8 = lean_int_add(x_7, x_3);
lean_dec(x_7);
x_9 = lean_int_sub(x_3, x_3);
x_10 = lean_int_emod(x_9, x_8);
x_11 = lean_int_add(x_10, x_8);
lean_dec(x_10);
x_12 = lean_int_emod(x_11, x_8);
lean_dec(x_8);
lean_dec(x_11);
x_13 = lean_int_add(x_12, x_3);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(30u);
x_15 = lean_nat_to_int(x_14);
x_16 = lean_int_add(x_3, x_15);
lean_dec(x_15);
x_17 = lean_int_sub(x_16, x_3);
lean_dec(x_16);
x_18 = lean_int_add(x_17, x_3);
lean_dec(x_17);
x_19 = lean_int_emod(x_9, x_18);
lean_dec(x_9);
x_20 = lean_int_add(x_19, x_18);
lean_dec(x_19);
x_21 = lean_int_emod(x_20, x_18);
lean_dec(x_18);
lean_dec(x_20);
x_22 = lean_int_add(x_21, x_3);
lean_dec(x_3);
lean_dec(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instInhabitedValidDate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Time_instInhabitedValidDate(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_alloc_closure((void*)(l_Std_Time_Month_instOrdinalDecidableEq___boxed), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Std_Time_Day_instOrdinalDecidableEq___boxed), 2, 0);
x_5 = l_instDecidableEqProd___redArg(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instDecidableEqValidDate(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_Time_instDecidableEqValidDate___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_instDecidableEqValidDate___redArg(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instDecidableEqValidDate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox(x_1);
lean_dec(x_1);
x_5 = l_Std_Time_instDecidableEqValidDate(x_4, x_2, x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Std_Time_instOrdValidDate___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_int_dec_lt(x_3, x_4);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = lean_int_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(2);
x_8 = lean_unbox(x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_int_dec_lt(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_int_dec_eq(x_9, x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(2);
x_14 = lean_unbox(x_13);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Std_Time_instOrdValidDate___lam__0___boxed), 2, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Time_instOrdValidDate___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_instOrdValidDate___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Std_Time_instOrdValidDate(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Std_Time_Month_Ordinal_cumulativeDays(x_1, x_3);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_int_add(x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_dayOfYear___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Std_Time_ValidDate_dayOfYear(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Std_Time_Month_Ordinal_days(x_1, x_3);
x_6 = lean_int_add(x_4, x_5);
lean_dec(x_5);
x_7 = lean_int_dec_le(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_to_int(x_8);
x_10 = lean_int_add(x_3, x_9);
lean_dec(x_9);
lean_dec(x_3);
x_3 = x_10;
x_4 = x_6;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
x_12 = lean_int_neg(x_4);
lean_dec(x_4);
x_13 = lean_int_add(x_2, x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Std_Time_ValidDate_ofOrdinal_go___redArg(x_1, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Std_Time_ValidDate_ofOrdinal_go___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l_Std_Time_ValidDate_ofOrdinal_go(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_unsigned_to_nat(11u);
x_6 = lean_nat_to_int(x_5);
x_7 = lean_int_add(x_4, x_6);
lean_dec(x_6);
x_8 = lean_int_sub(x_7, x_4);
lean_dec(x_7);
x_9 = lean_int_add(x_8, x_4);
lean_dec(x_8);
x_10 = lean_int_sub(x_4, x_4);
x_11 = lean_int_emod(x_10, x_9);
lean_dec(x_10);
x_12 = lean_int_add(x_11, x_9);
lean_dec(x_11);
x_13 = lean_int_emod(x_12, x_9);
lean_dec(x_9);
lean_dec(x_12);
x_14 = lean_int_add(x_13, x_4);
lean_dec(x_4);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_to_int(x_15);
x_17 = l_Std_Time_ValidDate_ofOrdinal_go___redArg(x_1, x_2, x_14, x_16);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Time_ValidDate_ofOrdinal___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Std_Time_ValidDate_ofOrdinal(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
lean_object* initialize_Std_Internal_Rat(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Day(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Time_Date_Unit_Month(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Time_Date_ValidDate(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Internal_Rat(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Day(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Time_Date_Unit_Month(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
