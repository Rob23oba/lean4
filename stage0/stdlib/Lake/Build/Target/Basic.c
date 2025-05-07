// Lean compiler output
// Module: Lake.Build.Target.Basic
// Imports: Lake.Build.Key
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
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___lam__0(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lake_PartialBuildKey_toString(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringTarget___lam__0(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_instToStringTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_instReprTarget(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_17; uint8_t x_18; 
x_17 = lean_unsigned_to_nat(1024u);
x_18 = lean_nat_dec_le(x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_to_int(x_19);
x_3 = x_20;
goto block_16;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_to_int(x_21);
x_3 = x_22;
goto block_16;
}
block_16:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_4 = lean_mk_string_unchecked("Lake.Target.mk", 14, 14);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_unsigned_to_nat(1024u);
x_9 = l___private_Lake_Build_Key_0__Lake_reprBuildKey____x40_Lake_Build_Key___hyg_69_(x_1, x_8);
x_10 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_13, 0, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*1, x_14);
x_15 = l_Repr_addAppParen(x_13, x_2);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Target_repr___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Target_repr___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Target_repr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Target_repr(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_instReprTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_Target_repr___boxed), 3, 1);
lean_closure_set(x_2, 0, lean_box(0));
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringTarget___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_PartialBuildKey_toString(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instToStringTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instToStringTarget___lam__0), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_alloc_closure((void*)(l_Lake_instCoePartialBuildKeyTarget___lam__0___boxed), 1, 0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_instCoePartialBuildKeyTarget___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_instCoePartialBuildKeyTarget___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
lean_object* initialize_Lake_Build_Key(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Build_Target_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Build_Key(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
