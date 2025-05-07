// Lean compiler output
// Module: Lake.Util.Cli
// Imports: Init.Data.Array.Basic
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
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object*, uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg___lam__0(lean_object*);
lean_object* l_Substring_takeWhileAux(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_posOfAux(lean_object*, uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setArgs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object*);
lean_object* l_Substring_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_setArgs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_consArg___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_ArgList_mk(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgList_mk___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ArgList_mk(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_alloc_closure((void*)(l_Lake_ArgsT_run_x27___redArg___lam__0___boxed), 1, 0);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_1(x_3, x_2);
x_7 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_alloc_closure((void*)(l_Lake_ArgsT_run_x27___redArg___lam__0___boxed), 1, 0);
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
lean_dec(x_3);
x_8 = lean_apply_1(x_5, x_4);
x_9 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_ArgsT_run_x27___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_ArgsT_run_x27___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_getArgs___redArg(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_getArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_getArgs(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_setArgs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_1(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_setArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_6);
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
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lake_takeArg_x3f___redArg___lam__0), 1, 0);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_2(x_3, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArg_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_takeArg_x3f___redArg___lam__0), 1, 0);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
else
{
uint8_t x_4; 
lean_dec(x_1);
x_4 = !lean_is_exclusive(x_2);
if (x_4 == 0)
{
lean_ctor_set_tag(x_2, 0);
return x_2;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_inc(x_5);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_takeArgD___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgD(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lake_takeArgD___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_alloc_closure((void*)(l_Lake_takeArgs___redArg___lam__0), 1, 0);
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_apply_2(x_3, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_takeArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_takeArgs___redArg___lam__0), 1, 0);
x_4 = lean_ctor_get(x_2, 2);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_consArg___redArg___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = lean_ctor_get(x_1, 2);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_2(x_4, lean_box(0), x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_consArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_alloc_closure((void*)(l_Lake_consArg___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_3);
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_2(x_5, lean_box(0), x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_string_utf8_get(x_1, x_4);
x_6 = lean_box_uint32(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_4);
lean_inc(x_9);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_nextn(x_10, x_7, x_8);
lean_dec(x_10);
x_12 = lean_string_utf8_extract(x_4, x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
lean_dec(x_4);
x_13 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_2(x_14, lean_box(0), x_13);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_6);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Substring_nextn(x_12, x_9, x_10);
lean_dec(x_12);
x_14 = lean_string_utf8_extract(x_6, x_13, x_11);
lean_dec(x_11);
lean_dec(x_13);
lean_dec(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_apply_2(x_16, lean_box(0), x_15);
x_18 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithEq___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_shortOptionWithEq___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_4);
lean_inc(x_9);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_nextn(x_10, x_7, x_8);
lean_dec(x_10);
x_12 = lean_string_utf8_extract(x_4, x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
lean_dec(x_4);
x_13 = lean_string_utf8_byte_size(x_12);
x_14 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
x_15 = l_Substring_takeWhileAux(x_12, x_13, x_14, x_8);
x_16 = lean_string_utf8_extract(x_12, x_15, x_13);
lean_dec(x_13);
lean_dec(x_15);
lean_dec(x_12);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_apply_2(x_18, lean_box(0), x_17);
x_20 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_19, x_5);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithSpace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_6);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Substring_nextn(x_12, x_9, x_10);
lean_dec(x_12);
x_14 = lean_string_utf8_extract(x_6, x_13, x_11);
lean_dec(x_11);
lean_dec(x_13);
lean_dec(x_6);
x_15 = lean_string_utf8_byte_size(x_14);
x_16 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
x_17 = l_Substring_takeWhileAux(x_14, x_15, x_16, x_10);
x_18 = lean_string_utf8_extract(x_14, x_17, x_15);
lean_dec(x_15);
lean_dec(x_17);
lean_dec(x_14);
x_19 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_ctor_get(x_3, 2);
lean_inc(x_20);
lean_dec(x_3);
x_21 = lean_apply_2(x_20, lean_box(0), x_19);
x_22 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_21, x_7);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_4);
x_5 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_5, 0, x_4);
lean_closure_set(x_5, 1, x_3);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_string_utf8_byte_size(x_4);
lean_inc(x_9);
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = l_Substring_nextn(x_10, x_7, x_8);
lean_dec(x_10);
x_12 = lean_string_utf8_extract(x_4, x_11, x_9);
lean_dec(x_9);
lean_dec(x_11);
lean_dec(x_4);
x_13 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_ctor_get(x_2, 2);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_apply_2(x_14, lean_box(0), x_13);
x_16 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_15, x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOptionWithArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_6);
x_7 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_7, 0, x_6);
lean_closure_set(x_7, 1, x_5);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_string_utf8_byte_size(x_6);
lean_inc(x_11);
lean_inc(x_6);
x_12 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Substring_nextn(x_12, x_9, x_10);
lean_dec(x_12);
x_14 = lean_string_utf8_extract(x_6, x_13, x_11);
lean_dec(x_11);
lean_dec(x_13);
lean_dec(x_6);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_ctor_get(x_3, 2);
lean_inc(x_16);
lean_dec(x_3);
x_17 = lean_apply_2(x_16, lean_box(0), x_15);
x_18 = lean_apply_4(x_8, lean_box(0), lean_box(0), x_17, x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_next_fast(x_1, x_2);
x_7 = l_Lake_multiShortOption_loop___redArg(x_3, x_4, x_1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_string_utf8_at_end(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_4);
lean_inc(x_3);
x_6 = lean_alloc_closure((void*)(l_Lake_multiShortOption_loop___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_4);
lean_closure_set(x_6, 2, x_1);
lean_closure_set(x_6, 3, x_2);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_string_utf8_get_fast(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_box_uint32(x_8);
x_10 = lean_apply_1(x_2, x_9);
x_11 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_10, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_13, lean_box(0), x_14);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_multiShortOption_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption_loop___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_multiShortOption_loop___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lake_multiShortOption_loop___redArg(x_1, x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_multiShortOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = l_Lake_multiShortOption_loop___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(32u);
x_6 = l_Char_ofNat(x_5);
x_7 = lean_string_utf8_byte_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_String_posOfAux(x_4, x_6, x_7, x_8);
x_10 = l_instDecidableEqPos(x_9, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_9);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_string_utf8_next(x_4, x_9);
lean_dec(x_9);
x_14 = lean_string_utf8_extract(x_4, x_13, x_7);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_2(x_16, lean_box(0), x_15);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_17, x_11);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_apply_1(x_3, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(32u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_string_utf8_byte_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_String_posOfAux(x_6, x_8, x_9, x_10);
x_12 = l_instDecidableEqPos(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_11);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_5);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_string_utf8_next(x_6, x_11);
lean_dec(x_11);
x_16 = lean_string_utf8_extract(x_6, x_15, x_9);
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_apply_2(x_18, lean_box(0), x_17);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_19, x_13);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_apply_1(x_5, x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrSpace___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_longOptionOrSpace___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(61u);
x_6 = l_Char_ofNat(x_5);
x_7 = lean_string_utf8_byte_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_String_posOfAux(x_4, x_6, x_7, x_8);
x_10 = l_instDecidableEqPos(x_9, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_9);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_string_utf8_next(x_4, x_9);
lean_dec(x_9);
x_14 = lean_string_utf8_extract(x_4, x_13, x_7);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_2(x_16, lean_box(0), x_15);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_17, x_11);
return x_18;
}
else
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_apply_1(x_3, x_4);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOptionOrEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(61u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_string_utf8_byte_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_String_posOfAux(x_6, x_8, x_9, x_10);
x_12 = l_instDecidableEqPos(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_11);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_5);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_string_utf8_next(x_6, x_11);
lean_dec(x_11);
x_16 = lean_string_utf8_extract(x_6, x_15, x_9);
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_apply_2(x_18, lean_box(0), x_17);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_19, x_13);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_apply_1(x_5, x_6);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_string_utf8_extract(x_1, x_2, x_3);
x_9 = lean_unsigned_to_nat(32u);
x_10 = l_Char_ofNat(x_9);
x_11 = lean_string_utf8_byte_size(x_8);
lean_inc(x_2);
x_12 = l_String_posOfAux(x_8, x_10, x_11, x_2);
x_13 = l_instDecidableEqPos(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_12);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_4);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_string_utf8_next(x_8, x_12);
lean_dec(x_12);
x_17 = lean_string_utf8_extract(x_8, x_16, x_11);
lean_dec(x_11);
lean_dec(x_16);
lean_dec(x_8);
x_18 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_ctor_get(x_6, 2);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_apply_2(x_19, lean_box(0), x_18);
x_21 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_20, x_14);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_22 = lean_apply_1(x_4, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_unsigned_to_nat(61u);
x_6 = l_Char_ofNat(x_5);
x_7 = lean_string_utf8_byte_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = l_String_posOfAux(x_4, x_6, x_7, x_8);
x_10 = l_instDecidableEqPos(x_9, x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_9);
lean_inc(x_4);
x_11 = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_11, 0, x_4);
lean_closure_set(x_11, 1, x_8);
lean_closure_set(x_11, 2, x_9);
lean_closure_set(x_11, 3, x_3);
lean_closure_set(x_11, 4, x_1);
lean_closure_set(x_11, 5, x_2);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_string_utf8_next(x_4, x_9);
lean_dec(x_9);
x_14 = lean_string_utf8_extract(x_4, x_13, x_7);
lean_dec(x_7);
lean_dec(x_13);
lean_dec(x_4);
x_15 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_apply_2(x_16, lean_box(0), x_15);
x_18 = lean_apply_4(x_12, lean_box(0), lean_box(0), x_17, x_11);
return x_18;
}
else
{
lean_object* x_19; uint32_t x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_9);
x_19 = lean_unsigned_to_nat(32u);
x_20 = l_Char_ofNat(x_19);
x_21 = l_String_posOfAux(x_4, x_20, x_7, x_8);
x_22 = l_instDecidableEqPos(x_21, x_7);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_inc(x_21);
lean_inc(x_4);
x_23 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_23, 0, x_4);
lean_closure_set(x_23, 1, x_8);
lean_closure_set(x_23, 2, x_21);
lean_closure_set(x_23, 3, x_3);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_string_utf8_next(x_4, x_21);
lean_dec(x_21);
x_26 = lean_string_utf8_extract(x_4, x_25, x_7);
lean_dec(x_7);
lean_dec(x_25);
lean_dec(x_4);
x_27 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_ctor_get(x_2, 2);
lean_inc(x_28);
lean_dec(x_2);
x_29 = lean_apply_2(x_28, lean_box(0), x_27);
x_30 = lean_apply_4(x_24, lean_box(0), lean_box(0), x_29, x_23);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_21);
lean_dec(x_7);
lean_dec(x_2);
lean_dec(x_1);
x_31 = lean_apply_1(x_3, x_4);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_unsigned_to_nat(61u);
x_8 = l_Char_ofNat(x_7);
x_9 = lean_string_utf8_byte_size(x_6);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_String_posOfAux(x_6, x_8, x_9, x_10);
x_12 = l_instDecidableEqPos(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lake_longOption___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_10);
lean_closure_set(x_13, 2, x_11);
lean_closure_set(x_13, 3, x_5);
lean_closure_set(x_13, 4, x_2);
lean_closure_set(x_13, 5, x_3);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_string_utf8_next(x_6, x_11);
lean_dec(x_11);
x_16 = lean_string_utf8_extract(x_6, x_15, x_9);
lean_dec(x_9);
lean_dec(x_15);
lean_dec(x_6);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_ctor_get(x_3, 2);
lean_inc(x_18);
lean_dec(x_3);
x_19 = lean_apply_2(x_18, lean_box(0), x_17);
x_20 = lean_apply_4(x_14, lean_box(0), lean_box(0), x_19, x_13);
return x_20;
}
else
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; uint8_t x_24; 
lean_dec(x_11);
x_21 = lean_unsigned_to_nat(32u);
x_22 = l_Char_ofNat(x_21);
x_23 = l_String_posOfAux(x_6, x_22, x_9, x_10);
x_24 = l_instDecidableEqPos(x_23, x_9);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_inc(x_23);
lean_inc(x_6);
x_25 = lean_alloc_closure((void*)(l_Lake_longOptionOrSpace___redArg___lam__0___boxed), 5, 4);
lean_closure_set(x_25, 0, x_6);
lean_closure_set(x_25, 1, x_10);
lean_closure_set(x_25, 2, x_23);
lean_closure_set(x_25, 3, x_5);
x_26 = lean_ctor_get(x_2, 1);
lean_inc(x_26);
lean_dec(x_2);
x_27 = lean_string_utf8_next(x_6, x_23);
lean_dec(x_23);
x_28 = lean_string_utf8_extract(x_6, x_27, x_9);
lean_dec(x_9);
lean_dec(x_27);
lean_dec(x_6);
x_29 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_29, 0, x_28);
x_30 = lean_ctor_get(x_3, 2);
lean_inc(x_30);
lean_dec(x_3);
x_31 = lean_apply_2(x_30, lean_box(0), x_29);
x_32 = lean_apply_4(x_26, lean_box(0), lean_box(0), x_31, x_25);
return x_32;
}
else
{
lean_object* x_33; 
lean_dec(x_23);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_apply_1(x_5, x_6);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_longOption___redArg___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_longOption___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_longOption___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_string_utf8_get(x_1, x_4);
x_6 = lean_box_uint32(x_5);
x_7 = lean_apply_1(x_2, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_string_length(x_5);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_dec_eq(x_6, x_7);
lean_dec(x_6);
if (x_8 == 0)
{
uint32_t x_9; lean_object* x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_string_utf8_get(x_5, x_7);
x_10 = lean_unsigned_to_nat(61u);
x_11 = l_Char_ofNat(x_10);
x_12 = l_instDecidableEqChar(x_9, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint32_t x_14; uint8_t x_15; 
x_13 = lean_unsigned_to_nat(32u);
x_14 = l_Char_ofNat(x_13);
x_15 = l_instDecidableEqChar(x_9, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_16 = lean_apply_1(x_4, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_4);
lean_inc(x_5);
x_17 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_17, 0, x_5);
lean_closure_set(x_17, 1, x_3);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_string_utf8_byte_size(x_5);
lean_inc(x_20);
lean_inc(x_5);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_19);
lean_ctor_set(x_21, 2, x_20);
x_22 = l_Substring_nextn(x_21, x_7, x_19);
lean_dec(x_21);
x_23 = lean_string_utf8_extract(x_5, x_22, x_20);
lean_dec(x_20);
lean_dec(x_22);
lean_dec(x_5);
x_24 = lean_string_utf8_byte_size(x_23);
x_25 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
x_26 = l_Substring_takeWhileAux(x_23, x_24, x_25, x_19);
x_27 = lean_string_utf8_extract(x_23, x_26, x_24);
lean_dec(x_24);
lean_dec(x_26);
lean_dec(x_23);
x_28 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_ctor_get(x_2, 2);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_apply_2(x_29, lean_box(0), x_28);
x_31 = lean_apply_4(x_18, lean_box(0), lean_box(0), x_30, x_17);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_4);
lean_inc(x_5);
x_32 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_32, 0, x_5);
lean_closure_set(x_32, 1, x_3);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_string_utf8_byte_size(x_5);
lean_inc(x_36);
lean_inc(x_5);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_36);
x_38 = l_Substring_nextn(x_37, x_34, x_35);
lean_dec(x_37);
x_39 = lean_string_utf8_extract(x_5, x_38, x_36);
lean_dec(x_36);
lean_dec(x_38);
lean_dec(x_5);
x_40 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_ctor_get(x_2, 2);
lean_inc(x_41);
lean_dec(x_2);
x_42 = lean_apply_2(x_41, lean_box(0), x_40);
x_43 = lean_apply_4(x_33, lean_box(0), lean_box(0), x_42, x_32);
return x_43;
}
}
else
{
lean_object* x_44; uint32_t x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_string_utf8_get(x_5, x_44);
lean_dec(x_5);
x_46 = lean_box_uint32(x_45);
x_47 = lean_apply_1(x_3, x_46);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_string_length(x_7);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
uint32_t x_11; lean_object* x_12; uint32_t x_13; uint8_t x_14; 
x_11 = lean_string_utf8_get(x_7, x_9);
x_12 = lean_unsigned_to_nat(61u);
x_13 = l_Char_ofNat(x_12);
x_14 = l_instDecidableEqChar(x_11, x_13);
if (x_14 == 0)
{
lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_15 = lean_unsigned_to_nat(32u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_11, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_apply_1(x_6, x_7);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
lean_dec(x_6);
lean_inc(x_7);
x_19 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_19, 0, x_7);
lean_closure_set(x_19, 1, x_5);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_string_utf8_byte_size(x_7);
lean_inc(x_22);
lean_inc(x_7);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_7);
lean_ctor_set(x_23, 1, x_21);
lean_ctor_set(x_23, 2, x_22);
x_24 = l_Substring_nextn(x_23, x_9, x_21);
lean_dec(x_23);
x_25 = lean_string_utf8_extract(x_7, x_24, x_22);
lean_dec(x_22);
lean_dec(x_24);
lean_dec(x_7);
x_26 = lean_string_utf8_byte_size(x_25);
x_27 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
x_28 = l_Substring_takeWhileAux(x_25, x_26, x_27, x_21);
x_29 = lean_string_utf8_extract(x_25, x_28, x_26);
lean_dec(x_26);
lean_dec(x_28);
lean_dec(x_25);
x_30 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
lean_dec(x_3);
x_32 = lean_apply_2(x_31, lean_box(0), x_30);
x_33 = lean_apply_4(x_20, lean_box(0), lean_box(0), x_32, x_19);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_6);
lean_inc(x_7);
x_34 = lean_alloc_closure((void*)(l_Lake_shortOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_34, 0, x_7);
lean_closure_set(x_34, 1, x_5);
x_35 = lean_ctor_get(x_2, 1);
lean_inc(x_35);
lean_dec(x_2);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_string_utf8_byte_size(x_7);
lean_inc(x_38);
lean_inc(x_7);
x_39 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_39, 0, x_7);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = l_Substring_nextn(x_39, x_36, x_37);
lean_dec(x_39);
x_41 = lean_string_utf8_extract(x_7, x_40, x_38);
lean_dec(x_38);
lean_dec(x_40);
lean_dec(x_7);
x_42 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_ctor_get(x_3, 2);
lean_inc(x_43);
lean_dec(x_3);
x_44 = lean_apply_2(x_43, lean_box(0), x_42);
x_45 = lean_apply_4(x_35, lean_box(0), lean_box(0), x_44, x_34);
return x_45;
}
}
else
{
lean_object* x_46; uint32_t x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_46 = lean_unsigned_to_nat(1u);
x_47 = lean_string_utf8_get(x_7, x_46);
lean_dec(x_7);
x_48 = lean_box_uint32(x_47);
x_49 = lean_apply_1(x_5, x_48);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lake_shortOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_shortOption___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0(lean_object* x_1, uint32_t x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box_uint32(x_2);
x_5 = lean_apply_1(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint32_t x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_string_utf8_extract(x_1, x_2, x_3);
x_9 = lean_unsigned_to_nat(32u);
x_10 = l_Char_ofNat(x_9);
x_11 = lean_string_utf8_byte_size(x_8);
lean_inc(x_2);
x_12 = l_String_posOfAux(x_8, x_10, x_11, x_2);
x_13 = l_instDecidableEqPos(x_12, x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_12);
lean_inc(x_8);
x_14 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__4___boxed), 5, 4);
lean_closure_set(x_14, 0, x_8);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_12);
lean_closure_set(x_14, 3, x_4);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_dec(x_5);
x_16 = lean_string_utf8_next(x_8, x_12);
lean_dec(x_12);
x_17 = lean_string_utf8_extract(x_8, x_16, x_11);
lean_dec(x_11);
lean_dec(x_16);
lean_dec(x_8);
x_18 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_ctor_get(x_6, 2);
lean_inc(x_19);
lean_dec(x_6);
x_20 = lean_apply_2(x_19, lean_box(0), x_18);
x_21 = lean_apply_4(x_15, lean_box(0), lean_box(0), x_20, x_14);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_22 = lean_apply_1(x_4, x_8);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_string_utf8_extract(x_1, x_2, x_3);
x_7 = lean_apply_1(x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint32_t x_6; lean_object* x_7; uint32_t x_8; uint8_t x_9; 
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_string_utf8_get(x_4, x_5);
x_7 = lean_unsigned_to_nat(45u);
x_8 = l_Char_ofNat(x_7);
x_9 = l_instDecidableEqChar(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
x_11 = lean_string_length(x_4);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_dec_eq(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
uint32_t x_14; lean_object* x_15; uint32_t x_16; uint8_t x_17; 
x_14 = lean_string_utf8_get(x_4, x_12);
x_15 = lean_unsigned_to_nat(61u);
x_16 = l_Char_ofNat(x_15);
x_17 = l_instDecidableEqChar(x_14, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint32_t x_19; uint8_t x_20; 
x_18 = lean_unsigned_to_nat(32u);
x_19 = l_Char_ofNat(x_18);
x_20 = l_instDecidableEqChar(x_14, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_ctor_get(x_3, 2);
lean_inc(x_21);
lean_dec(x_3);
x_22 = lean_apply_1(x_21, x_4);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_3);
x_23 = lean_box_uint32(x_6);
x_24 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_24, 0, x_10);
lean_closure_set(x_24, 1, x_23);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_string_utf8_byte_size(x_4);
lean_inc(x_27);
lean_inc(x_4);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Substring_nextn(x_28, x_12, x_26);
lean_dec(x_28);
x_30 = lean_string_utf8_extract(x_4, x_29, x_27);
lean_dec(x_27);
lean_dec(x_29);
lean_dec(x_4);
x_31 = lean_string_utf8_byte_size(x_30);
x_32 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
x_33 = l_Substring_takeWhileAux(x_30, x_31, x_32, x_26);
x_34 = lean_string_utf8_extract(x_30, x_33, x_31);
lean_dec(x_31);
lean_dec(x_33);
lean_dec(x_30);
x_35 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_ctor_get(x_2, 2);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_apply_2(x_36, lean_box(0), x_35);
x_38 = lean_apply_4(x_25, lean_box(0), lean_box(0), x_37, x_24);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_3);
x_39 = lean_box_uint32(x_6);
x_40 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_40, 0, x_10);
lean_closure_set(x_40, 1, x_39);
x_41 = lean_ctor_get(x_1, 1);
lean_inc(x_41);
lean_dec(x_1);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_string_utf8_byte_size(x_4);
lean_inc(x_44);
lean_inc(x_4);
x_45 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_45, 0, x_4);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_44);
x_46 = l_Substring_nextn(x_45, x_42, x_43);
lean_dec(x_45);
x_47 = lean_string_utf8_extract(x_4, x_46, x_44);
lean_dec(x_44);
lean_dec(x_46);
lean_dec(x_4);
x_48 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
lean_dec(x_2);
x_50 = lean_apply_2(x_49, lean_box(0), x_48);
x_51 = lean_apply_4(x_41, lean_box(0), lean_box(0), x_50, x_40);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box_uint32(x_6);
x_53 = lean_apply_1(x_10, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; uint32_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_3, 0);
lean_inc(x_54);
lean_dec(x_3);
x_55 = lean_unsigned_to_nat(61u);
x_56 = l_Char_ofNat(x_55);
x_57 = lean_string_utf8_byte_size(x_4);
x_58 = lean_unsigned_to_nat(0u);
x_59 = l_String_posOfAux(x_4, x_56, x_57, x_58);
x_60 = l_instDecidableEqPos(x_59, x_57);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_59);
lean_inc(x_4);
x_61 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_61, 0, x_4);
lean_closure_set(x_61, 1, x_58);
lean_closure_set(x_61, 2, x_59);
lean_closure_set(x_61, 3, x_54);
lean_closure_set(x_61, 4, x_1);
lean_closure_set(x_61, 5, x_2);
x_62 = lean_ctor_get(x_1, 1);
lean_inc(x_62);
lean_dec(x_1);
x_63 = lean_string_utf8_next(x_4, x_59);
lean_dec(x_59);
x_64 = lean_string_utf8_extract(x_4, x_63, x_57);
lean_dec(x_57);
lean_dec(x_63);
lean_dec(x_4);
x_65 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_65, 0, x_64);
x_66 = lean_ctor_get(x_2, 2);
lean_inc(x_66);
lean_dec(x_2);
x_67 = lean_apply_2(x_66, lean_box(0), x_65);
x_68 = lean_apply_4(x_62, lean_box(0), lean_box(0), x_67, x_61);
return x_68;
}
else
{
lean_object* x_69; uint32_t x_70; lean_object* x_71; uint8_t x_72; 
lean_dec(x_59);
x_69 = lean_unsigned_to_nat(32u);
x_70 = l_Char_ofNat(x_69);
x_71 = l_String_posOfAux(x_4, x_70, x_57, x_58);
x_72 = l_instDecidableEqPos(x_71, x_57);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_inc(x_71);
lean_inc(x_4);
x_73 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_73, 0, x_4);
lean_closure_set(x_73, 1, x_58);
lean_closure_set(x_73, 2, x_71);
lean_closure_set(x_73, 3, x_54);
x_74 = lean_ctor_get(x_1, 1);
lean_inc(x_74);
lean_dec(x_1);
x_75 = lean_string_utf8_next(x_4, x_71);
lean_dec(x_71);
x_76 = lean_string_utf8_extract(x_4, x_75, x_57);
lean_dec(x_57);
lean_dec(x_75);
lean_dec(x_4);
x_77 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_77, 0, x_76);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
lean_dec(x_2);
x_79 = lean_apply_2(x_78, lean_box(0), x_77);
x_80 = lean_apply_4(x_74, lean_box(0), lean_box(0), x_79, x_73);
return x_80;
}
else
{
lean_object* x_81; 
lean_dec(x_71);
lean_dec(x_57);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_apply_1(x_54, x_4);
return x_81;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_string_utf8_get(x_6, x_7);
x_9 = lean_unsigned_to_nat(45u);
x_10 = l_Char_ofNat(x_9);
x_11 = l_instDecidableEqChar(x_8, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
x_13 = lean_string_length(x_6);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_dec_eq(x_13, x_14);
lean_dec(x_13);
if (x_15 == 0)
{
uint32_t x_16; lean_object* x_17; uint32_t x_18; uint8_t x_19; 
x_16 = lean_string_utf8_get(x_6, x_14);
x_17 = lean_unsigned_to_nat(61u);
x_18 = l_Char_ofNat(x_17);
x_19 = l_instDecidableEqChar(x_16, x_18);
if (x_19 == 0)
{
lean_object* x_20; uint32_t x_21; uint8_t x_22; 
x_20 = lean_unsigned_to_nat(32u);
x_21 = l_Char_ofNat(x_20);
x_22 = l_instDecidableEqChar(x_16, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_5, 2);
lean_inc(x_23);
lean_dec(x_5);
x_24 = lean_apply_1(x_23, x_6);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_5);
x_25 = lean_box_uint32(x_8);
x_26 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_26, 0, x_12);
lean_closure_set(x_26, 1, x_25);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_dec(x_2);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_string_utf8_byte_size(x_6);
lean_inc(x_29);
lean_inc(x_6);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_6);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Substring_nextn(x_30, x_14, x_28);
lean_dec(x_30);
x_32 = lean_string_utf8_extract(x_6, x_31, x_29);
lean_dec(x_29);
lean_dec(x_31);
lean_dec(x_6);
x_33 = lean_string_utf8_byte_size(x_32);
x_34 = lean_alloc_closure((void*)(l_Char_isWhitespace___boxed), 1, 0);
x_35 = l_Substring_takeWhileAux(x_32, x_33, x_34, x_28);
x_36 = lean_string_utf8_extract(x_32, x_35, x_33);
lean_dec(x_33);
lean_dec(x_35);
lean_dec(x_32);
x_37 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_ctor_get(x_3, 2);
lean_inc(x_38);
lean_dec(x_3);
x_39 = lean_apply_2(x_38, lean_box(0), x_37);
x_40 = lean_apply_4(x_27, lean_box(0), lean_box(0), x_39, x_26);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_5);
x_41 = lean_box_uint32(x_8);
x_42 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_42, 0, x_12);
lean_closure_set(x_42, 1, x_41);
x_43 = lean_ctor_get(x_2, 1);
lean_inc(x_43);
lean_dec(x_2);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_string_utf8_byte_size(x_6);
lean_inc(x_46);
lean_inc(x_6);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_6);
lean_ctor_set(x_47, 1, x_45);
lean_ctor_set(x_47, 2, x_46);
x_48 = l_Substring_nextn(x_47, x_44, x_45);
lean_dec(x_47);
x_49 = lean_string_utf8_extract(x_6, x_48, x_46);
lean_dec(x_46);
lean_dec(x_48);
lean_dec(x_6);
x_50 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_ctor_get(x_3, 2);
lean_inc(x_51);
lean_dec(x_3);
x_52 = lean_apply_2(x_51, lean_box(0), x_50);
x_53 = lean_apply_4(x_43, lean_box(0), lean_box(0), x_52, x_42);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_54 = lean_box_uint32(x_8);
x_55 = lean_apply_1(x_12, x_54);
return x_55;
}
}
else
{
lean_object* x_56; lean_object* x_57; uint32_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_56 = lean_ctor_get(x_5, 0);
lean_inc(x_56);
lean_dec(x_5);
x_57 = lean_unsigned_to_nat(61u);
x_58 = l_Char_ofNat(x_57);
x_59 = lean_string_utf8_byte_size(x_6);
x_60 = lean_unsigned_to_nat(0u);
x_61 = l_String_posOfAux(x_6, x_58, x_59, x_60);
x_62 = l_instDecidableEqPos(x_61, x_59);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_61);
lean_inc(x_6);
x_63 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__2___boxed), 7, 6);
lean_closure_set(x_63, 0, x_6);
lean_closure_set(x_63, 1, x_60);
lean_closure_set(x_63, 2, x_61);
lean_closure_set(x_63, 3, x_56);
lean_closure_set(x_63, 4, x_2);
lean_closure_set(x_63, 5, x_3);
x_64 = lean_ctor_get(x_2, 1);
lean_inc(x_64);
lean_dec(x_2);
x_65 = lean_string_utf8_next(x_6, x_61);
lean_dec(x_61);
x_66 = lean_string_utf8_extract(x_6, x_65, x_59);
lean_dec(x_59);
lean_dec(x_65);
lean_dec(x_6);
x_67 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_67, 0, x_66);
x_68 = lean_ctor_get(x_3, 2);
lean_inc(x_68);
lean_dec(x_3);
x_69 = lean_apply_2(x_68, lean_box(0), x_67);
x_70 = lean_apply_4(x_64, lean_box(0), lean_box(0), x_69, x_63);
return x_70;
}
else
{
lean_object* x_71; uint32_t x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_61);
x_71 = lean_unsigned_to_nat(32u);
x_72 = l_Char_ofNat(x_71);
x_73 = l_String_posOfAux(x_6, x_72, x_59, x_60);
x_74 = l_instDecidableEqPos(x_73, x_59);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_inc(x_73);
lean_inc(x_6);
x_75 = lean_alloc_closure((void*)(l_Lake_option___redArg___lam__3___boxed), 5, 4);
lean_closure_set(x_75, 0, x_6);
lean_closure_set(x_75, 1, x_60);
lean_closure_set(x_75, 2, x_73);
lean_closure_set(x_75, 3, x_56);
x_76 = lean_ctor_get(x_2, 1);
lean_inc(x_76);
lean_dec(x_2);
x_77 = lean_string_utf8_next(x_6, x_73);
lean_dec(x_73);
x_78 = lean_string_utf8_extract(x_6, x_77, x_59);
lean_dec(x_59);
lean_dec(x_77);
lean_dec(x_6);
x_79 = lean_alloc_closure((void*)(l_Lake_shortOptionWithEq___redArg___lam__1), 2, 1);
lean_closure_set(x_79, 0, x_78);
x_80 = lean_ctor_get(x_3, 2);
lean_inc(x_80);
lean_dec(x_3);
x_81 = lean_apply_2(x_80, lean_box(0), x_79);
x_82 = lean_apply_4(x_76, lean_box(0), lean_box(0), x_81, x_75);
return x_82;
}
else
{
lean_object* x_83; 
lean_dec(x_73);
lean_dec(x_59);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_apply_1(x_56, x_6);
return x_83;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint32_t x_4; lean_object* x_5; 
x_4 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_5 = l_Lake_option___redArg___lam__0(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_option___redArg___lam__4(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lake_option___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lake_option___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_option___redArg___lam__3(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_1(x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, lean_box(0), x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_5, 1);
lean_inc(x_9);
lean_dec(x_5);
lean_inc(x_8);
x_10 = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_8);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_string_length(x_8);
x_20 = lean_nat_dec_lt(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_dec(x_8);
x_11 = x_20;
goto block_17;
}
else
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; uint32_t x_24; uint8_t x_25; 
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_string_utf8_get(x_8, x_21);
lean_dec(x_8);
x_23 = lean_unsigned_to_nat(45u);
x_24 = l_Char_ofNat(x_23);
x_25 = l_instDecidableEqChar(x_22, x_24);
x_11 = x_25;
goto block_17;
}
block_17:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_apply_2(x_1, lean_box(0), x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = lean_apply_1(x_14, x_9);
x_16 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_15, x_10);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
lean_inc(x_4);
x_8 = lean_alloc_closure((void*)(l_Lake_processLeadingOption___redArg___lam__1), 5, 4);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_3);
lean_closure_set(x_8, 2, x_2);
lean_closure_set(x_8, 3, x_4);
x_9 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_processLeadingOption___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOption___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_processLeadingOption___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_processLeadingOptions___redArg(x_1, x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_apply_1(x_1, x_2);
x_7 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_apply_2(x_1, lean_box(0), x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_26; uint8_t x_27; 
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
lean_inc(x_3);
lean_inc(x_10);
x_12 = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__2___boxed), 5, 4);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_10);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_4);
x_13 = lean_string_length(x_10);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_dec_lt(x_26, x_13);
if (x_27 == 0)
{
lean_dec(x_10);
x_14 = x_27;
goto block_25;
}
else
{
lean_object* x_28; uint32_t x_29; lean_object* x_30; uint32_t x_31; uint8_t x_32; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_string_utf8_get(x_10, x_28);
lean_dec(x_10);
x_30 = lean_unsigned_to_nat(45u);
x_31 = l_Char_ofNat(x_30);
x_32 = l_instDecidableEqChar(x_29, x_31);
x_14 = x_32;
goto block_25;
}
block_25:
{
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_nat_dec_eq(x_13, x_15);
lean_dec(x_13);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_17 = lean_box(0);
x_18 = lean_apply_2(x_1, lean_box(0), x_17);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_apply_1(x_19, x_11);
x_21 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_20, x_6);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec(x_5);
x_23 = lean_apply_1(x_22, x_11);
x_24 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_23, x_12);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_4 = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__0___boxed), 4, 3);
lean_closure_set(x_4, 0, x_1);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_3);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
lean_inc(x_4);
lean_inc(x_5);
x_9 = lean_alloc_closure((void*)(l_Lake_processLeadingOptions___redArg___lam__1), 7, 6);
lean_closure_set(x_9, 0, x_8);
lean_closure_set(x_9, 1, x_3);
lean_closure_set(x_9, 2, x_5);
lean_closure_set(x_9, 3, x_4);
lean_closure_set(x_9, 4, x_2);
lean_closure_set(x_9, 5, x_4);
x_10 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_processLeadingOptions___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lake_processLeadingOptions___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_processLeadingOptions___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_processLeadingOptions___redArg___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 0, x_6);
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
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_collectArgs___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = lean_apply_2(x_1, lean_box(0), x_2);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_string_length(x_10);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_lt(x_21, x_11);
if (x_22 == 0)
{
x_12 = x_22;
goto block_20;
}
else
{
lean_object* x_23; uint32_t x_24; lean_object* x_25; uint32_t x_26; uint8_t x_27; 
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_string_utf8_get(x_10, x_23);
x_25 = lean_unsigned_to_nat(45u);
x_26 = l_Char_ofNat(x_25);
x_27 = l_instDecidableEqChar(x_24, x_26);
x_12 = x_27;
goto block_20;
}
block_20:
{
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_nat_dec_eq(x_11, x_13);
lean_dec(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_push(x_2, x_10);
x_16 = l_Lake_collectArgs___redArg(x_3, x_4, x_5, x_15);
return x_16;
}
else
{
lean_object* x_17; 
lean_dec(x_10);
x_17 = l_Lake_collectArgs___redArg(x_3, x_4, x_5, x_2);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_apply_1(x_5, x_10);
x_19 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_18, x_7);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_5 = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__0), 1, 0);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__1___boxed), 5, 4);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_3);
lean_closure_set(x_6, 3, x_4);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_apply_2(x_8, lean_box(0), x_5);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
lean_inc(x_7);
x_12 = lean_alloc_closure((void*)(l_Lake_collectArgs___redArg___lam__2), 8, 7);
lean_closure_set(x_12, 0, x_11);
lean_closure_set(x_12, 1, x_4);
lean_closure_set(x_12, 2, x_1);
lean_closure_set(x_12, 3, x_2);
lean_closure_set(x_12, 4, x_3);
lean_closure_set(x_12, 5, x_7);
lean_closure_set(x_12, 6, x_6);
x_13 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_collectArgs___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_collectArgs___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_collectArgs___redArg___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_array_to_list(x_2);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_apply_1(x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
x_4 = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(x_4, 0, x_2);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = l_Lake_collectArgs___redArg(x_1, x_2, x_3, x_7);
x_9 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_8, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_processOptions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_5 = lean_alloc_closure((void*)(l_Lake_processOptions___redArg___lam__0), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = l_Lake_collectArgs___redArg(x_2, x_3, x_4, x_8);
x_10 = lean_apply_4(x_6, lean_box(0), lean_box(0), x_9, x_5);
return x_10;
}
}
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Cli(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Array_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
