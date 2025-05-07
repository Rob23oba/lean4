// Lean compiler output
// Module: Init.Data.Option.BasicAux
// Imports: Init.Data.Option.Basic Init.Util
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
lean_object* l_panic___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___redArg(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_get_x21___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_4 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_5 = lean_unsigned_to_nat(21u);
x_6 = lean_unsigned_to_nat(14u);
x_7 = lean_mk_string_unchecked("value is none", 13, 13);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___redArg(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; 
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Option_get_x21(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Init.Data.Option.BasicAux", 25, 25);
x_5 = lean_mk_string_unchecked("Option.get!", 11, 11);
x_6 = lean_unsigned_to_nat(21u);
x_7 = lean_unsigned_to_nat(14u);
x_8 = lean_mk_string_unchecked("value is none", 13, 13);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___redArg(x_2, x_9);
return x_10;
}
else
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_3, 0);
lean_inc(x_11);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Option_get_x21___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Option_get_x21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Option_get_x21(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
lean_object* initialize_Init_Data_Option_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Option_BasicAux(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Option_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
