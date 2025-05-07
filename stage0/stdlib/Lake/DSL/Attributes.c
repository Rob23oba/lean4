// Lean compiler output
// Module: Lake.DSL.Attributes
// Imports: Lake.DSL.AttributesCore
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
LEAN_EXPORT lean_object* l_Lake_initFn___lam__0____x40_Lake_DSL_Attributes___hyg_4_(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lake_testDriverAttr;
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_initFn____x40_Lake_DSL_Attributes___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initFn___lam__1____x40_Lake_DSL_Attributes___hyg_4_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_DSL_Attributes___hyg_4_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_initFn___lam__0____x40_Lake_DSL_Attributes___hyg_4____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_initFn____x40_Lake_DSL_Attributes___hyg_4__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_initFn____x40_Lake_DSL_Attributes___hyg_4__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_box(1);
x_7 = lean_box(0);
x_8 = lean_unbox(x_6);
x_9 = lean_unbox(x_7);
x_10 = l_Lean_logAt___at___Lean_log___at___Lean_logError___at___Lean_Core_wrapAsyncAsSnapshot_spec__25_spec__25_spec__25(x_1, x_2, x_8, x_9, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn___lam__0____x40_Lake_DSL_Attributes___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("@[test_runner] has been deprecated, use @[test_driver] instead", 62, 62);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofFormat(x_9);
lean_inc(x_5);
x_11 = l_Lean_logWarningAt___at___Lake_initFn____x40_Lake_DSL_Attributes___hyg_4__spec__0(x_3, x_10, x_5, x_6, x_7);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(x_4);
x_15 = lean_apply_6(x_13, x_2, x_3, x_14, x_5, x_6, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn___lam__1____x40_Lake_DSL_Attributes___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_apply_4(x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn____x40_Lake_DSL_Attributes___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_2 = lean_box(0);
x_3 = lean_mk_string_unchecked("Lake", 4, 4);
lean_inc(x_3);
x_4 = l_Lean_Name_str___override(x_2, x_3);
x_5 = lean_mk_string_unchecked("initFn", 6, 6);
x_6 = l_Lean_Name_str___override(x_4, x_5);
x_7 = lean_mk_string_unchecked("_@", 2, 2);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = l_Lean_Name_str___override(x_8, x_3);
x_10 = lean_mk_string_unchecked("DSL", 3, 3);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("Attributes", 10, 10);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_hyg", 4, 4);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = lean_unsigned_to_nat(4u);
x_17 = l_Lean_Name_num___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("test_runner", 11, 11);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lake_testDriverAttr;
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_inc(x_21);
x_22 = lean_alloc_closure((void*)(l_Lake_initFn___lam__0____x40_Lake_DSL_Attributes___hyg_4____boxed), 7, 1);
lean_closure_set(x_22, 0, x_21);
lean_inc(x_21);
x_23 = lean_alloc_closure((void*)(l_Lake_initFn___lam__1____x40_Lake_DSL_Attributes___hyg_4_), 5, 1);
lean_closure_set(x_23, 0, x_21);
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_ctor_get(x_24, 2);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_24, sizeof(void*)*3);
lean_dec(x_24);
x_27 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_19);
lean_ctor_set(x_27, 2, x_25);
lean_ctor_set_uint8(x_27, sizeof(void*)*3, x_26);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_22);
lean_ctor_set(x_28, 2, x_23);
x_29 = l_Lean_registerBuiltinAttribute(x_28, x_1);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarningAt___at___Lake_initFn____x40_Lake_DSL_Attributes___hyg_4__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_logWarningAt___at___Lake_initFn____x40_Lake_DSL_Attributes___hyg_4__spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_initFn___lam__0____x40_Lake_DSL_Attributes___hyg_4____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lake_initFn___lam__0____x40_Lake_DSL_Attributes___hyg_4_(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Lake_DSL_AttributesCore(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Attributes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_AttributesCore(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lake_initFn____x40_Lake_DSL_Attributes___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
