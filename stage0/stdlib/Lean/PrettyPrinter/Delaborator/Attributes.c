// Lean compiler output
// Module: Lean.PrettyPrinter.Delaborator.Attributes
// Imports: Lean.Attributes
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
LEAN_EXPORT lean_object* l_Lean_ppUsingAnonymousConstructorAttr;
LEAN_EXPORT uint8_t l_Lean_hasPPNoDotAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_TagAttribute_hasTag(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasPPUsingAnonymousConstructorAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTagAttribute(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasPPNoDotAttribute___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_hasPPUsingAnonymousConstructorAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ppNoDotAttr;
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_30_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4____boxed), 4, 0);
x_3 = lean_mk_string_unchecked("pp_using_anonymous_constructor", 30, 30);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("mark structure to be pretty printed using `⟨a,b,c⟩` notation", 64, 60);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("ppUsingAnonymousConstructorAttr", 31, 31);
x_8 = l_Lean_Name_mkStr2(x_6, x_7);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_registerTagAttribute(x_4, x_5, x_2, x_8, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_initFn___lam__0____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_30_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_2 = lean_alloc_closure((void*)(l_Lean_initFn___lam__0____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4____boxed), 4, 0);
x_3 = lean_mk_string_unchecked("pp_nodot", 8, 8);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("mark declaration to never be pretty printed using field notation", 64, 64);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("ppNoDotAttr", 11, 11);
x_8 = l_Lean_Name_mkStr2(x_6, x_7);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_registerTagAttribute(x_4, x_5, x_2, x_8, x_10, x_1);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_hasPPUsingAnonymousConstructorAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_ppUsingAnonymousConstructorAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_hasPPUsingAnonymousConstructorAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_hasPPUsingAnonymousConstructorAttribute(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_hasPPNoDotAttribute(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_ppNoDotAttr;
x_4 = l_Lean_TagAttribute_hasTag(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_hasPPNoDotAttribute___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_hasPPNoDotAttribute(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_Attributes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_PrettyPrinter_Delaborator_Attributes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_4_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppUsingAnonymousConstructorAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppUsingAnonymousConstructorAttr);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_PrettyPrinter_Delaborator_Attributes___hyg_30_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_ppNoDotAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_ppNoDotAttr);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
