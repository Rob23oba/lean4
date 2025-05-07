// Lean compiler output
// Module: Init.Grind.CommRing.Int
// Imports: Init.Grind.CommRing.Basic Init.Data.Int.Lemmas
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
lean_object* l_Int_add___boxed(lean_object*, lean_object*);
lean_object* l_Int_sub___boxed(lean_object*, lean_object*);
lean_object* l_instNatCastInt___lam__0(lean_object*);
extern lean_object* l_Int_instNegInt;
extern lean_object* l_Int_instMul;
lean_object* l_instHAdd___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_instOfNat(lean_object*);
extern lean_object* l_instIntCastInt;
lean_object* l_instPowNat___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_instCommRingInt;
lean_object* l_Int_pow___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Grind_instCommRingInt() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_alloc_closure((void*)(l_Int_add___boxed), 2, 0);
x_2 = l_Int_instMul;
x_3 = l_Int_instNegInt;
x_4 = lean_alloc_closure((void*)(l_Int_sub___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Int_pow___boxed), 2, 0);
x_6 = l_instPowNat___redArg(x_5);
x_7 = lean_alloc_closure((void*)(l_instHAdd___redArg___lam__0), 3, 1);
lean_closure_set(x_7, 0, x_6);
x_8 = lean_alloc_closure((void*)(l_instNatCastInt___lam__0), 1, 0);
x_9 = l_instIntCastInt;
x_10 = lean_alloc_closure((void*)(l_instOfNat), 1, 0);
x_11 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_2);
lean_ctor_set(x_11, 2, x_3);
lean_ctor_set(x_11, 3, x_4);
lean_ctor_set(x_11, 4, x_7);
lean_ctor_set(x_11, 5, x_10);
lean_ctor_set(x_11, 6, x_8);
lean_ctor_set(x_11, 7, x_9);
return x_11;
}
}
lean_object* initialize_Init_Grind_CommRing_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_CommRing_Int(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_CommRing_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_instCommRingInt = _init_l_Lean_Grind_instCommRingInt();
lean_mark_persistent(l_Lean_Grind_instCommRingInt);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
