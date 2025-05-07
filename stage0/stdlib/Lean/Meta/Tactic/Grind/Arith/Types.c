// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Types
// Imports: Lean.Meta.Tactic.Grind.Arith.Offset.Types Lean.Meta.Tactic.Grind.Arith.Cutsat.Types Lean.Meta.Tactic.Grind.Arith.CommRing.Types
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
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* l_instHashableInt___lam__0___boxed(lean_object*);
lean_object* l_instBEqProd___redArg(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_instInhabitedState;
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashable;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_instInhabitedState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; size_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_1 = l_Array_empty(lean_box(0));
lean_inc(x_1);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
lean_inc(x_1);
x_6 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_6, 0, x_2);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 2, x_3);
lean_ctor_set(x_6, 3, x_3);
lean_ctor_set_usize(x_6, 4, x_5);
x_7 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_7);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
lean_inc(x_7);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_7);
lean_inc(x_7);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_7);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_3);
lean_ctor_set(x_12, 3, x_3);
lean_ctor_set_usize(x_12, 4, x_5);
lean_inc(x_1);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
lean_inc(x_1);
x_14 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
lean_ctor_set(x_14, 2, x_3);
lean_ctor_set(x_14, 3, x_3);
lean_ctor_set_usize(x_14, 4, x_5);
x_15 = lean_box(0);
lean_inc(x_12);
lean_inc(x_8);
lean_inc(x_6);
x_16 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_8);
lean_ctor_set(x_16, 2, x_9);
lean_ctor_set(x_16, 3, x_10);
lean_ctor_set(x_16, 4, x_12);
lean_ctor_set(x_16, 5, x_12);
lean_ctor_set(x_16, 6, x_14);
lean_ctor_set(x_16, 7, x_15);
lean_inc(x_7);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_7);
lean_inc(x_7);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_7);
lean_inc(x_1);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_1);
lean_inc(x_1);
x_20 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_1);
lean_ctor_set(x_20, 2, x_3);
lean_ctor_set(x_20, 3, x_3);
lean_ctor_set_usize(x_20, 4, x_5);
lean_inc(x_1);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_1);
lean_inc(x_1);
x_22 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_1);
lean_ctor_set(x_22, 2, x_3);
lean_ctor_set(x_22, 3, x_3);
lean_ctor_set_usize(x_22, 4, x_5);
lean_inc(x_1);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_1);
lean_inc(x_1);
x_24 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_1);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_3);
lean_ctor_set_usize(x_24, 4, x_5);
lean_inc(x_1);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_1);
lean_inc(x_1);
x_26 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_1);
lean_ctor_set(x_26, 2, x_3);
lean_ctor_set(x_26, 3, x_3);
lean_ctor_set_usize(x_26, 4, x_5);
x_27 = lean_box(0);
lean_inc(x_1);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_1);
lean_inc(x_1);
x_29 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_1);
lean_ctor_set(x_29, 2, x_3);
lean_ctor_set(x_29, 3, x_3);
lean_ctor_set_usize(x_29, 4, x_5);
lean_inc(x_1);
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_1);
lean_inc(x_1);
x_31 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_1);
lean_ctor_set(x_31, 2, x_3);
lean_ctor_set(x_31, 3, x_3);
lean_ctor_set_usize(x_31, 4, x_5);
x_32 = lean_box(0);
x_33 = lean_box(0);
lean_inc(x_7);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_7);
x_35 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_36 = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
x_37 = l_instBEqOfDecidableEq___redArg(x_36);
x_38 = l_instBEqProd___redArg(x_35, x_37);
x_39 = l_Lean_Expr_instHashable;
x_40 = lean_alloc_closure((void*)(l_instHashableInt___lam__0___boxed), 1, 0);
x_41 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_40);
x_42 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_38, x_41);
lean_dec(x_41);
lean_dec(x_38);
lean_inc(x_22);
lean_inc_n(x_8, 2);
x_43 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_43, 0, x_6);
lean_ctor_set(x_43, 1, x_8);
lean_ctor_set(x_43, 2, x_17);
lean_ctor_set(x_43, 3, x_18);
lean_ctor_set(x_43, 4, x_8);
lean_ctor_set(x_43, 5, x_20);
lean_ctor_set(x_43, 6, x_22);
lean_ctor_set(x_43, 7, x_22);
lean_ctor_set(x_43, 8, x_24);
lean_ctor_set(x_43, 9, x_26);
lean_ctor_set(x_43, 10, x_27);
lean_ctor_set(x_43, 11, x_29);
lean_ctor_set(x_43, 12, x_31);
lean_ctor_set(x_43, 13, x_3);
lean_ctor_set(x_43, 14, x_33);
lean_ctor_set(x_43, 15, x_34);
lean_ctor_set(x_43, 16, x_42);
x_44 = lean_unbox(x_32);
lean_ctor_set_uint8(x_43, sizeof(void*)*17, x_44);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_7);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_1);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set(x_46, 2, x_8);
lean_ctor_set(x_46, 3, x_3);
x_47 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_47, 0, x_16);
lean_ctor_set(x_47, 1, x_43);
lean_ctor_set(x_47, 2, x_46);
return x_47;
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Types(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_Cutsat_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_instInhabitedState = _init_l_Lean_Meta_Grind_Arith_instInhabitedState();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_instInhabitedState);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
