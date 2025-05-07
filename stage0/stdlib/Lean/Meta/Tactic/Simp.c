// Lean compiler output
// Module: Lean.Meta.Tactic.Simp
// Imports: Lean.Meta.Tactic.Simp.SimpTheorems Lean.Meta.Tactic.Simp.SimpCongrTheorems Lean.Meta.Tactic.Simp.Types Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Simp.Rewrite Lean.Meta.Tactic.Simp.SimpAll Lean.Meta.Tactic.Simp.Simproc Lean.Meta.Tactic.Simp.BuiltinSimprocs Lean.Meta.Tactic.Simp.RegisterCommand Lean.Meta.Tactic.Simp.Attr Lean.Meta.Tactic.Simp.Diagnostics Lean.Meta.Tactic.Simp.Arith
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
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_154_(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78_(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_116_(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_304_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_192_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_341_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_267_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_230_(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_40_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_3);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("initFn", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("_@", 2, 2);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = l_Lean_Name_str___override(x_13, x_8);
x_15 = l_Lean_Name_str___override(x_14, x_2);
x_16 = l_Lean_Name_str___override(x_15, x_3);
x_17 = lean_mk_string_unchecked("Simp", 4, 4);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("_hyg", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_unsigned_to_nat(3u);
x_22 = l_Lean_Name_num___override(x_20, x_21);
x_23 = lean_unbox(x_6);
x_24 = l_Lean_registerTraceClass(x_5, x_23, x_22, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_40_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
x_5 = lean_mk_string_unchecked("congr", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(40u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
x_5 = lean_mk_string_unchecked("discharge", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(78u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_116_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
x_5 = lean_mk_string_unchecked("rewrite", 7, 7);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(116u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_154_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
x_5 = lean_mk_string_unchecked("unify", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(154u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_192_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
x_5 = lean_mk_string_unchecked("ground", 6, 6);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(1);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(192u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_230_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
x_5 = lean_mk_string_unchecked("numSteps", 8, 8);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(230u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_267_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
x_5 = lean_mk_string_unchecked("heads", 5, 5);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(267u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_304_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_2 = lean_mk_string_unchecked("Debug", 5, 5);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_4);
lean_inc(x_3);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_9);
x_16 = l_Lean_Name_str___override(x_15, x_3);
x_17 = l_Lean_Name_str___override(x_16, x_4);
x_18 = lean_mk_string_unchecked("Simp", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("_hyg", 4, 4);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_unsigned_to_nat(304u);
x_23 = l_Lean_Name_num___override(x_21, x_22);
x_24 = lean_unbox(x_7);
x_25 = l_Lean_registerTraceClass(x_6, x_24, x_23, x_1);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_341_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Debug", 5, 5);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("simp", 4, 4);
x_6 = lean_mk_string_unchecked("congr", 5, 5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(1);
x_9 = lean_box(0);
x_10 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_10);
x_17 = l_Lean_Name_str___override(x_16, x_3);
x_18 = l_Lean_Name_str___override(x_17, x_4);
x_19 = lean_mk_string_unchecked("Simp", 4, 4);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(341u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_8);
x_26 = l_Lean_registerTraceClass(x_7, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Rewrite(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_SimpAll(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_RegisterCommand(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Diagnostics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_SimpTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpCongrTheorems(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Rewrite(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_SimpAll(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Simproc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_BuiltinSimprocs(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_RegisterCommand(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Diagnostics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_40_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_78_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_116_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_154_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_192_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_230_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_267_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_304_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Simp___hyg_341_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
