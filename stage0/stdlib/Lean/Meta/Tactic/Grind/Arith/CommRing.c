// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing
// Imports: Lean.Util.Trace Lean.Meta.Tactic.Grind.Arith.CommRing.Poly Lean.Meta.Tactic.Grind.Arith.CommRing.Types Lean.Meta.Tactic.Grind.Arith.CommRing.RingId Lean.Meta.Tactic.Grind.Arith.CommRing.Internalize Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr Lean.Meta.Tactic.Grind.Arith.CommRing.Var Lean.Meta.Tactic.Grind.Arith.CommRing.Reify Lean.Meta.Tactic.Grind.Arith.CommRing.EqCnstr Lean.Meta.Tactic.Grind.Arith.CommRing.Proof Lean.Meta.Tactic.Grind.Arith.CommRing.DenoteExpr Lean.Meta.Tactic.Grind.Arith.CommRing.Inv Lean.Meta.Tactic.Grind.Arith.CommRing.PP
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
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_542_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_419_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_460_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_501_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_624_(lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_583_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_665_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_378_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
x_9 = lean_mk_string_unchecked("initFn", 6, 6);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = lean_mk_string_unchecked("_@", 2, 2);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = l_Lean_Name_str___override(x_12, x_7);
x_14 = lean_mk_string_unchecked("Meta", 4, 4);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("Tactic", 6, 6);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Grind", 5, 5);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Arith", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("CommRing", 8, 8);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("_hyg", 4, 4);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Name_num___override(x_25, x_26);
x_28 = lean_unbox(x_5);
x_29 = l_Lean_registerTraceClass(x_4, x_28, x_27, x_1);
return x_29;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("internalize", 11, 11);
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
x_15 = lean_mk_string_unchecked("Meta", 4, 4);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("Grind", 5, 5);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("Arith", 5, 5);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("CommRing", 8, 8);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("_hyg", 4, 4);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = lean_unsigned_to_nat(44u);
x_28 = l_Lean_Name_num___override(x_26, x_27);
x_29 = lean_unbox(x_6);
x_30 = l_Lean_registerTraceClass(x_5, x_29, x_28, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("assert", 6, 6);
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
x_15 = lean_mk_string_unchecked("Meta", 4, 4);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("Grind", 5, 5);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("Arith", 5, 5);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("CommRing", 8, 8);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("_hyg", 4, 4);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = lean_unsigned_to_nat(85u);
x_28 = l_Lean_Name_num___override(x_26, x_27);
x_29 = lean_unbox(x_6);
x_30 = l_Lean_registerTraceClass(x_5, x_29, x_28, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("assert", 6, 6);
x_5 = lean_mk_string_unchecked("unsat", 5, 5);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(126u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("assert", 6, 6);
x_5 = lean_mk_string_unchecked("trivial", 7, 7);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(168u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("assert", 6, 6);
x_5 = lean_mk_string_unchecked("queue", 5, 5);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(210u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("assert", 6, 6);
x_5 = lean_mk_string_unchecked("basis", 5, 5);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(252u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("assert", 6, 6);
x_5 = lean_mk_string_unchecked("store", 5, 5);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(294u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("assert", 6, 6);
x_5 = lean_mk_string_unchecked("discard", 7, 7);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(336u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_378_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("simp", 4, 4);
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
x_15 = lean_mk_string_unchecked("Meta", 4, 4);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("Grind", 5, 5);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("Arith", 5, 5);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("CommRing", 8, 8);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("_hyg", 4, 4);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = lean_unsigned_to_nat(378u);
x_28 = l_Lean_Name_num___override(x_26, x_27);
x_29 = lean_unbox(x_6);
x_30 = l_Lean_registerTraceClass(x_5, x_29, x_28, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_419_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("superpose", 9, 9);
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
x_15 = lean_mk_string_unchecked("Meta", 4, 4);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("Grind", 5, 5);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("Arith", 5, 5);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("CommRing", 8, 8);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("_hyg", 4, 4);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = lean_unsigned_to_nat(419u);
x_28 = l_Lean_Name_num___override(x_26, x_27);
x_29 = lean_unbox(x_6);
x_30 = l_Lean_registerTraceClass(x_5, x_29, x_28, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_460_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ring", 4, 4);
x_4 = lean_mk_string_unchecked("impEq", 5, 5);
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
x_15 = lean_mk_string_unchecked("Meta", 4, 4);
x_16 = l_Lean_Name_str___override(x_14, x_15);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("Grind", 5, 5);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("Arith", 5, 5);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("CommRing", 8, 8);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("_hyg", 4, 4);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = lean_unsigned_to_nat(460u);
x_28 = l_Lean_Name_num___override(x_26, x_27);
x_29 = lean_unbox(x_6);
x_30 = l_Lean_registerTraceClass(x_5, x_29, x_28, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_501_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("debug", 5, 5);
x_4 = lean_mk_string_unchecked("ring", 4, 4);
x_5 = lean_mk_string_unchecked("simp", 4, 4);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(501u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_542_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("debug", 5, 5);
x_4 = lean_mk_string_unchecked("ring", 4, 4);
x_5 = lean_mk_string_unchecked("proof", 5, 5);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(542u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_583_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("debug", 5, 5);
x_4 = lean_mk_string_unchecked("ring", 4, 4);
x_5 = lean_mk_string_unchecked("check", 5, 5);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(583u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_624_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("debug", 5, 5);
x_4 = lean_mk_string_unchecked("ring", 4, 4);
x_5 = lean_mk_string_unchecked("impEq", 5, 5);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(624u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_665_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("debug", 5, 5);
x_4 = lean_mk_string_unchecked("ring", 4, 4);
x_5 = lean_mk_string_unchecked("simpBasis", 9, 9);
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
x_16 = lean_mk_string_unchecked("Meta", 4, 4);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("Tactic", 6, 6);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("Grind", 5, 5);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("Arith", 5, 5);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_mk_string_unchecked("CommRing", 8, 8);
x_25 = l_Lean_Name_str___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("_hyg", 4, 4);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = lean_unsigned_to_nat(665u);
x_29 = l_Lean_Name_num___override(x_27, x_28);
x_30 = lean_unbox(x_7);
x_31 = l_Lean_registerTraceClass(x_6, x_30, x_29, x_1);
return x_31;
}
}
lean_object* initialize_Lean_Util_Trace(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Var(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_Trace(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_RingId(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Var(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Reify(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_EqCnstr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Proof(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_DenoteExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Inv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_PP(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_3_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_44_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_85_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_126_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_168_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_210_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_252_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_294_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_336_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_378_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_419_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_460_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_501_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_542_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_583_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_624_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_initFn____x40_Lean_Meta_Tactic_Grind_Arith_CommRing___hyg_665_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
