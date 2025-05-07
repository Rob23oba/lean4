// Lean compiler output
// Module: Init.Grind.CommRing.Basic
// Imports: Init.Data.Zero Init.Data.Int.DivMod.Lemmas Init.Data.Int.Pow Init.TacticsExtra
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_ofNat__eq__natCast___autoParam;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_ofNat__succ___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_intCast__neg___autoParam;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_intCast__ofNat___autoParam;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* _init_l_Lean_Grind_CommRing_ofNat__succ___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
lean_inc(x_7);
lean_inc(x_11);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_7);
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_7);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_mk_string_unchecked(";", 1, 1);
x_21 = l_Lean_mkAtom(x_20);
x_22 = lean_array_push(x_19, x_21);
x_23 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_24 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_23);
x_25 = lean_mk_string_unchecked("rfl", 3, 3);
x_26 = l_Lean_mkAtom(x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_22, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_7);
x_31 = lean_array_push(x_7, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_array_push(x_7, x_32);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_ofNat__eq__natCast___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
lean_inc(x_7);
lean_inc(x_11);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_7);
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_7);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_mk_string_unchecked(";", 1, 1);
x_21 = l_Lean_mkAtom(x_20);
x_22 = lean_array_push(x_19, x_21);
x_23 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_24 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_23);
x_25 = lean_mk_string_unchecked("rfl", 3, 3);
x_26 = l_Lean_mkAtom(x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_22, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_7);
x_31 = lean_array_push(x_7, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_array_push(x_7, x_32);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_intCast__ofNat___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
lean_inc(x_7);
lean_inc(x_11);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_7);
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_7);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_mk_string_unchecked(";", 1, 1);
x_21 = l_Lean_mkAtom(x_20);
x_22 = lean_array_push(x_19, x_21);
x_23 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_24 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_23);
x_25 = lean_mk_string_unchecked("rfl", 3, 3);
x_26 = l_Lean_mkAtom(x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_22, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_7);
x_31 = lean_array_push(x_7, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_array_push(x_7, x_32);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
static lean_object* _init_l_Lean_Grind_CommRing_intCast__neg___autoParam() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("intros", 6, 6);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
lean_inc(x_7);
lean_inc(x_11);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_7);
x_17 = lean_array_push(x_15, x_16);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_7);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_mk_string_unchecked(";", 1, 1);
x_21 = l_Lean_mkAtom(x_20);
x_22 = lean_array_push(x_19, x_21);
x_23 = lean_mk_string_unchecked("tacticRfl", 9, 9);
x_24 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_23);
x_25 = lean_mk_string_unchecked("rfl", 3, 3);
x_26 = l_Lean_mkAtom(x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_24);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_22, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_11);
lean_ctor_set(x_30, 2, x_29);
lean_inc(x_7);
x_31 = lean_array_push(x_7, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_31);
x_33 = lean_array_push(x_7, x_32);
x_34 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_6);
lean_ctor_set(x_34, 2, x_33);
return x_34;
}
}
lean_object* initialize_Init_Data_Zero(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin, lean_object*);
lean_object* initialize_Init_TacticsExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Grind_CommRing_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Zero(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_TacticsExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Grind_CommRing_ofNat__succ___autoParam = _init_l_Lean_Grind_CommRing_ofNat__succ___autoParam();
lean_mark_persistent(l_Lean_Grind_CommRing_ofNat__succ___autoParam);
l_Lean_Grind_CommRing_ofNat__eq__natCast___autoParam = _init_l_Lean_Grind_CommRing_ofNat__eq__natCast___autoParam();
lean_mark_persistent(l_Lean_Grind_CommRing_ofNat__eq__natCast___autoParam);
l_Lean_Grind_CommRing_intCast__ofNat___autoParam = _init_l_Lean_Grind_CommRing_intCast__ofNat___autoParam();
lean_mark_persistent(l_Lean_Grind_CommRing_intCast__ofNat___autoParam);
l_Lean_Grind_CommRing_intCast__neg___autoParam = _init_l_Lean_Grind_CommRing_intCast__neg___autoParam();
lean_mark_persistent(l_Lean_Grind_CommRing_intCast__neg___autoParam);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
