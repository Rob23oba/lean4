// Lean compiler output
// Module: Init.Data.List.Nat.Range
// Imports: Init.Data.List.Nat.TakeDrop Init.Data.List.Range Init.Data.List.Pairwise Init.Data.List.Find Init.Data.List.Erase
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
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_List_Nat_Range___hyg_141_;
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_List_Nat_Range___hyg_201_;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
static lean_object* _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_141_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_12 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("optConfig", 9, 9);
x_17 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_16);
lean_inc(x_7);
lean_inc(x_11);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_7);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_array_push(x_15, x_20);
lean_inc(x_18);
x_22 = lean_array_push(x_21, x_18);
lean_inc(x_18);
x_23 = lean_array_push(x_22, x_18);
lean_inc(x_18);
x_24 = lean_array_push(x_23, x_18);
x_25 = lean_array_push(x_24, x_18);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_7);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_array_push(x_7, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_201_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
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
x_12 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_12);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("optConfig", 9, 9);
x_17 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_16);
lean_inc(x_7);
lean_inc(x_11);
x_18 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_7);
lean_inc(x_18);
lean_inc(x_7);
x_19 = lean_array_push(x_7, x_18);
x_20 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_array_push(x_15, x_20);
lean_inc(x_18);
x_22 = lean_array_push(x_21, x_18);
lean_inc(x_18);
x_23 = lean_array_push(x_22, x_18);
lean_inc(x_18);
x_24 = lean_array_push(x_23, x_18);
x_25 = lean_array_push(x_24, x_18);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_13);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_11);
lean_ctor_set(x_28, 2, x_27);
lean_inc(x_7);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_9);
lean_ctor_set(x_30, 2, x_29);
x_31 = lean_array_push(x_7, x_30);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_6);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
lean_object* initialize_Init_Data_List_Nat_TakeDrop(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Range(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Find(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Erase(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_Nat_Range(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Nat_TakeDrop(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Range(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Find(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Erase(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto____x40_Init_Data_List_Nat_Range___hyg_141_ = _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_141_();
lean_mark_persistent(l___auto____x40_Init_Data_List_Nat_Range___hyg_141_);
l___auto____x40_Init_Data_List_Nat_Range___hyg_201_ = _init_l___auto____x40_Init_Data_List_Nat_Range___hyg_201_();
lean_mark_persistent(l___auto____x40_Init_Data_List_Nat_Range___hyg_201_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
