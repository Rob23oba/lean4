// Lean compiler output
// Module: Init.Data.List.MinMax
// Imports: Init.Data.List.Lemmas Init.Data.List.Pairwise
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
LEAN_EXPORT lean_object* l___auto____x40_Init_Data_List_MinMax___hyg_599_;
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_dec(x_3);
lean_inc(x_2);
return x_2;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_apply_2(x_3, x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___redArg(x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Init_Data_List_MinMax_0__List_getLast_x3f_match__1_splitter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
return x_6;
}
}
static lean_object* _init_l___auto____x40_Init_Data_List_MinMax___hyg_599_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
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
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("fun", 3, 3);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_2);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = l_Lean_mkAtom(x_17);
lean_inc(x_7);
x_20 = lean_array_push(x_7, x_19);
x_21 = lean_mk_string_unchecked("basicFun", 8, 8);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_21);
x_23 = lean_mk_string_unchecked("a", 1, 1);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_string_utf8_byte_size(x_23);
lean_inc(x_23);
x_26 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = l_Lean_Name_mkStr1(x_23);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_26);
lean_ctor_set(x_29, 2, x_27);
lean_ctor_set(x_29, 3, x_28);
lean_inc(x_7);
x_30 = lean_array_push(x_7, x_29);
x_31 = lean_mk_string_unchecked("b", 1, 1);
x_32 = lean_string_utf8_byte_size(x_31);
lean_inc(x_31);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_24);
lean_ctor_set(x_33, 2, x_32);
x_34 = l_Lean_Name_mkStr1(x_31);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_1);
lean_ctor_set(x_35, 1, x_33);
lean_ctor_set(x_35, 2, x_34);
lean_ctor_set(x_35, 3, x_28);
x_36 = lean_array_push(x_30, x_35);
x_37 = lean_mk_string_unchecked("hole", 4, 4);
lean_inc(x_16);
lean_inc(x_3);
lean_inc(x_2);
x_38 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_37);
x_39 = lean_mk_string_unchecked("_", 1, 1);
x_40 = l_Lean_mkAtom(x_39);
lean_inc(x_7);
x_41 = lean_array_push(x_7, x_40);
x_42 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_38);
lean_ctor_set(x_42, 2, x_41);
lean_inc(x_42);
lean_inc(x_36);
x_43 = lean_array_push(x_36, x_42);
x_44 = lean_array_push(x_43, x_42);
lean_inc(x_11);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_11);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_7);
x_46 = lean_array_push(x_7, x_45);
lean_inc(x_7);
lean_inc(x_11);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_1);
lean_ctor_set(x_47, 1, x_11);
lean_ctor_set(x_47, 2, x_7);
x_48 = lean_array_push(x_46, x_47);
x_49 = lean_mk_string_unchecked("=>", 2, 2);
x_50 = l_Lean_mkAtom(x_49);
x_51 = lean_array_push(x_48, x_50);
x_52 = lean_mk_string_unchecked("app", 3, 3);
x_53 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_52);
x_54 = lean_mk_string_unchecked("Std.Antisymm.antisymm", 21, 21);
x_55 = lean_string_utf8_byte_size(x_54);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_24);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_mk_string_unchecked("Std", 3, 3);
x_58 = lean_mk_string_unchecked("Antisymm", 8, 8);
x_59 = lean_mk_string_unchecked("antisymm", 8, 8);
x_60 = l_Lean_Name_mkStr3(x_57, x_58, x_59);
x_61 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_61, 0, x_1);
lean_ctor_set(x_61, 1, x_56);
lean_ctor_set(x_61, 2, x_60);
lean_ctor_set(x_61, 3, x_28);
lean_inc(x_7);
x_62 = lean_array_push(x_7, x_61);
lean_inc(x_11);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_1);
lean_ctor_set(x_63, 1, x_11);
lean_ctor_set(x_63, 2, x_36);
x_64 = lean_array_push(x_62, x_63);
x_65 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_65, 0, x_1);
lean_ctor_set(x_65, 1, x_53);
lean_ctor_set(x_65, 2, x_64);
x_66 = lean_array_push(x_51, x_65);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_22);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_array_push(x_20, x_67);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_18);
lean_ctor_set(x_69, 2, x_68);
x_70 = lean_array_push(x_15, x_69);
x_71 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_71, 0, x_1);
lean_ctor_set(x_71, 1, x_13);
lean_ctor_set(x_71, 2, x_70);
lean_inc(x_7);
x_72 = lean_array_push(x_7, x_71);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_1);
lean_ctor_set(x_73, 1, x_11);
lean_ctor_set(x_73, 2, x_72);
lean_inc(x_7);
x_74 = lean_array_push(x_7, x_73);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_1);
lean_ctor_set(x_75, 1, x_9);
lean_ctor_set(x_75, 2, x_74);
x_76 = lean_array_push(x_7, x_75);
x_77 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_77, 0, x_1);
lean_ctor_set(x_77, 1, x_6);
lean_ctor_set(x_77, 2, x_76);
return x_77;
}
}
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Data_List_Pairwise(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_MinMax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_List_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Pairwise(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___auto____x40_Init_Data_List_MinMax___hyg_599_ = _init_l___auto____x40_Init_Data_List_MinMax___hyg_599_();
lean_mark_persistent(l___auto____x40_Init_Data_List_MinMax___hyg_599_);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
