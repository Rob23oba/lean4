// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Basic
// Imports: Lean.Elab.Tactic.Basic
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
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_applyCleanWfTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Basic___hyg_5_(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_debug_rawDecreasingByGoal;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Tactic_evalTactic(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Basic___hyg_5_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_2 = lean_mk_string_unchecked("debug", 5, 5);
x_3 = lean_mk_string_unchecked("rawDecreasingByGoal", 19, 19);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_mk_string_unchecked("", 0, 0);
x_7 = lean_mk_string_unchecked("Shows the raw `decreasing_by` goal including internal implementation detail instead of cleaning it up with the `clean_wf` tactic. Can be enabled for debugging purposes. Please report an issue if you have to use this option for other reasons.", 241, 241);
x_8 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_6);
lean_ctor_set(x_8, 2, x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Elab", 4, 4);
x_11 = lean_mk_string_unchecked("WF", 2, 2);
x_12 = l_Lean_Name_mkStr5(x_9, x_10, x_11, x_2, x_3);
x_13 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_4, x_8, x_12, x_1);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_applyCleanWfTactic(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_7, 2);
lean_inc(x_10);
x_11 = l_Lean_Elab_WF_debug_rawDecreasingByGoal;
x_12 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_ref_get(x_8, x_9);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_15 = lean_ctor_get(x_13, 1);
x_16 = lean_ctor_get(x_13, 0);
lean_dec(x_16);
x_17 = lean_ctor_get(x_7, 5);
lean_inc(x_17);
x_18 = l_Lean_SourceInfo_fromRef(x_17, x_12);
lean_dec(x_17);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Tactic", 6, 6);
x_22 = lean_mk_string_unchecked("allGoals", 8, 8);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_23 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_22);
x_24 = lean_mk_string_unchecked("all_goals", 9, 9);
lean_inc(x_18);
lean_ctor_set_tag(x_13, 2);
lean_ctor_set(x_13, 1, x_24);
lean_ctor_set(x_13, 0, x_18);
x_25 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
x_26 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_25);
x_27 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_28 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_27);
x_29 = lean_mk_string_unchecked("null", 4, 4);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = lean_mk_string_unchecked("tacticClean_wf", 14, 14);
x_32 = l_Lean_Name_mkStr1(x_31);
x_33 = lean_mk_string_unchecked("clean_wf", 8, 8);
lean_inc(x_18);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_18);
x_35 = l_Lean_Syntax_node1(x_18, x_32, x_34);
lean_inc(x_18);
x_36 = l_Lean_Syntax_node1(x_18, x_30, x_35);
lean_inc(x_18);
x_37 = l_Lean_Syntax_node1(x_18, x_28, x_36);
lean_inc(x_18);
x_38 = l_Lean_Syntax_node1(x_18, x_26, x_37);
x_39 = l_Lean_Syntax_node2(x_18, x_23, x_13, x_38);
x_40 = l_Lean_Elab_Tactic_evalTactic(x_39, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_41 = lean_ctor_get(x_13, 1);
lean_inc(x_41);
lean_dec(x_13);
x_42 = lean_ctor_get(x_7, 5);
lean_inc(x_42);
x_43 = l_Lean_SourceInfo_fromRef(x_42, x_12);
lean_dec(x_42);
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Parser", 6, 6);
x_46 = lean_mk_string_unchecked("Tactic", 6, 6);
x_47 = lean_mk_string_unchecked("allGoals", 8, 8);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_48 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_47);
x_49 = lean_mk_string_unchecked("all_goals", 9, 9);
lean_inc(x_43);
x_50 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_50, 0, x_43);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
x_52 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_51);
x_53 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
x_54 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_53);
x_55 = lean_mk_string_unchecked("null", 4, 4);
x_56 = l_Lean_Name_mkStr1(x_55);
x_57 = lean_mk_string_unchecked("tacticClean_wf", 14, 14);
x_58 = l_Lean_Name_mkStr1(x_57);
x_59 = lean_mk_string_unchecked("clean_wf", 8, 8);
lean_inc(x_43);
x_60 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_60, 0, x_43);
lean_ctor_set(x_60, 1, x_59);
lean_inc(x_43);
x_61 = l_Lean_Syntax_node1(x_43, x_58, x_60);
lean_inc(x_43);
x_62 = l_Lean_Syntax_node1(x_43, x_56, x_61);
lean_inc(x_43);
x_63 = l_Lean_Syntax_node1(x_43, x_54, x_62);
lean_inc(x_43);
x_64 = l_Lean_Syntax_node1(x_43, x_52, x_63);
x_65 = l_Lean_Syntax_node2(x_43, x_48, x_50, x_64);
x_66 = l_Lean_Elab_Tactic_evalTactic(x_65, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_41);
return x_66;
}
}
else
{
lean_object* x_67; lean_object* x_68; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_9);
return x_68;
}
}
}
lean_object* initialize_Lean_Elab_Tactic_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Basic(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Basic___hyg_5_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_WF_debug_rawDecreasingByGoal = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_WF_debug_rawDecreasingByGoal);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
