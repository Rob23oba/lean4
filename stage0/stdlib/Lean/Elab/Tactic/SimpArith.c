// Lean compiler output
// Module: Lean.Elab.Tactic.SimpArith
// Imports: Lean.Elab.Tactic.Simp Lean.Meta.Tactic.TryThis
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
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Tactic_tacticElabAttribute;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_setArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Tactic_TryThis_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_unsetTrailing(lean_object*);
lean_object* l_Lean_Syntax_setKind(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = l_Lean_Syntax_getArg(x_1, x_3);
if (lean_obj_tag(x_4) == 1)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 2);
lean_inc(x_7);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_7);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_11 = l_Lean_Syntax_setArg(x_1, x_3, x_4);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_13 = lean_ctor_get(x_4, 2);
lean_dec(x_13);
x_14 = lean_ctor_get(x_4, 1);
lean_dec(x_14);
x_15 = lean_ctor_get(x_4, 0);
lean_dec(x_15);
x_16 = lean_array_fget(x_7, x_8);
x_17 = lean_box(0);
x_18 = lean_array_fset(x_7, x_8, x_17);
x_19 = lean_mk_empty_array_with_capacity(x_3);
x_20 = lean_array_push(x_19, x_2);
x_21 = l_Lean_Syntax_getArgs(x_16);
lean_dec(x_16);
x_22 = l_Array_append(lean_box(0), x_20, x_21);
lean_dec(x_21);
x_23 = lean_mk_string_unchecked("null", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_box(2);
lean_ctor_set(x_4, 2, x_22);
lean_ctor_set(x_4, 1, x_24);
lean_ctor_set(x_4, 0, x_25);
x_26 = lean_array_fset(x_18, x_8, x_4);
x_27 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lean_Syntax_setArg(x_1, x_3, x_27);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_4);
x_29 = lean_array_fget(x_7, x_8);
x_30 = lean_box(0);
x_31 = lean_array_fset(x_7, x_8, x_30);
x_32 = lean_mk_empty_array_with_capacity(x_3);
x_33 = lean_array_push(x_32, x_2);
x_34 = l_Lean_Syntax_getArgs(x_29);
lean_dec(x_29);
x_35 = l_Array_append(lean_box(0), x_33, x_34);
lean_dec(x_34);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
x_38 = lean_box(2);
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_35);
x_40 = lean_array_fset(x_31, x_8, x_39);
x_41 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_41, 0, x_5);
lean_ctor_set(x_41, 1, x_6);
lean_ctor_set(x_41, 2, x_40);
x_42 = l_Lean_Syntax_setArg(x_1, x_3, x_41);
return x_42;
}
}
}
else
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = l_Lean_Syntax_setArg(x_1, x_3, x_4);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_SourceInfo_fromRef(x_8, x_10);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
x_17 = lean_mk_string_unchecked("posConfigItem", 13, 13);
x_18 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_17);
x_19 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_11);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("arith", 5, 5);
lean_inc(x_21);
x_22 = l_String_toSubstring_x27(x_21);
x_23 = l_Lean_Name_mkStr1(x_21);
x_24 = lean_box(0);
lean_inc(x_11);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_11);
x_26 = l_Lean_Syntax_node2(x_11, x_18, x_20, x_25);
x_27 = l_Lean_Syntax_node1(x_11, x_16, x_26);
x_28 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(x_1, x_27);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_ctor_get(x_2, 5);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_SourceInfo_fromRef(x_30, x_32);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Parser", 6, 6);
x_36 = lean_mk_string_unchecked("Tactic", 6, 6);
x_37 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_38 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_37);
x_39 = lean_mk_string_unchecked("posConfigItem", 13, 13);
x_40 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_39);
x_41 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_33);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("arith", 5, 5);
lean_inc(x_43);
x_44 = l_String_toSubstring_x27(x_43);
x_45 = l_Lean_Name_mkStr1(x_43);
x_46 = lean_box(0);
lean_inc(x_33);
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_46);
lean_inc(x_33);
x_48 = l_Lean_Syntax_node2(x_33, x_40, x_42, x_47);
x_49 = l_Lean_Syntax_node1(x_33, x_38, x_48);
x_50 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(x_1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_29);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_7 = lean_ctor_get(x_5, 0);
lean_dec(x_7);
x_8 = lean_ctor_get(x_2, 5);
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l_Lean_SourceInfo_fromRef(x_8, x_10);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Parser", 6, 6);
x_14 = lean_mk_string_unchecked("Tactic", 6, 6);
x_15 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_16 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_15);
x_17 = lean_mk_string_unchecked("posConfigItem", 13, 13);
x_18 = l_Lean_Name_mkStr4(x_12, x_13, x_14, x_17);
x_19 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_11);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_11);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_mk_string_unchecked("decide", 6, 6);
lean_inc(x_21);
x_22 = l_String_toSubstring_x27(x_21);
x_23 = l_Lean_Name_mkStr1(x_21);
x_24 = lean_box(0);
lean_inc(x_11);
x_25 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_23);
lean_ctor_set(x_25, 3, x_24);
lean_inc(x_11);
x_26 = l_Lean_Syntax_node2(x_11, x_18, x_20, x_25);
x_27 = l_Lean_Syntax_node1(x_11, x_16, x_26);
x_28 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(x_1, x_27);
lean_ctor_set(x_5, 0, x_28);
return x_5;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_29 = lean_ctor_get(x_5, 1);
lean_inc(x_29);
lean_dec(x_5);
x_30 = lean_ctor_get(x_2, 5);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
x_33 = l_Lean_SourceInfo_fromRef(x_30, x_32);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Parser", 6, 6);
x_36 = lean_mk_string_unchecked("Tactic", 6, 6);
x_37 = lean_mk_string_unchecked("configItem", 10, 10);
lean_inc(x_36);
lean_inc(x_35);
lean_inc(x_34);
x_38 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_37);
x_39 = lean_mk_string_unchecked("posConfigItem", 13, 13);
x_40 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_39);
x_41 = lean_mk_string_unchecked("+", 1, 1);
lean_inc(x_33);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_33);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("decide", 6, 6);
lean_inc(x_43);
x_44 = l_String_toSubstring_x27(x_43);
x_45 = l_Lean_Name_mkStr1(x_43);
x_46 = lean_box(0);
lean_inc(x_33);
x_47 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_47, 0, x_33);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_46);
lean_inc(x_33);
x_48 = l_Lean_Syntax_node2(x_33, x_40, x_42, x_47);
x_49 = l_Lean_Syntax_node1(x_33, x_38, x_48);
x_50 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addConfigItem(x_1, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_29);
return x_51;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = l_Lean_Syntax_setKind(x_1, x_3);
x_5 = lean_unsigned_to_nat(0u);
x_6 = l_Lean_mkAtom(x_2);
x_7 = l_Lean_Syntax_setArg(x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_setKind(x_1, x_2, x_3);
x_10 = l_Lean_Syntax_unsetTrailing(x_9);
lean_inc(x_10);
x_11 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(x_10, x_6, x_7, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addDecide(x_10, x_6, x_7, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(x_16, x_6, x_7, x_17);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_mk_string_unchecked("tactic", 6, 6);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = lean_ctor_get(x_6, 5);
lean_inc(x_24);
x_25 = lean_unsigned_to_nat(0u);
x_26 = l_Lean_Syntax_getArg(x_1, x_25);
lean_dec(x_1);
lean_inc(x_23);
lean_ctor_set(x_18, 1, x_12);
lean_ctor_set(x_18, 0, x_23);
x_27 = lean_box(0);
x_28 = lean_box(0);
x_29 = lean_box(0);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_31, 0, x_18);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set(x_31, 2, x_27);
lean_ctor_set(x_31, 3, x_28);
lean_ctor_set(x_31, 4, x_29);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_14, 1, x_20);
lean_ctor_set(x_14, 0, x_23);
x_32 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_27);
lean_ctor_set(x_32, 2, x_27);
lean_ctor_set(x_32, 3, x_28);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
x_33 = lean_unsigned_to_nat(2u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_31);
x_36 = lean_array_push(x_35, x_32);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_24);
x_38 = lean_mk_string_unchecked("Try these:", 10, 10);
x_39 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_26, x_36, x_37, x_38, x_28, x_27, x_4, x_5, x_6, x_7, x_21);
lean_dec(x_37);
lean_dec(x_26);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_40 = lean_ctor_get(x_18, 0);
x_41 = lean_ctor_get(x_18, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_18);
x_42 = lean_mk_string_unchecked("tactic", 6, 6);
x_43 = l_Lean_Name_mkStr1(x_42);
x_44 = lean_ctor_get(x_6, 5);
lean_inc(x_44);
x_45 = lean_unsigned_to_nat(0u);
x_46 = l_Lean_Syntax_getArg(x_1, x_45);
lean_dec(x_1);
lean_inc(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_12);
x_48 = lean_box(0);
x_49 = lean_box(0);
x_50 = lean_box(0);
x_51 = lean_box(0);
x_52 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_52, 0, x_47);
lean_ctor_set(x_52, 1, x_48);
lean_ctor_set(x_52, 2, x_48);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_50);
lean_ctor_set(x_52, 5, x_51);
lean_ctor_set(x_14, 1, x_40);
lean_ctor_set(x_14, 0, x_43);
x_53 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_53, 0, x_14);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_49);
lean_ctor_set(x_53, 4, x_50);
lean_ctor_set(x_53, 5, x_51);
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_mk_empty_array_with_capacity(x_54);
x_56 = lean_array_push(x_55, x_52);
x_57 = lean_array_push(x_56, x_53);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_44);
x_59 = lean_mk_string_unchecked("Try these:", 10, 10);
x_60 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_46, x_57, x_58, x_59, x_49, x_48, x_4, x_5, x_6, x_7, x_41);
lean_dec(x_58);
lean_dec(x_46);
return x_60;
}
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_61 = lean_ctor_get(x_14, 0);
x_62 = lean_ctor_get(x_14, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_14);
x_63 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addArith(x_61, x_6, x_7, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_mk_string_unchecked("tactic", 6, 6);
x_68 = l_Lean_Name_mkStr1(x_67);
x_69 = lean_ctor_get(x_6, 5);
lean_inc(x_69);
x_70 = lean_unsigned_to_nat(0u);
x_71 = l_Lean_Syntax_getArg(x_1, x_70);
lean_dec(x_1);
lean_inc(x_68);
if (lean_is_scalar(x_66)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_66;
}
lean_ctor_set(x_72, 0, x_68);
lean_ctor_set(x_72, 1, x_12);
x_73 = lean_box(0);
x_74 = lean_box(0);
x_75 = lean_box(0);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_77, 0, x_72);
lean_ctor_set(x_77, 1, x_73);
lean_ctor_set(x_77, 2, x_73);
lean_ctor_set(x_77, 3, x_74);
lean_ctor_set(x_77, 4, x_75);
lean_ctor_set(x_77, 5, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_64);
x_79 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_73);
lean_ctor_set(x_79, 2, x_73);
lean_ctor_set(x_79, 3, x_74);
lean_ctor_set(x_79, 4, x_75);
lean_ctor_set(x_79, 5, x_76);
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_mk_empty_array_with_capacity(x_80);
x_82 = lean_array_push(x_81, x_77);
x_83 = lean_array_push(x_82, x_79);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_69);
x_85 = lean_mk_string_unchecked("Try these:", 10, 10);
x_86 = l_Lean_Meta_Tactic_TryThis_addSuggestions(x_71, x_83, x_84, x_85, x_74, x_73, x_4, x_5, x_6, x_7, x_65);
lean_dec(x_84);
lean_dec(x_71);
return x_86;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_mk_string_unchecked("simp", 4, 4);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_7);
x_11 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_7);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(x_1, x_7, x_11, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("`simp_arith` has been deprecated. It was a shorthand for `simp +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.", 163, 163);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_15, x_2, x_3, x_4, x_5, x_13);
lean_dec(x_5);
lean_dec(x_4);
return x_16;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpArith___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalSimpArith___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpArith", 9, 9);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimpArith", 13, 13);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArith___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("simp!", 5, 5);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Tactic", 6, 6);
x_11 = lean_mk_string_unchecked("simpAutoUnfold", 14, 14);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(x_1, x_7, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("`simp_arith!` has been deprecated. It was a shorthand for `simp! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.", 165, 165);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_16, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalSimpArithBang___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpArithBang___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpArithBang(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpArithBang", 13, 13);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimpArithBang", 17, 17);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpArithBang___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("simp_all", 8, 8);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Tactic", 6, 6);
x_11 = lean_mk_string_unchecked("simpAll", 7, 7);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(x_1, x_7, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("`simp_all_arith` has been deprecated. It was a shorthand for `simp_all +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.", 171, 171);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_16, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalSimpAllArith___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArith___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArith(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpAllArith", 12, 12);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimpAllArith", 16, 16);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArith___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_mk_string_unchecked("simp_all!", 9, 9);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Parser", 6, 6);
x_10 = lean_mk_string_unchecked("Tactic", 6, 6);
x_11 = lean_mk_string_unchecked("simpAllAutoUnfold", 17, 17);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
lean_inc(x_5);
lean_inc(x_4);
x_13 = l___private_Lean_Elab_Tactic_SimpArith_0__Lean_Elab_Tactic_addSuggestions(x_1, x_7, x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_mk_string_unchecked("`simp_all_arith!` has been deprecated. It was a shorthand for `simp_all! +arith +decide`, but most of the time, `+decide` was redundant since simprocs have been implemented.", 173, 173);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_throwError___at___Lean_throwErrorAt___at___Lean_Elab_Tactic_evalTactic_throwExs_spec__0_spec__0___redArg(x_16, x_2, x_3, x_4, x_5, x_14);
lean_dec(x_5);
lean_dec(x_4);
return x_17;
}
else
{
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(x_1, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_evalSimpAllArithBang___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_evalSimpAllArithBang(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = l_Lean_Elab_Tactic_tacticElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Tactic", 6, 6);
x_6 = lean_mk_string_unchecked("simpAllArithBang", 16, 16);
lean_inc(x_5);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("evalSimpAllArithBang", 20, 20);
x_10 = l_Lean_Name_mkStr4(x_3, x_8, x_5, x_9);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_evalSimpAllArithBang___boxed), 10, 0);
x_12 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_10, x_11, x_1);
return x_12;
}
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_TryThis(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_SimpArith(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_TryThis(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpArith__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpArithBang__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllArith__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l___regBuiltin_Lean_Elab_Tactic_evalSimpAllArithBang__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
