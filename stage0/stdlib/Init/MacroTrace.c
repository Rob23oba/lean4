// Lean compiler output
// Module: Init.MacroTrace
// Imports: Init.Data.ToString.Macro Init.Meta
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
lean_object* l_Lean_Syntax_mkNameLit(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_quoteNameMk(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_termMacro_x2etrace_x5b___x5d__;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_String_intercalate(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* _init_l_Lean_termMacro_x2etrace_x5b___x5d__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("termMacro.trace[_]_", 19, 19);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(1022u);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("Macro.trace[", 12, 12);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("ident", 5, 5);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("]", 1, 1);
x_14 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_6);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_mk_string_unchecked("term", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_15);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_24, 0, x_3);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean___aux__Init__MacroTrace______macroRules__Lean__termMacro_x2etrace_x5b___x5d____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("termMacro.trace[_]_", 19, 19);
lean_inc(x_4);
x_6 = l_Lean_Name_mkStr2(x_4, x_5);
lean_inc(x_1);
x_7 = l_Lean_Syntax_isOfKind(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_unsigned_to_nat(3u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = l_Lean_Syntax_getArg(x_1, x_10);
lean_dec(x_1);
x_14 = lean_ctor_get(x_2, 5);
lean_inc(x_14);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_SourceInfo_fromRef(x_14, x_16);
lean_dec(x_14);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 1);
lean_inc(x_19);
lean_dec(x_2);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Term", 4, 4);
x_22 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_4);
x_23 = l_Lean_Name_mkStr4(x_4, x_20, x_21, x_22);
x_24 = lean_mk_string_unchecked("Macro.trace", 11, 11);
x_25 = l_String_toSubstring_x27(x_24);
x_26 = lean_mk_string_unchecked("Macro", 5, 5);
x_27 = lean_mk_string_unchecked("trace", 5, 5);
lean_inc(x_27);
lean_inc(x_26);
x_28 = l_Lean_Name_mkStr2(x_26, x_27);
x_29 = l_Lean_addMacroScope(x_19, x_28, x_18);
lean_inc(x_4);
x_30 = l_Lean_Name_mkStr3(x_4, x_26, x_27);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_17);
x_35 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_35, 0, x_17);
lean_ctor_set(x_35, 1, x_25);
lean_ctor_set(x_35, 2, x_29);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_mk_string_unchecked("null", 4, 4);
x_37 = l_Lean_Name_mkStr1(x_36);
x_55 = l_Lean_Syntax_getId(x_13);
lean_dec(x_13);
x_56 = lean_erase_macro_scopes(x_55);
lean_inc(x_56);
x_57 = l___private_Init_Meta_0__Lean_getEscapedNameParts_x3f(x_31, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = l_Lean_quoteNameMk(x_56);
x_38 = x_58;
goto block_54;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_mk_string_unchecked("quotedName", 10, 10);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_4);
x_61 = l_Lean_Name_mkStr4(x_4, x_20, x_21, x_60);
x_62 = lean_mk_string_unchecked("`", 1, 1);
x_63 = lean_mk_string_unchecked(".", 1, 1);
x_64 = l_String_intercalate(x_63, x_59);
lean_dec(x_63);
x_65 = lean_string_append(x_62, x_64);
lean_dec(x_64);
x_66 = lean_box(2);
x_67 = l_Lean_Syntax_mkNameLit(x_65, x_66);
x_68 = lean_mk_empty_array_with_capacity(x_10);
x_69 = lean_array_push(x_68, x_67);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_61);
lean_ctor_set(x_70, 2, x_69);
x_38 = x_70;
goto block_54;
}
block_54:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_mk_string_unchecked("paren", 5, 5);
x_40 = l_Lean_Name_mkStr4(x_4, x_20, x_21, x_39);
x_41 = lean_mk_string_unchecked("(", 1, 1);
lean_inc(x_17);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("termS!_", 7, 7);
x_44 = l_Lean_Name_mkStr1(x_43);
x_45 = lean_mk_string_unchecked("s!", 2, 2);
lean_inc(x_17);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_17);
lean_ctor_set(x_46, 1, x_45);
lean_inc(x_17);
x_47 = l_Lean_Syntax_node2(x_17, x_44, x_46, x_12);
x_48 = lean_mk_string_unchecked(")", 1, 1);
lean_inc(x_17);
x_49 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_49, 0, x_17);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_17);
x_50 = l_Lean_Syntax_node3(x_17, x_40, x_42, x_47, x_49);
lean_inc(x_17);
x_51 = l_Lean_Syntax_node2(x_17, x_37, x_38, x_50);
x_52 = l_Lean_Syntax_node2(x_17, x_23, x_35, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_3);
return x_53;
}
}
}
}
lean_object* initialize_Init_Data_ToString_Macro(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Meta(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_MacroTrace(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_ToString_Macro(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_termMacro_x2etrace_x5b___x5d__ = _init_l_Lean_termMacro_x2etrace_x5b___x5d__();
lean_mark_persistent(l_Lean_termMacro_x2etrace_x5b___x5d__);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
