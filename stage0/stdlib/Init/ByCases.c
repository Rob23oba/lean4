// Lean compiler output
// Module: Init.ByCases
// Imports: Init.Classical
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_tacticBy__cases___x3a__;
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* _init_l_tacticBy__cases___x3a__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("tacticBy_cases_:_", 17, 17);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_unsigned_to_nat(1022u);
x_4 = lean_mk_string_unchecked("andthen", 7, 7);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_mk_string_unchecked("by_cases ", 9, 9);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = lean_mk_string_unchecked("optional", 8, 8);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("atomic", 6, 6);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked(" : ", 3, 3);
x_18 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_5);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_16);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_5);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_8);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("term", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_3);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticBy_cases_:_", 17, 17);
x_5 = l_Lean_Name_mkStr1(x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = l_Lean_Syntax_matchesNull(x_11, x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_15 = lean_unsigned_to_nat(2u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
lean_dec(x_1);
x_17 = lean_ctor_get(x_2, 5);
lean_inc(x_17);
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
x_20 = l_Lean_SourceInfo_fromRef(x_17, x_19);
lean_dec(x_17);
x_21 = lean_ctor_get(x_2, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_mk_string_unchecked("by_cases", 8, 8);
lean_inc(x_20);
x_24 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_24, 0, x_20);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("null", 4, 4);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_mk_string_unchecked("h", 1, 1);
lean_inc(x_27);
x_28 = l_String_toSubstring_x27(x_27);
x_29 = l_Lean_Name_mkStr1(x_27);
x_30 = l_Lean_addMacroScope(x_22, x_29, x_21);
x_31 = lean_box(0);
lean_inc(x_20);
x_32 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_32, 0, x_20);
lean_ctor_set(x_32, 1, x_28);
lean_ctor_set(x_32, 2, x_30);
lean_ctor_set(x_32, 3, x_31);
x_33 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_20);
x_34 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_33);
lean_inc(x_20);
x_35 = l_Lean_Syntax_node2(x_20, x_26, x_32, x_34);
x_36 = l_Lean_Syntax_node3(x_20, x_5, x_24, x_35, x_16);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__ByCases______macroRules__tacticBy__cases___x3a____2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_mk_string_unchecked("tacticBy_cases_:_", 17, 17);
x_5 = l_Lean_Name_mkStr1(x_4);
lean_inc(x_1);
x_6 = l_Lean_Syntax_isOfKind(x_1, x_5);
lean_dec(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(1);
x_8 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Syntax_getArg(x_1, x_9);
x_11 = lean_unsigned_to_nat(2u);
lean_inc(x_10);
x_12 = l_Lean_Syntax_matchesNull(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(1);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_Lean_Syntax_getArg(x_10, x_15);
lean_dec(x_10);
x_17 = l_Lean_Syntax_getArg(x_1, x_11);
lean_dec(x_1);
x_18 = lean_ctor_get(x_2, 5);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_SourceInfo_fromRef(x_18, x_20);
lean_dec(x_18);
x_22 = lean_ctor_get(x_2, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 1);
lean_inc(x_23);
lean_dec(x_2);
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("Parser", 6, 6);
x_26 = lean_mk_string_unchecked("Tactic", 6, 6);
x_27 = lean_mk_string_unchecked("open", 4, 4);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
lean_inc(x_21);
x_29 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_29, 0, x_21);
lean_ctor_set(x_29, 1, x_27);
x_30 = lean_mk_string_unchecked("Command", 7, 7);
x_31 = lean_mk_string_unchecked("openSimple", 10, 10);
lean_inc(x_25);
lean_inc(x_24);
x_32 = l_Lean_Name_mkStr4(x_24, x_25, x_30, x_31);
x_33 = lean_mk_string_unchecked("null", 4, 4);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_mk_string_unchecked("Classical", 9, 9);
lean_inc(x_35);
x_36 = l_String_toSubstring_x27(x_35);
x_37 = l_Lean_Name_mkStr1(x_35);
lean_inc(x_22);
lean_inc(x_37);
lean_inc(x_23);
x_38 = l_Lean_addMacroScope(x_23, x_37, x_22);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
lean_inc(x_21);
x_42 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_42, 0, x_21);
lean_ctor_set(x_42, 1, x_36);
lean_ctor_set(x_42, 2, x_38);
lean_ctor_set(x_42, 3, x_41);
lean_inc(x_34);
lean_inc(x_21);
x_43 = l_Lean_Syntax_node1(x_21, x_34, x_42);
lean_inc(x_21);
x_44 = l_Lean_Syntax_node1(x_21, x_32, x_43);
x_45 = lean_mk_string_unchecked("in", 2, 2);
lean_inc(x_21);
x_46 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_48 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_47);
x_49 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
x_50 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_49);
x_51 = lean_mk_string_unchecked("refine", 6, 6);
lean_inc(x_51);
lean_inc(x_25);
lean_inc(x_24);
x_52 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_51);
lean_inc(x_21);
x_53 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_53, 0, x_21);
lean_ctor_set(x_53, 1, x_51);
x_54 = lean_mk_string_unchecked("termDepIfThenElse", 17, 17);
x_55 = l_Lean_Name_mkStr1(x_54);
x_56 = lean_mk_string_unchecked("if", 2, 2);
lean_inc(x_21);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("binderIdent", 11, 11);
lean_inc(x_24);
x_59 = l_Lean_Name_mkStr2(x_24, x_58);
lean_inc(x_21);
x_60 = l_Lean_Syntax_node1(x_21, x_59, x_16);
x_61 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_21);
x_62 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_62, 0, x_21);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_mk_string_unchecked("then", 4, 4);
lean_inc(x_21);
x_64 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_64, 0, x_21);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_mk_string_unchecked("Term", 4, 4);
x_66 = lean_mk_string_unchecked("syntheticHole", 13, 13);
x_67 = l_Lean_Name_mkStr4(x_24, x_25, x_65, x_66);
x_68 = lean_mk_string_unchecked("\?", 1, 1);
lean_inc(x_21);
x_69 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_69, 0, x_21);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_mk_string_unchecked("pos", 3, 3);
lean_inc(x_70);
x_71 = l_String_toSubstring_x27(x_70);
x_72 = l_Lean_Name_mkStr1(x_70);
lean_inc(x_22);
lean_inc(x_23);
x_73 = l_Lean_addMacroScope(x_23, x_72, x_22);
lean_inc(x_21);
x_74 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_74, 0, x_21);
lean_ctor_set(x_74, 1, x_71);
lean_ctor_set(x_74, 2, x_73);
lean_ctor_set(x_74, 3, x_40);
lean_inc(x_69);
lean_inc(x_67);
lean_inc(x_21);
x_75 = l_Lean_Syntax_node2(x_21, x_67, x_69, x_74);
x_76 = lean_mk_string_unchecked("else", 4, 4);
lean_inc(x_21);
x_77 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_77, 0, x_21);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("neg", 3, 3);
lean_inc(x_78);
x_79 = l_String_toSubstring_x27(x_78);
x_80 = l_Lean_Name_mkStr1(x_78);
x_81 = l_Lean_addMacroScope(x_23, x_80, x_22);
lean_inc(x_21);
x_82 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_82, 0, x_21);
lean_ctor_set(x_82, 1, x_79);
lean_ctor_set(x_82, 2, x_81);
lean_ctor_set(x_82, 3, x_40);
lean_inc(x_21);
x_83 = l_Lean_Syntax_node2(x_21, x_67, x_69, x_82);
lean_inc(x_21);
x_84 = l_Lean_Syntax_node8(x_21, x_55, x_57, x_60, x_62, x_17, x_64, x_75, x_77, x_83);
lean_inc(x_21);
x_85 = l_Lean_Syntax_node2(x_21, x_52, x_53, x_84);
lean_inc(x_21);
x_86 = l_Lean_Syntax_node1(x_21, x_34, x_85);
lean_inc(x_21);
x_87 = l_Lean_Syntax_node1(x_21, x_50, x_86);
lean_inc(x_21);
x_88 = l_Lean_Syntax_node1(x_21, x_48, x_87);
x_89 = l_Lean_Syntax_node4(x_21, x_28, x_29, x_44, x_46, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_3);
return x_90;
}
}
}
}
lean_object* initialize_Init_Classical(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_ByCases(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Classical(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_tacticBy__cases___x3a__ = _init_l_tacticBy__cases___x3a__();
lean_mark_persistent(l_tacticBy__cases___x3a__);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
