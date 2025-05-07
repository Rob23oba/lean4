// Lean compiler output
// Module: Lake.Util.Family
// Imports: Lean.Parser.Command
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___lam__0___boxed(lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Syntax_getId(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_mkIdentFrom(lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_mkApp(lean_object*, lean_object*);
lean_object* l_Array_mkArray1___redArg(lean_object*);
lean_object* l_Lean_Macro_resolveGlobalName(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_extractMacroScopes(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___lam__0(lean_object*);
lean_object* l_Lean_Macro_throwErrorAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_familyDef;
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
static lean_object* _init_l_Lake_familyDef() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("familyDef", 9, 9);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(1022u);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("optional", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Parser", 6, 6);
x_11 = lean_mk_string_unchecked("Command", 7, 7);
x_12 = lean_mk_string_unchecked("docComment", 10, 10);
x_13 = l_Lean_Name_mkStr4(x_9, x_10, x_11, x_12);
x_14 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("family_def ", 11, 11);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_6);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked("ident", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
lean_inc(x_21);
lean_inc(x_6);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked(" : ", 3, 3);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_6);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_22);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_6);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_6);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_21);
x_27 = lean_mk_string_unchecked("term", 4, 4);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_30);
lean_inc(x_6);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_mk_string_unchecked(" := ", 4, 4);
x_33 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_inc(x_6);
x_34 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_34, 0, x_6);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_33);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_6);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_30);
x_36 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_36, 0, x_3);
lean_ctor_set(x_36, 1, x_4);
lean_ctor_set(x_36, 2, x_35);
return x_36;
}
}
LEAN_EXPORT uint8_t l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("Lake", 4, 4);
x_5 = lean_mk_string_unchecked("familyDef", 9, 9);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_134; lean_object* x_186; 
x_10 = lean_alloc_closure((void*)(l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___lam__0___boxed), 1, 0);
x_11 = lean_unsigned_to_nat(0u);
x_12 = l_Lean_Syntax_getArg(x_1, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = l_Lean_Syntax_getArg(x_1, x_13);
x_15 = lean_unsigned_to_nat(4u);
x_16 = l_Lean_Syntax_getArg(x_1, x_15);
x_17 = lean_unsigned_to_nat(5u);
x_18 = l_Lean_Syntax_getArg(x_1, x_17);
x_19 = lean_unsigned_to_nat(7u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_186 = l_Lean_Syntax_getOptional_x3f(x_12);
lean_dec(x_12);
if (lean_obj_tag(x_186) == 0)
{
lean_object* x_187; 
x_187 = lean_box(0);
x_134 = x_187;
goto block_185;
}
else
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_186);
if (x_188 == 0)
{
x_134 = x_186;
goto block_185;
}
else
{
lean_object* x_189; lean_object* x_190; 
x_189 = lean_ctor_get(x_186, 0);
lean_inc(x_189);
lean_dec(x_186);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_134 = x_190;
goto block_185;
}
}
block_133:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_inc(x_25);
x_36 = l_Array_append(lean_box(0), x_25, x_35);
lean_dec(x_35);
lean_inc(x_28);
lean_inc(x_32);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_32);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_mk_string_unchecked("Term", 4, 4);
x_39 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_38);
lean_inc(x_30);
lean_inc(x_23);
x_40 = l_Lean_Name_mkStr4(x_23, x_30, x_38, x_39);
x_41 = lean_mk_string_unchecked("@[", 2, 2);
lean_inc(x_32);
x_42 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("attrInstance", 12, 12);
lean_inc(x_38);
lean_inc(x_30);
lean_inc(x_23);
x_44 = l_Lean_Name_mkStr4(x_23, x_30, x_38, x_43);
x_45 = lean_mk_string_unchecked("attrKind", 8, 8);
lean_inc(x_38);
lean_inc(x_30);
lean_inc(x_23);
x_46 = l_Lean_Name_mkStr4(x_23, x_30, x_38, x_45);
lean_inc(x_28);
lean_inc(x_32);
x_47 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_47, 0, x_32);
lean_ctor_set(x_47, 1, x_28);
lean_ctor_set(x_47, 2, x_25);
lean_inc(x_47);
lean_inc(x_32);
x_48 = l_Lean_Syntax_node1(x_32, x_46, x_47);
x_49 = lean_mk_string_unchecked("Attr", 4, 4);
x_50 = lean_mk_string_unchecked("simp", 4, 4);
lean_inc(x_50);
lean_inc(x_30);
lean_inc(x_23);
x_51 = l_Lean_Name_mkStr4(x_23, x_30, x_49, x_50);
lean_inc(x_32);
x_52 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_52, 0, x_32);
lean_ctor_set(x_52, 1, x_50);
lean_inc_n(x_47, 3);
lean_inc(x_32);
x_53 = l_Lean_Syntax_node4(x_32, x_51, x_52, x_47, x_47, x_47);
lean_inc(x_48);
lean_inc(x_32);
x_54 = l_Lean_Syntax_node2(x_32, x_44, x_48, x_53);
lean_inc(x_28);
lean_inc(x_32);
x_55 = l_Lean_Syntax_node1(x_32, x_28, x_54);
x_56 = lean_mk_string_unchecked("]", 1, 1);
lean_inc(x_32);
x_57 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_57, 0, x_32);
lean_ctor_set(x_57, 1, x_56);
lean_inc(x_32);
x_58 = l_Lean_Syntax_node3(x_32, x_40, x_42, x_55, x_57);
lean_inc(x_28);
lean_inc(x_32);
x_59 = l_Lean_Syntax_node1(x_32, x_28, x_58);
lean_inc_n(x_47, 4);
lean_inc(x_24);
lean_inc(x_32);
x_60 = l_Lean_Syntax_node6(x_32, x_24, x_37, x_59, x_47, x_47, x_47, x_47);
x_61 = lean_mk_string_unchecked("axiom", 5, 5);
lean_inc(x_61);
lean_inc(x_33);
lean_inc(x_30);
lean_inc(x_23);
x_62 = l_Lean_Name_mkStr4(x_23, x_30, x_33, x_61);
lean_inc(x_32);
x_63 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_63, 0, x_32);
lean_ctor_set(x_63, 1, x_61);
x_64 = lean_mk_string_unchecked("declId", 6, 6);
lean_inc(x_33);
lean_inc(x_30);
lean_inc(x_23);
x_65 = l_Lean_Name_mkStr4(x_23, x_30, x_33, x_64);
x_66 = l_Lean_mkIdentFrom(x_14, x_34, x_7);
lean_dec(x_14);
x_67 = lean_mk_empty_array_with_capacity(x_11);
x_68 = lean_box(2);
lean_inc(x_28);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_28);
lean_ctor_set(x_69, 2, x_67);
x_70 = lean_mk_empty_array_with_capacity(x_13);
lean_inc(x_66);
x_71 = lean_array_push(x_70, x_66);
x_72 = lean_array_push(x_71, x_69);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_68);
lean_ctor_set(x_73, 1, x_65);
lean_ctor_set(x_73, 2, x_72);
x_74 = lean_mk_string_unchecked("declSig", 7, 7);
lean_inc(x_33);
lean_inc(x_30);
lean_inc(x_23);
x_75 = l_Lean_Name_mkStr4(x_23, x_30, x_33, x_74);
x_76 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_38);
lean_inc(x_30);
lean_inc(x_23);
x_77 = l_Lean_Name_mkStr4(x_23, x_30, x_38, x_76);
x_78 = lean_mk_string_unchecked(":", 1, 1);
lean_inc(x_32);
x_79 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_79, 0, x_32);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("term_=_", 7, 7);
x_81 = l_Lean_Name_mkStr1(x_80);
x_82 = l_Lean_Syntax_mkApp(x_29, x_21);
x_83 = lean_mk_string_unchecked("=", 1, 1);
lean_inc(x_32);
x_84 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_84, 0, x_32);
lean_ctor_set(x_84, 1, x_83);
lean_inc(x_20);
lean_inc(x_32);
x_85 = l_Lean_Syntax_node3(x_32, x_81, x_82, x_84, x_20);
lean_inc(x_79);
lean_inc(x_77);
lean_inc(x_32);
x_86 = l_Lean_Syntax_node2(x_32, x_77, x_79, x_85);
lean_inc(x_47);
lean_inc(x_75);
lean_inc(x_32);
x_87 = l_Lean_Syntax_node2(x_32, x_75, x_47, x_86);
lean_inc(x_32);
x_88 = l_Lean_Syntax_node3(x_32, x_62, x_63, x_73, x_87);
lean_inc(x_26);
lean_inc(x_32);
x_89 = l_Lean_Syntax_node2(x_32, x_26, x_60, x_88);
lean_inc_n(x_47, 6);
lean_inc(x_32);
x_90 = l_Lean_Syntax_node6(x_32, x_24, x_47, x_47, x_47, x_47, x_47, x_47);
x_91 = lean_mk_string_unchecked("instance", 8, 8);
lean_inc(x_91);
lean_inc(x_33);
lean_inc(x_30);
lean_inc(x_23);
x_92 = l_Lean_Name_mkStr4(x_23, x_30, x_33, x_91);
lean_inc(x_32);
x_93 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_93, 0, x_32);
lean_ctor_set(x_93, 1, x_91);
x_94 = lean_mk_string_unchecked("app", 3, 3);
lean_inc(x_38);
lean_inc(x_30);
lean_inc(x_23);
x_95 = l_Lean_Name_mkStr4(x_23, x_30, x_38, x_94);
x_96 = lean_mk_string_unchecked("FamilyDef", 9, 9);
lean_inc(x_96);
x_97 = l_String_toSubstring_x27(x_96);
lean_inc(x_96);
x_98 = l_Lean_Name_mkStr1(x_96);
x_99 = l_Lean_addMacroScope(x_22, x_98, x_27);
x_100 = l_Lean_Name_mkStr2(x_4, x_96);
x_101 = lean_box(0);
lean_inc(x_100);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_100);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_106, 0, x_102);
lean_ctor_set(x_106, 1, x_105);
lean_inc(x_32);
x_107 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_107, 0, x_32);
lean_ctor_set(x_107, 1, x_97);
lean_ctor_set(x_107, 2, x_99);
lean_ctor_set(x_107, 3, x_106);
lean_inc(x_28);
lean_inc(x_32);
x_108 = l_Lean_Syntax_node3(x_32, x_28, x_16, x_18, x_20);
lean_inc(x_32);
x_109 = l_Lean_Syntax_node2(x_32, x_95, x_107, x_108);
lean_inc(x_32);
x_110 = l_Lean_Syntax_node2(x_32, x_77, x_79, x_109);
lean_inc(x_47);
lean_inc(x_32);
x_111 = l_Lean_Syntax_node2(x_32, x_75, x_47, x_110);
x_112 = lean_mk_string_unchecked("declValSimple", 13, 13);
lean_inc(x_30);
lean_inc(x_23);
x_113 = l_Lean_Name_mkStr4(x_23, x_30, x_33, x_112);
x_114 = lean_mk_string_unchecked(":=", 2, 2);
lean_inc(x_32);
x_115 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_115, 0, x_32);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("anonymousCtor", 13, 13);
lean_inc(x_30);
lean_inc(x_23);
x_117 = l_Lean_Name_mkStr4(x_23, x_30, x_38, x_116);
x_118 = lean_mk_string_unchecked("⟨", 3, 1);
lean_inc(x_32);
x_119 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_119, 0, x_32);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_28);
lean_inc(x_32);
x_120 = l_Lean_Syntax_node1(x_32, x_28, x_66);
x_121 = lean_mk_string_unchecked("⟩", 3, 1);
lean_inc(x_32);
x_122 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_122, 0, x_32);
lean_ctor_set(x_122, 1, x_121);
lean_inc(x_32);
x_123 = l_Lean_Syntax_node3(x_32, x_117, x_119, x_120, x_122);
x_124 = lean_mk_string_unchecked("Termination", 11, 11);
x_125 = lean_mk_string_unchecked("suffix", 6, 6);
x_126 = l_Lean_Name_mkStr4(x_23, x_30, x_124, x_125);
lean_inc_n(x_47, 2);
lean_inc(x_32);
x_127 = l_Lean_Syntax_node2(x_32, x_126, x_47, x_47);
lean_inc(x_47);
lean_inc(x_32);
x_128 = l_Lean_Syntax_node4(x_32, x_113, x_115, x_123, x_127, x_47);
lean_inc(x_47);
lean_inc(x_32);
x_129 = l_Lean_Syntax_node6(x_32, x_92, x_48, x_93, x_47, x_47, x_111, x_128);
lean_inc(x_32);
x_130 = l_Lean_Syntax_node2(x_32, x_26, x_90, x_129);
x_131 = l_Lean_Syntax_node2(x_32, x_28, x_89, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_31);
return x_132;
}
block_185:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_135 = l_Lean_Syntax_getId(x_16);
x_136 = l_Lean_extractMacroScopes(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
lean_dec(x_136);
lean_inc(x_2);
lean_inc(x_137);
x_138 = l_Lean_Macro_resolveGlobalName(x_137, x_2, x_3);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 0)
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
lean_dec(x_134);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_14);
lean_dec(x_4);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_mk_string_unchecked("unknown family '", 16, 16);
x_142 = l_Lean_Name_toString(x_137, x_7, x_10);
x_143 = lean_string_append(x_141, x_142);
lean_dec(x_142);
x_144 = lean_mk_string_unchecked("'", 1, 1);
x_145 = lean_string_append(x_143, x_144);
lean_dec(x_144);
x_146 = l_Lean_Macro_throwErrorAt(lean_box(0), x_16, x_145, x_2, x_140);
lean_dec(x_2);
lean_dec(x_16);
x_147 = !lean_is_exclusive(x_146);
if (x_147 == 0)
{
return x_146;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_146, 0);
x_149 = lean_ctor_get(x_146, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_146);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_137);
lean_dec(x_10);
x_151 = lean_ctor_get(x_139, 0);
lean_inc(x_151);
lean_dec(x_139);
x_152 = lean_ctor_get(x_138, 1);
lean_inc(x_152);
lean_dec(x_138);
x_153 = lean_ctor_get(x_151, 0);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_unsigned_to_nat(1u);
x_155 = lean_mk_empty_array_with_capacity(x_154);
lean_inc(x_18);
x_156 = lean_array_push(x_155, x_18);
x_157 = lean_mk_string_unchecked("_root_", 6, 6);
x_158 = l_Lean_Name_mkStr1(x_157);
x_159 = l_Lean_Name_append(x_158, x_153);
x_160 = l_Lean_Syntax_getId(x_14);
x_161 = l_Lean_Name_append(x_159, x_160);
x_162 = lean_ctor_get(x_2, 5);
lean_inc(x_162);
x_163 = lean_box(0);
x_164 = lean_unbox(x_163);
x_165 = l_Lean_SourceInfo_fromRef(x_162, x_164);
lean_dec(x_162);
x_166 = lean_ctor_get(x_2, 2);
lean_inc(x_166);
x_167 = lean_ctor_get(x_2, 1);
lean_inc(x_167);
lean_dec(x_2);
x_168 = lean_mk_string_unchecked("null", 4, 4);
x_169 = l_Lean_Name_mkStr1(x_168);
x_170 = lean_mk_string_unchecked("Lean", 4, 4);
x_171 = lean_mk_string_unchecked("Parser", 6, 6);
x_172 = lean_mk_string_unchecked("Command", 7, 7);
x_173 = lean_mk_string_unchecked("declaration", 11, 11);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
x_174 = l_Lean_Name_mkStr4(x_170, x_171, x_172, x_173);
x_175 = lean_mk_string_unchecked("declModifiers", 13, 13);
lean_inc(x_172);
lean_inc(x_171);
lean_inc(x_170);
x_176 = l_Lean_Name_mkStr4(x_170, x_171, x_172, x_175);
x_177 = l_Array_mkArray0(lean_box(0));
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_178; 
x_178 = l_Array_empty(lean_box(0));
lean_inc(x_16);
x_21 = x_156;
x_22 = x_167;
x_23 = x_170;
x_24 = x_176;
x_25 = x_177;
x_26 = x_174;
x_27 = x_166;
x_28 = x_169;
x_29 = x_16;
x_30 = x_171;
x_31 = x_152;
x_32 = x_165;
x_33 = x_172;
x_34 = x_161;
x_35 = x_178;
goto block_133;
}
else
{
lean_object* x_179; lean_object* x_180; 
x_179 = lean_ctor_get(x_134, 0);
lean_inc(x_179);
lean_dec(x_134);
x_180 = l_Array_mkArray1___redArg(x_179);
lean_inc(x_16);
x_21 = x_156;
x_22 = x_167;
x_23 = x_170;
x_24 = x_176;
x_25 = x_177;
x_26 = x_174;
x_27 = x_166;
x_28 = x_169;
x_29 = x_16;
x_30 = x_171;
x_31 = x_152;
x_32 = x_165;
x_33 = x_172;
x_34 = x_161;
x_35 = x_180;
goto block_133;
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
x_181 = !lean_is_exclusive(x_138);
if (x_181 == 0)
{
return x_138;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_138, 0);
x_183 = lean_ctor_get(x_138, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_138);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lake___aux__Lake__Util__Family______macroRules__Lake__familyDef__1___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Util_Family(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_familyDef = _init_l_Lake_familyDef();
lean_mark_persistent(l_Lake_familyDef);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
