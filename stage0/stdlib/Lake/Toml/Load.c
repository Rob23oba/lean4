// Lean compiler output
// Module: Lake.Toml.Load
// Imports: Lake.Toml.Elab Lake.Util.Message
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
lean_object* l_Lean_Core_getMaxHeartbeats(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
lean_object* l_Lake_Toml_elabToml(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Data_Trie_empty(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
extern lean_object* l_Lake_Toml_toml;
lean_object* l_Lean_Parser_ParserFn_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_Parser_mkParserState(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lake_mkParserErrorMessage(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
uint8_t lean_string_utf8_at_end(lean_object*, lean_object*);
lean_object* l_Lake_mkExceptionMessage(lean_object*, lean_object*);
extern lean_object* l_Lean_MessageLog_empty;
extern lean_object* l_Lean_diagnostics;
lean_object* lean_usize_to_nat(size_t);
extern lean_object* l_Lean_inheritedTraceOptions;
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_mk_empty_environment(uint32_t, lean_object*);
lean_object* l_Lake_mkMessageNoPos(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* l_Lean_MessageLog_add(lean_object*, lean_object*);
uint8_t l_Lean_MessageLog_hasErrors(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_loadToml(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint32_t x_4; lean_object* x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_uint32_of_nat(x_3);
x_5 = lean_mk_empty_environment(x_4, x_2);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = l_Lake_Toml_toml;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = lean_box(0);
x_13 = lean_box(0);
lean_inc(x_7);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = l_Lean_Data_Trie_empty(lean_box(0));
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l_Lean_Parser_mkParserState(x_16);
lean_inc(x_1);
x_18 = l_Lean_Parser_ParserFn_run(x_10, x_1, x_14, x_15, x_17);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_string_utf8_at_end(x_16, x_20);
lean_dec(x_20);
lean_dec(x_16);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_7);
x_22 = lean_box(0);
x_23 = lean_mk_string_unchecked("", 0, 0);
x_24 = lean_mk_string_unchecked("end of input", 12, 12);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lake_mkParserErrorMessage(x_1, x_18, x_27);
lean_dec(x_18);
x_29 = l_Lean_MessageLog_empty;
x_30 = l_Lean_MessageLog_add(x_28, x_29);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_30);
return x_5;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint64_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; uint8_t x_128; lean_object* x_130; uint8_t x_131; 
lean_free_object(x_5);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_mk_string_unchecked("_uniq", 5, 5);
x_34 = l_Lean_Name_mkStr1(x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_31);
x_36 = lean_uint64_of_nat(x_3);
x_37 = lean_unsigned_to_nat(5u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_to_nat(x_38);
x_40 = lean_nat_pow(x_32, x_39);
lean_dec(x_39);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_42 = lean_usize_to_nat(x_41);
x_43 = lean_mk_empty_array_with_capacity(x_42);
lean_dec(x_42);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
lean_inc(x_43);
x_45 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
lean_ctor_set(x_45, 2, x_3);
lean_ctor_set(x_45, 3, x_3);
lean_ctor_set_usize(x_45, 4, x_38);
x_46 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set_uint64(x_46, sizeof(void*)*1, x_36);
x_47 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_47);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
lean_inc(x_48);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_48);
lean_inc(x_43);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_43);
lean_inc(x_43);
x_51 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_3);
lean_ctor_set(x_51, 3, x_3);
lean_ctor_set_usize(x_51, 4, x_38);
x_52 = lean_box(0);
lean_inc(x_51);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_53, 2, x_52);
lean_inc(x_47);
x_54 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_54, 0, x_47);
x_55 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_55, 0, x_47);
lean_inc(x_43);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_43);
x_57 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_43);
lean_ctor_set(x_57, 2, x_3);
lean_ctor_set(x_57, 3, x_3);
lean_ctor_set_usize(x_57, 4, x_38);
x_58 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_58, 0, x_54);
lean_ctor_set(x_58, 1, x_55);
lean_ctor_set(x_58, 2, x_57);
lean_ctor_set_uint8(x_58, sizeof(void*)*3, x_21);
x_59 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_49);
x_60 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_60, 0, x_7);
lean_ctor_set(x_60, 1, x_32);
lean_ctor_set(x_60, 2, x_35);
lean_ctor_set(x_60, 3, x_46);
lean_ctor_set(x_60, 4, x_49);
lean_ctor_set(x_60, 5, x_53);
lean_ctor_set(x_60, 6, x_58);
lean_ctor_set(x_60, 7, x_59);
x_61 = lean_st_mk_ref(x_60, x_8);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = l_Lean_inheritedTraceOptions;
x_65 = lean_st_ref_get(x_64, x_63);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
lean_dec(x_65);
x_68 = lean_st_ref_get(x_62, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_18, 0);
lean_inc(x_71);
lean_dec(x_18);
x_72 = l_Lean_Parser_SyntaxStack_back(x_71);
lean_dec(x_71);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 2);
lean_inc(x_74);
x_75 = lean_box(0);
x_76 = l_Lean_Core_getMaxHeartbeats(x_11);
x_77 = lean_box(0);
x_78 = lean_box(0);
x_79 = l_Lean_diagnostics;
x_80 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_79);
x_130 = lean_ctor_get(x_69, 0);
lean_inc(x_130);
lean_dec(x_69);
x_131 = l_Lean_Kernel_isDiagnosticsEnabled(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
if (x_80 == 0)
{
x_128 = x_21;
goto block_129;
}
else
{
goto block_127;
}
}
else
{
if (x_80 == 0)
{
goto block_127;
}
else
{
x_128 = x_21;
goto block_129;
}
}
block_112:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_83 = l_Lean_maxRecDepth;
x_84 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_11, x_83);
x_85 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_85, 0, x_73);
lean_ctor_set(x_85, 1, x_74);
lean_ctor_set(x_85, 2, x_11);
lean_ctor_set(x_85, 3, x_3);
lean_ctor_set(x_85, 4, x_84);
lean_ctor_set(x_85, 5, x_75);
lean_ctor_set(x_85, 6, x_12);
lean_ctor_set(x_85, 7, x_13);
lean_ctor_set(x_85, 8, x_3);
lean_ctor_set(x_85, 9, x_76);
lean_ctor_set(x_85, 10, x_31);
lean_ctor_set(x_85, 11, x_78);
lean_ctor_set(x_85, 12, x_66);
lean_ctor_set_uint8(x_85, sizeof(void*)*13, x_80);
x_86 = lean_unbox(x_77);
lean_ctor_set_uint8(x_85, sizeof(void*)*13 + 1, x_86);
x_87 = l_Lake_Toml_elabToml(x_72, x_85, x_81, x_82);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; 
lean_dec(x_1);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_ref_get(x_62, x_89);
lean_dec(x_62);
x_91 = !lean_is_exclusive(x_90);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_92 = lean_ctor_get(x_90, 0);
x_93 = lean_ctor_get(x_92, 5);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_MessageLog_hasErrors(x_93);
if (x_94 == 0)
{
lean_dec(x_93);
lean_ctor_set(x_90, 0, x_88);
return x_90;
}
else
{
lean_dec(x_88);
lean_ctor_set_tag(x_90, 1);
lean_ctor_set(x_90, 0, x_93);
return x_90;
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_95 = lean_ctor_get(x_90, 0);
x_96 = lean_ctor_get(x_90, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_90);
x_97 = lean_ctor_get(x_95, 5);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_MessageLog_hasErrors(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_97);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_88);
lean_ctor_set(x_99, 1, x_96);
return x_99;
}
else
{
lean_object* x_100; 
lean_dec(x_88);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_97);
lean_ctor_set(x_100, 1, x_96);
return x_100;
}
}
}
else
{
uint8_t x_101; 
lean_dec(x_62);
x_101 = !lean_is_exclusive(x_87);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_87, 0);
x_103 = l_Lake_mkExceptionMessage(x_1, x_102);
x_104 = l_Lean_MessageLog_empty;
x_105 = l_Lean_MessageLog_add(x_103, x_104);
lean_ctor_set(x_87, 0, x_105);
return x_87;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_87, 0);
x_107 = lean_ctor_get(x_87, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_87);
x_108 = l_Lake_mkExceptionMessage(x_1, x_106);
x_109 = l_Lean_MessageLog_empty;
x_110 = l_Lean_MessageLog_add(x_108, x_109);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
}
}
block_127:
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_113 = lean_st_ref_take(x_62, x_70);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = l_Lean_Kernel_enableDiag(x_116, x_80);
x_118 = lean_ctor_get(x_114, 1);
lean_inc(x_118);
x_119 = lean_ctor_get(x_114, 2);
lean_inc(x_119);
x_120 = lean_ctor_get(x_114, 3);
lean_inc(x_120);
x_121 = lean_ctor_get(x_114, 5);
lean_inc(x_121);
x_122 = lean_ctor_get(x_114, 6);
lean_inc(x_122);
x_123 = lean_ctor_get(x_114, 7);
lean_inc(x_123);
lean_dec(x_114);
x_124 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_124, 0, x_117);
lean_ctor_set(x_124, 1, x_118);
lean_ctor_set(x_124, 2, x_119);
lean_ctor_set(x_124, 3, x_120);
lean_ctor_set(x_124, 4, x_49);
lean_ctor_set(x_124, 5, x_121);
lean_ctor_set(x_124, 6, x_122);
lean_ctor_set(x_124, 7, x_123);
x_125 = lean_st_ref_set(x_62, x_124, x_115);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
lean_inc(x_62);
x_81 = x_62;
x_82 = x_126;
goto block_112;
}
block_129:
{
if (x_128 == 0)
{
goto block_127;
}
else
{
lean_dec(x_49);
lean_inc(x_62);
x_81 = x_62;
x_82 = x_70;
goto block_112;
}
}
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_16);
lean_dec(x_7);
x_132 = lean_ctor_get(x_19, 0);
lean_inc(x_132);
lean_dec(x_19);
x_133 = l_Lake_mkParserErrorMessage(x_1, x_18, x_132);
lean_dec(x_18);
x_134 = l_Lean_MessageLog_empty;
x_135 = l_Lean_MessageLog_add(x_133, x_134);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_135);
return x_5;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_136 = lean_ctor_get(x_5, 0);
x_137 = lean_ctor_get(x_5, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_5);
x_138 = l_Lake_Toml_toml;
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
x_140 = lean_box(0);
x_141 = lean_box(0);
x_142 = lean_box(0);
lean_inc(x_136);
x_143 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_143, 0, x_136);
lean_ctor_set(x_143, 1, x_140);
lean_ctor_set(x_143, 2, x_141);
lean_ctor_set(x_143, 3, x_142);
x_144 = l_Lean_Data_Trie_empty(lean_box(0));
x_145 = lean_ctor_get(x_1, 0);
lean_inc(x_145);
x_146 = l_Lean_Parser_mkParserState(x_145);
lean_inc(x_1);
x_147 = l_Lean_Parser_ParserFn_run(x_139, x_1, x_143, x_144, x_146);
x_148 = lean_ctor_get(x_147, 4);
lean_inc(x_148);
if (lean_obj_tag(x_148) == 0)
{
lean_object* x_149; uint8_t x_150; 
x_149 = lean_ctor_get(x_147, 2);
lean_inc(x_149);
x_150 = lean_string_utf8_at_end(x_145, x_149);
lean_dec(x_149);
lean_dec(x_145);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_136);
x_151 = lean_box(0);
x_152 = lean_mk_string_unchecked("", 0, 0);
x_153 = lean_mk_string_unchecked("end of input", 12, 12);
x_154 = lean_box(0);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_156, 0, x_151);
lean_ctor_set(x_156, 1, x_152);
lean_ctor_set(x_156, 2, x_155);
x_157 = l_Lake_mkParserErrorMessage(x_1, x_147, x_156);
lean_dec(x_147);
x_158 = l_Lean_MessageLog_empty;
x_159 = l_Lean_MessageLog_add(x_157, x_158);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_137);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; uint64_t x_166; lean_object* x_167; size_t x_168; lean_object* x_169; lean_object* x_170; size_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; uint8_t x_251; lean_object* x_253; uint8_t x_254; 
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_unsigned_to_nat(2u);
x_163 = lean_mk_string_unchecked("_uniq", 5, 5);
x_164 = l_Lean_Name_mkStr1(x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_161);
x_166 = lean_uint64_of_nat(x_3);
x_167 = lean_unsigned_to_nat(5u);
x_168 = lean_usize_of_nat(x_167);
x_169 = lean_usize_to_nat(x_168);
x_170 = lean_nat_pow(x_162, x_169);
lean_dec(x_169);
x_171 = lean_usize_of_nat(x_170);
lean_dec(x_170);
x_172 = lean_usize_to_nat(x_171);
x_173 = lean_mk_empty_array_with_capacity(x_172);
lean_dec(x_172);
lean_inc(x_173);
x_174 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_174, 0, x_173);
lean_inc(x_173);
x_175 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_173);
lean_ctor_set(x_175, 2, x_3);
lean_ctor_set(x_175, 3, x_3);
lean_ctor_set_usize(x_175, 4, x_168);
x_176 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set_uint64(x_176, sizeof(void*)*1, x_166);
x_177 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_177);
x_178 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_inc(x_178);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_178);
lean_inc(x_173);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_173);
lean_inc(x_173);
x_181 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_173);
lean_ctor_set(x_181, 2, x_3);
lean_ctor_set(x_181, 3, x_3);
lean_ctor_set_usize(x_181, 4, x_168);
x_182 = lean_box(0);
lean_inc(x_181);
x_183 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_181);
lean_ctor_set(x_183, 2, x_182);
lean_inc(x_177);
x_184 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_184, 0, x_177);
x_185 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_185, 0, x_177);
lean_inc(x_173);
x_186 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_186, 0, x_173);
x_187 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_187, 0, x_186);
lean_ctor_set(x_187, 1, x_173);
lean_ctor_set(x_187, 2, x_3);
lean_ctor_set(x_187, 3, x_3);
lean_ctor_set_usize(x_187, 4, x_168);
x_188 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_188, 0, x_184);
lean_ctor_set(x_188, 1, x_185);
lean_ctor_set(x_188, 2, x_187);
lean_ctor_set_uint8(x_188, sizeof(void*)*3, x_150);
x_189 = lean_mk_empty_array_with_capacity(x_3);
lean_inc(x_179);
x_190 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_190, 0, x_136);
lean_ctor_set(x_190, 1, x_162);
lean_ctor_set(x_190, 2, x_165);
lean_ctor_set(x_190, 3, x_176);
lean_ctor_set(x_190, 4, x_179);
lean_ctor_set(x_190, 5, x_183);
lean_ctor_set(x_190, 6, x_188);
lean_ctor_set(x_190, 7, x_189);
x_191 = lean_st_mk_ref(x_190, x_137);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = l_Lean_inheritedTraceOptions;
x_195 = lean_st_ref_get(x_194, x_193);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_st_ref_get(x_192, x_197);
x_199 = lean_ctor_get(x_198, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_198, 1);
lean_inc(x_200);
lean_dec(x_198);
x_201 = lean_ctor_get(x_147, 0);
lean_inc(x_201);
lean_dec(x_147);
x_202 = l_Lean_Parser_SyntaxStack_back(x_201);
lean_dec(x_201);
x_203 = lean_ctor_get(x_1, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_1, 2);
lean_inc(x_204);
x_205 = lean_box(0);
x_206 = l_Lean_Core_getMaxHeartbeats(x_140);
x_207 = lean_box(0);
x_208 = lean_box(0);
x_209 = l_Lean_diagnostics;
x_210 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_140, x_209);
x_253 = lean_ctor_get(x_199, 0);
lean_inc(x_253);
lean_dec(x_199);
x_254 = l_Lean_Kernel_isDiagnosticsEnabled(x_253);
lean_dec(x_253);
if (x_254 == 0)
{
if (x_210 == 0)
{
x_251 = x_150;
goto block_252;
}
else
{
goto block_250;
}
}
else
{
if (x_210 == 0)
{
goto block_250;
}
else
{
x_251 = x_150;
goto block_252;
}
}
block_235:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; 
x_213 = l_Lean_maxRecDepth;
x_214 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_140, x_213);
x_215 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_215, 0, x_203);
lean_ctor_set(x_215, 1, x_204);
lean_ctor_set(x_215, 2, x_140);
lean_ctor_set(x_215, 3, x_3);
lean_ctor_set(x_215, 4, x_214);
lean_ctor_set(x_215, 5, x_205);
lean_ctor_set(x_215, 6, x_141);
lean_ctor_set(x_215, 7, x_142);
lean_ctor_set(x_215, 8, x_3);
lean_ctor_set(x_215, 9, x_206);
lean_ctor_set(x_215, 10, x_161);
lean_ctor_set(x_215, 11, x_208);
lean_ctor_set(x_215, 12, x_196);
lean_ctor_set_uint8(x_215, sizeof(void*)*13, x_210);
x_216 = lean_unbox(x_207);
lean_ctor_set_uint8(x_215, sizeof(void*)*13 + 1, x_216);
x_217 = l_Lake_Toml_elabToml(x_202, x_215, x_211, x_212);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
lean_dec(x_1);
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_st_ref_get(x_192, x_219);
lean_dec(x_192);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_221, 5);
lean_inc(x_224);
lean_dec(x_221);
x_225 = l_Lean_MessageLog_hasErrors(x_224);
if (x_225 == 0)
{
lean_object* x_226; 
lean_dec(x_224);
if (lean_is_scalar(x_223)) {
 x_226 = lean_alloc_ctor(0, 2, 0);
} else {
 x_226 = x_223;
}
lean_ctor_set(x_226, 0, x_218);
lean_ctor_set(x_226, 1, x_222);
return x_226;
}
else
{
lean_object* x_227; 
lean_dec(x_218);
if (lean_is_scalar(x_223)) {
 x_227 = lean_alloc_ctor(1, 2, 0);
} else {
 x_227 = x_223;
 lean_ctor_set_tag(x_227, 1);
}
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_222);
return x_227;
}
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_dec(x_192);
x_228 = lean_ctor_get(x_217, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_217, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_217)) {
 lean_ctor_release(x_217, 0);
 lean_ctor_release(x_217, 1);
 x_230 = x_217;
} else {
 lean_dec_ref(x_217);
 x_230 = lean_box(0);
}
x_231 = l_Lake_mkExceptionMessage(x_1, x_228);
x_232 = l_Lean_MessageLog_empty;
x_233 = l_Lean_MessageLog_add(x_231, x_232);
if (lean_is_scalar(x_230)) {
 x_234 = lean_alloc_ctor(1, 2, 0);
} else {
 x_234 = x_230;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_229);
return x_234;
}
}
block_250:
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_236 = lean_st_ref_take(x_192, x_200);
x_237 = lean_ctor_get(x_236, 0);
lean_inc(x_237);
x_238 = lean_ctor_get(x_236, 1);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = l_Lean_Kernel_enableDiag(x_239, x_210);
x_241 = lean_ctor_get(x_237, 1);
lean_inc(x_241);
x_242 = lean_ctor_get(x_237, 2);
lean_inc(x_242);
x_243 = lean_ctor_get(x_237, 3);
lean_inc(x_243);
x_244 = lean_ctor_get(x_237, 5);
lean_inc(x_244);
x_245 = lean_ctor_get(x_237, 6);
lean_inc(x_245);
x_246 = lean_ctor_get(x_237, 7);
lean_inc(x_246);
lean_dec(x_237);
x_247 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_247, 0, x_240);
lean_ctor_set(x_247, 1, x_241);
lean_ctor_set(x_247, 2, x_242);
lean_ctor_set(x_247, 3, x_243);
lean_ctor_set(x_247, 4, x_179);
lean_ctor_set(x_247, 5, x_244);
lean_ctor_set(x_247, 6, x_245);
lean_ctor_set(x_247, 7, x_246);
x_248 = lean_st_ref_set(x_192, x_247, x_238);
x_249 = lean_ctor_get(x_248, 1);
lean_inc(x_249);
lean_dec(x_248);
lean_inc(x_192);
x_211 = x_192;
x_212 = x_249;
goto block_235;
}
block_252:
{
if (x_251 == 0)
{
goto block_250;
}
else
{
lean_dec(x_179);
lean_inc(x_192);
x_211 = x_192;
x_212 = x_200;
goto block_235;
}
}
}
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_145);
lean_dec(x_136);
x_255 = lean_ctor_get(x_148, 0);
lean_inc(x_255);
lean_dec(x_148);
x_256 = l_Lake_mkParserErrorMessage(x_1, x_147, x_255);
lean_dec(x_147);
x_257 = l_Lean_MessageLog_empty;
x_258 = l_Lean_MessageLog_add(x_256, x_257);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_137);
return x_259;
}
}
}
else
{
uint8_t x_260; 
x_260 = !lean_is_exclusive(x_5);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_261 = lean_ctor_get(x_5, 0);
x_262 = lean_mk_string_unchecked("failed to initialize TOML environment: ", 39, 39);
x_263 = l_Lean_stringToMessageData(x_262);
lean_dec(x_262);
x_264 = lean_io_error_to_string(x_261);
x_265 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_265, 0, x_264);
x_266 = l_Lean_MessageData_ofFormat(x_265);
x_267 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_267, 0, x_263);
lean_ctor_set(x_267, 1, x_266);
x_268 = lean_mk_string_unchecked("", 0, 0);
x_269 = l_Lean_stringToMessageData(x_268);
lean_dec(x_268);
x_270 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_box(2);
x_272 = lean_unbox(x_271);
x_273 = l_Lake_mkMessageNoPos(x_1, x_270, x_272);
x_274 = l_Lean_MessageLog_empty;
x_275 = l_Lean_MessageLog_add(x_273, x_274);
lean_ctor_set(x_5, 0, x_275);
return x_5;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_276 = lean_ctor_get(x_5, 0);
x_277 = lean_ctor_get(x_5, 1);
lean_inc(x_277);
lean_inc(x_276);
lean_dec(x_5);
x_278 = lean_mk_string_unchecked("failed to initialize TOML environment: ", 39, 39);
x_279 = l_Lean_stringToMessageData(x_278);
lean_dec(x_278);
x_280 = lean_io_error_to_string(x_276);
x_281 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_281, 0, x_280);
x_282 = l_Lean_MessageData_ofFormat(x_281);
x_283 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_283, 0, x_279);
lean_ctor_set(x_283, 1, x_282);
x_284 = lean_mk_string_unchecked("", 0, 0);
x_285 = l_Lean_stringToMessageData(x_284);
lean_dec(x_284);
x_286 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_286, 0, x_283);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_box(2);
x_288 = lean_unbox(x_287);
x_289 = l_Lake_mkMessageNoPos(x_1, x_286, x_288);
x_290 = l_Lean_MessageLog_empty;
x_291 = l_Lean_MessageLog_add(x_289, x_290);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_277);
return x_292;
}
}
}
}
lean_object* initialize_Lake_Toml_Elab(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Util_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Load(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_Elab(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Util_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
