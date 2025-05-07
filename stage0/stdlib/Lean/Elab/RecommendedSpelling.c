// Lean compiler output
// Module: Lean.Elab.RecommendedSpelling
// Imports: Lean.Parser.Term.Doc Lean.Parser.Command Lean.Elab.Command
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
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getString(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_Command_commandElabAttribute;
lean_object* l_Lean_instInhabitedPersistentEnvExtensionState___redArg(lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_Doc_addRecommendedSpelling(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getDocString(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_Doc_recommendedSpellingExt;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Command_liftTermElabM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_elabRecommendedSpelling(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_mk_string_unchecked("ident", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
lean_inc(x_6);
x_9 = l_Lean_Syntax_isOfKind(x_6, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_3);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_11 = lean_box(0);
x_12 = lean_array_uset(x_3, x_2, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_16 = lean_array_uset(x_12, x_2, x_6);
x_2 = x_15;
x_3 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_box(0);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_realizeGlobalConstNoOverloadWithInfo(x_9, x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_12);
x_2 = x_18;
x_3 = x_19;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_21 = !lean_is_exclusive(x_11);
if (x_21 == 0)
{
return x_11;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_11, 0);
x_23 = lean_ctor_get(x_11, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_11);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___redArg(x_1, x_2, x_3, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(4u);
x_13 = lean_mk_string_unchecked("str", 3, 3);
x_14 = lean_usize_dec_eq(x_3, x_4);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_5, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_5);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_5, 0);
lean_dec(x_18);
x_19 = l_Lean_Syntax_getArg(x_1, x_12);
x_20 = l_Lean_Name_mkStr1(x_13);
x_21 = l_Lean_Syntax_isOfKind(x_19, x_20);
lean_dec(x_20);
x_22 = lean_box(x_21);
lean_ctor_set(x_5, 0, x_22);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_ctor_get(x_5, 1);
lean_inc(x_23);
lean_dec(x_5);
x_24 = l_Lean_Syntax_getArg(x_1, x_12);
x_25 = l_Lean_Name_mkStr1(x_13);
x_26 = l_Lean_Syntax_isOfKind(x_24, x_25);
lean_dec(x_25);
x_27 = lean_box(x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_23);
x_6 = x_28;
goto block_11;
}
}
else
{
uint8_t x_29; 
lean_dec(x_13);
x_29 = !lean_is_exclusive(x_5);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_5, 1);
x_31 = lean_ctor_get(x_5, 0);
lean_dec(x_31);
x_32 = lean_array_uget(x_2, x_3);
x_33 = lean_array_push(x_30, x_32);
x_34 = lean_box(x_14);
lean_ctor_set(x_5, 1, x_33);
lean_ctor_set(x_5, 0, x_34);
x_6 = x_5;
goto block_11;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = lean_array_uget(x_2, x_3);
x_37 = lean_array_push(x_35, x_36);
x_38 = lean_box(x_14);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_37);
x_6 = x_39;
goto block_11;
}
}
}
else
{
lean_dec(x_13);
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_elabRecommendedSpelling(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = lean_mk_string_unchecked("Lean", 4, 4);
x_106 = lean_mk_string_unchecked("Parser", 6, 6);
x_107 = lean_mk_string_unchecked("Command", 7, 7);
x_108 = lean_mk_string_unchecked("recommended_spelling", 20, 20);
lean_inc(x_107);
lean_inc(x_106);
lean_inc(x_105);
x_109 = l_Lean_Name_mkStr4(x_105, x_106, x_107, x_108);
lean_inc(x_1);
x_110 = l_Lean_Syntax_isOfKind(x_1, x_109);
lean_dec(x_109);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_111 = lean_mk_string_unchecked("Malformed recommended spelling command", 38, 38);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
x_113 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_112, x_2, x_3, x_4);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; uint8_t x_116; 
x_114 = lean_unsigned_to_nat(0u);
x_115 = l_Lean_Syntax_getArg(x_1, x_114);
x_116 = l_Lean_Syntax_isNone(x_115);
if (x_116 == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_unsigned_to_nat(1u);
lean_inc(x_115);
x_118 = l_Lean_Syntax_matchesNull(x_115, x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_115);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_119 = lean_mk_string_unchecked("Malformed recommended spelling command", 38, 38);
x_120 = l_Lean_stringToMessageData(x_119);
lean_dec(x_119);
x_121 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_120, x_2, x_3, x_4);
return x_121;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_122 = l_Lean_Syntax_getArg(x_115, x_114);
lean_dec(x_115);
x_123 = lean_mk_string_unchecked("docComment", 10, 10);
x_124 = l_Lean_Name_mkStr4(x_105, x_106, x_107, x_123);
lean_inc(x_122);
x_125 = l_Lean_Syntax_isOfKind(x_122, x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_122);
lean_dec(x_1);
x_126 = lean_mk_string_unchecked("Malformed recommended spelling command", 38, 38);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_127, x_2, x_3, x_4);
return x_128;
}
else
{
lean_object* x_129; 
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_122);
x_72 = x_129;
x_73 = x_2;
x_74 = x_3;
x_75 = x_4;
goto block_104;
}
}
}
else
{
lean_object* x_130; 
lean_dec(x_115);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
x_130 = lean_box(0);
x_72 = x_130;
x_73 = x_2;
x_74 = x_3;
x_75 = x_4;
goto block_104;
}
}
block_33:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_11 = lean_st_ref_take(x_5, x_8);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_9);
lean_ctor_set(x_14, 2, x_10);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
x_16 = l_Lean_Parser_Term_Doc_addRecommendedSpelling(x_15, x_14, x_6);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_12, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_12, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_12, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_12, 5);
lean_inc(x_21);
x_22 = lean_ctor_get(x_12, 6);
lean_inc(x_22);
x_23 = lean_ctor_get(x_12, 7);
lean_inc(x_23);
x_24 = lean_ctor_get(x_12, 8);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_18);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
x_26 = lean_st_ref_set(x_5, x_25, x_13);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
block_71:
{
size_t x_41; lean_object* x_42; size_t x_43; lean_object* x_44; 
x_41 = lean_array_size(x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_usize_of_nat(x_42);
x_44 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0(x_41, x_43, x_40);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_1);
x_45 = lean_mk_string_unchecked("Malformed recommended spelling command", 38, 38);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_46, x_35, x_36, x_38);
return x_47;
}
else
{
lean_object* x_48; size_t x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_44, 0);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_array_size(x_48);
x_50 = lean_box_usize(x_49);
x_51 = lean_box_usize(x_43);
x_52 = lean_alloc_closure((void*)(l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___boxed), 10, 3);
lean_closure_set(x_52, 0, x_50);
lean_closure_set(x_52, 1, x_51);
lean_closure_set(x_52, 2, x_48);
x_53 = l_Lean_Elab_Command_liftTermElabM___redArg(x_52, x_35, x_36, x_38);
lean_dec(x_35);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Lean_Syntax_getArg(x_1, x_39);
x_57 = l_Lean_Syntax_getArg(x_1, x_34);
lean_dec(x_1);
x_58 = l_Lean_TSyntax_getString(x_56);
lean_dec(x_56);
x_59 = l_Lean_TSyntax_getString(x_57);
lean_dec(x_57);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_60; 
x_60 = lean_box(0);
x_5 = x_36;
x_6 = x_54;
x_7 = x_58;
x_8 = x_55;
x_9 = x_59;
x_10 = x_60;
goto block_33;
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_37);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_ctor_get(x_37, 0);
x_63 = l_Lean_TSyntax_getDocString(x_62);
lean_dec(x_62);
lean_ctor_set(x_37, 0, x_63);
x_5 = x_36;
x_6 = x_54;
x_7 = x_58;
x_8 = x_55;
x_9 = x_59;
x_10 = x_37;
goto block_33;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_37, 0);
lean_inc(x_64);
lean_dec(x_37);
x_65 = l_Lean_TSyntax_getDocString(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_5 = x_36;
x_6 = x_54;
x_7 = x_58;
x_8 = x_55;
x_9 = x_59;
x_10 = x_66;
goto block_33;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_37);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_53);
if (x_67 == 0)
{
return x_53;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_53, 0);
x_69 = lean_ctor_get(x_53, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_53);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
block_104:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_unsigned_to_nat(2u);
x_77 = l_Lean_Syntax_getArg(x_1, x_76);
x_78 = lean_mk_string_unchecked("str", 3, 3);
x_79 = l_Lean_Name_mkStr1(x_78);
x_80 = l_Lean_Syntax_isOfKind(x_77, x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_79);
lean_dec(x_72);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("Malformed recommended spelling command", 38, 38);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_82, x_73, x_74, x_75);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_unsigned_to_nat(4u);
x_85 = l_Lean_Syntax_getArg(x_1, x_84);
x_86 = l_Lean_Syntax_isOfKind(x_85, x_79);
lean_dec(x_79);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_72);
lean_dec(x_1);
x_87 = lean_mk_string_unchecked("Malformed recommended spelling command", 38, 38);
x_88 = l_Lean_stringToMessageData(x_87);
lean_dec(x_87);
x_89 = l_Lean_throwError___at_____private_Lean_Elab_Command_0__Lean_Elab_Command_elabCommandUsing_spec__0___redArg(x_88, x_73, x_74, x_75);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_90 = lean_unsigned_to_nat(7u);
x_91 = l_Lean_Syntax_getArg(x_1, x_90);
x_92 = l_Lean_Syntax_getArgs(x_91);
lean_dec(x_91);
x_93 = l_Array_empty(lean_box(0));
x_94 = lean_unsigned_to_nat(0u);
x_95 = lean_array_get_size(x_92);
x_96 = lean_nat_dec_lt(x_94, x_95);
if (x_96 == 0)
{
lean_dec(x_95);
lean_dec(x_92);
x_34 = x_76;
x_35 = x_73;
x_36 = x_74;
x_37 = x_72;
x_38 = x_75;
x_39 = x_84;
x_40 = x_93;
goto block_71;
}
else
{
uint8_t x_97; 
x_97 = lean_nat_dec_le(x_95, x_95);
if (x_97 == 0)
{
lean_dec(x_95);
lean_dec(x_92);
x_34 = x_76;
x_35 = x_73;
x_36 = x_74;
x_37 = x_72;
x_38 = x_75;
x_39 = x_84;
x_40 = x_93;
goto block_71;
}
else
{
lean_object* x_98; lean_object* x_99; size_t x_100; size_t x_101; lean_object* x_102; lean_object* x_103; 
x_98 = lean_box(x_86);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_93);
x_100 = lean_usize_of_nat(x_94);
x_101 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_102 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2(x_1, x_92, x_100, x_101, x_99);
lean_dec(x_92);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_34 = x_76;
x_35 = x_73;
x_36 = x_74;
x_37 = x_72;
x_38 = x_75;
x_39 = x_84;
x_40 = x_103;
goto block_71;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__1(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_elabRecommendedSpelling_spec__2(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_Term_Doc_elabRecommendedSpelling(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = l_Lean_Elab_Command_commandElabAttribute;
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Parser", 6, 6);
x_5 = lean_mk_string_unchecked("Command", 7, 7);
x_6 = lean_mk_string_unchecked("recommended_spelling", 20, 20);
lean_inc(x_3);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("Term", 4, 4);
x_10 = lean_mk_string_unchecked("Doc", 3, 3);
x_11 = lean_mk_string_unchecked("elabRecommendedSpelling", 23, 23);
x_12 = l_Lean_Name_mkStr5(x_3, x_8, x_9, x_10, x_11);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Term_Doc_elabRecommendedSpelling___boxed), 4, 0);
x_14 = l_Lean_KeyedDeclsAttribute_addBuiltin___redArg(x_2, x_7, x_12, x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Array_append(lean_box(0), x_4, x_6);
lean_dec(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_st_ref_get(x_1, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = l_Array_instInhabited(lean_box(0));
lean_inc(x_9);
x_10 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_9);
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
lean_dec(x_4);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = l_Lean_Parser_Term_Doc_recommendedSpellingExt;
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
x_16 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_10, x_14, x_11, x_15);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_ctor_get(x_13, 4);
lean_inc(x_18);
x_19 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_9, x_13, x_12, x_15);
x_20 = lean_apply_1(x_18, x_19);
x_21 = lean_array_push(x_17, x_20);
x_22 = l_Array_empty(lean_box(0));
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_21);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_21);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_23);
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(x_21, x_27, x_28, x_22);
lean_dec(x_21);
lean_ctor_set(x_6, 0, x_29);
return x_6;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_30 = lean_ctor_get(x_6, 0);
x_31 = lean_ctor_get(x_6, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_6);
x_32 = l_Array_instInhabited(lean_box(0));
lean_inc(x_32);
x_33 = l_Lean_instInhabitedPersistentEnvExtensionState___redArg(x_32);
x_34 = lean_ctor_get(x_4, 0);
lean_inc(x_34);
lean_dec(x_4);
x_35 = lean_ctor_get(x_30, 0);
lean_inc(x_35);
lean_dec(x_30);
x_36 = l_Lean_Parser_Term_Doc_recommendedSpellingExt;
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_37, sizeof(void*)*3);
x_39 = l___private_Lean_Environment_0__Lean_EnvExtension_getStateUnsafe___redArg(x_33, x_37, x_34, x_38);
lean_dec(x_37);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_36, 4);
lean_inc(x_41);
x_42 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_32, x_36, x_35, x_38);
x_43 = lean_apply_1(x_41, x_42);
x_44 = lean_array_push(x_40, x_43);
x_45 = l_Array_empty(lean_box(0));
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_44);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_object* x_49; 
lean_dec(x_47);
lean_dec(x_44);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_45);
lean_ctor_set(x_49, 1, x_31);
return x_49;
}
else
{
uint8_t x_50; 
x_50 = lean_nat_dec_le(x_47, x_47);
if (x_50 == 0)
{
lean_object* x_51; 
lean_dec(x_47);
lean_dec(x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_45);
lean_ctor_set(x_51, 1, x_31);
return x_51;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_usize_of_nat(x_46);
x_53 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_54 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(x_44, x_52, x_53, x_45);
lean_dec(x_44);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_31);
return x_55;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Term_Doc_allRecommendedSpellings_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Term_Doc_allRecommendedSpellings___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Term_Doc_allRecommendedSpellings___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Term_Doc_allRecommendedSpellings(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
lean_object* initialize_Lean_Parser_Term_Doc(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Command(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Command(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_RecommendedSpelling(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term_Doc(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Command(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l___regBuiltin_Lean_Elab_Term_Doc_elabRecommendedSpelling__1(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
