// Lean compiler output
// Module: Lake.DSL.Syntax
// Imports: Lake.DSL.DeclUtil Lean.Parser.Term
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
LEAN_EXPORT lean_object* l_Lake_DSL_depSpec;
LEAN_EXPORT lean_object* l_Lake_DSL_fromClause;
LEAN_EXPORT lean_object* l_Lake_DSL_runIO;
LEAN_EXPORT lean_object* l_Lake_DSL_leanExeCommand;
LEAN_EXPORT lean_object* l_Lake_DSL_requireDecl;
extern lean_object* l_Lake_DSL_simpleBinder;
extern lean_object* l_Lake_DSL_optConfig;
LEAN_EXPORT lean_object* l_Lake_DSL_verSpec;
extern lean_object* l_Lake_DSL_identOrStr;
LEAN_EXPORT lean_object* l_Lake_DSL_packageCommand;
LEAN_EXPORT lean_object* l_Lake_DSL_cmdDo;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_packageTargetLit;
LEAN_EXPORT lean_object* l_Lake_DSL_getConfig;
LEAN_EXPORT lean_object* l_Lake_DSL_packageFacetDecl;
LEAN_EXPORT lean_object* l_Lake_DSL_postUpdateDecl;
LEAN_EXPORT lean_object* l_Lake_DSL_term_x60_x40_______x2f________;
LEAN_EXPORT lean_object* l_Lake_DSL_facetSuffix;
LEAN_EXPORT lean_object* l_Lake_DSL_scriptDeclSpec;
LEAN_EXPORT lean_object* l_Lake_DSL_inputDirCommand;
LEAN_EXPORT lean_object* l_Lake_verLit;
LEAN_EXPORT lean_object* l_Lake_DSL_fromGit;
LEAN_EXPORT lean_object* l_Lake_DSL_externLibCommand;
LEAN_EXPORT lean_object* l_Lake_DSL_inputFileCommand;
LEAN_EXPORT lean_object* l_Lake_DSL_fromSource;
LEAN_EXPORT lean_object* l_Lake_DSL_fromPath;
extern lean_object* l_Lake_DSL_declValDo;
LEAN_EXPORT lean_object* l_Lake_DSL_moduleFacetDecl;
LEAN_EXPORT lean_object* l_Lake_DSL_scriptDecl;
LEAN_EXPORT lean_object* l_Lake_DSL_leanLibCommand;
LEAN_EXPORT lean_object* l_Lake_DSL_libraryFacetDecl;
LEAN_EXPORT lean_object* l_Lake_DSL_externLibDeclSpec;
LEAN_EXPORT lean_object* l_Lake_DSL_targetCommand;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_depName;
LEAN_EXPORT lean_object* l_Lake_DSL_term_x60_x2b______;
LEAN_EXPORT lean_object* l_Lake_DSL_buildDeclSig;
LEAN_EXPORT lean_object* l_Lake_DSL_metaIf;
LEAN_EXPORT lean_object* l_Lake_DSL_dirConst;
LEAN_EXPORT lean_object* l_Lake_DSL_withClause;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_DSL_verClause;
static lean_object* _init_l_Lake_DSL_dirConst() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("dirConst", 8, 8);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_mk_string_unchecked("__dir__", 7, 7);
x_7 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_5);
lean_ctor_set(x_8, 2, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_DSL_getConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("getConfig", 9, 9);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("get_config\? ", 12, 12);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("ident", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lake_DSL_packageCommand() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("packageCommand", 14, 14);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("package ", 8, 8);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_identOrStr;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lake_DSL_optConfig;
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_DSL_postUpdateDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("postUpdateDecl", 14, 14);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
lean_inc(x_15);
lean_inc(x_14);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("post_update ", 12, 12);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = l_Lake_DSL_simpleBinder;
lean_inc(x_7);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_9);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_7);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_24);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_mk_string_unchecked("orelse", 6, 6);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_mk_string_unchecked("Command", 7, 7);
x_35 = lean_mk_string_unchecked("declValSimple", 13, 13);
x_36 = l_Lean_Name_mkStr4(x_14, x_15, x_34, x_35);
x_37 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = l_Lake_DSL_declValDo;
x_39 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_39, 0, x_33);
lean_ctor_set(x_39, 1, x_37);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_40, 0, x_7);
lean_ctor_set(x_40, 1, x_31);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_41, 0, x_4);
lean_ctor_set(x_41, 1, x_5);
lean_ctor_set(x_41, 2, x_40);
return x_41;
}
}
static lean_object* _init_l_Lake_DSL_fromPath() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_mk_string_unchecked("fromPath", 8, 8);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("term", 4, 4);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_8, 0, x_6);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_4);
lean_ctor_set(x_9, 2, x_8);
return x_9;
}
}
static lean_object* _init_l_Lake_DSL_fromGit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("fromGit", 7, 7);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("git ", 4, 4);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(1024u);
lean_inc(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_14);
lean_inc(x_6);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_mk_string_unchecked("optional", 8, 8);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_mk_string_unchecked("@", 1, 1);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_6);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_14);
lean_inc(x_17);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
lean_inc(x_6);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_15);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("/", 1, 1);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_6);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_17);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_6);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_DSL_fromSource() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("fromSource", 10, 10);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("orelse", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lake_DSL_fromGit;
x_8 = l_Lake_DSL_fromPath;
x_9 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_8);
x_10 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
static lean_object* _init_l_Lake_DSL_fromClause() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("fromClause", 10, 10);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked(" from ", 6, 6);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lake_DSL_fromSource;
x_10 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
static lean_object* _init_l_Lake_DSL_withClause() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("withClause", 10, 10);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked(" with ", 6, 6);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("term", 4, 4);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lake_DSL_verSpec() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("verSpec", 7, 7);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("optional", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("git ", 4, 4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_mk_string_unchecked("term", 4, 4);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_unsigned_to_nat(1024u);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_13);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lake_DSL_verClause() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("verClause", 9, 9);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked(" @ ", 3, 3);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lake_DSL_verSpec;
x_10 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_8);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
static lean_object* _init_l_Lake_DSL_depName() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("depName", 7, 7);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("optional", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("atomic", 6, 6);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("str", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_mk_string_unchecked(" / ", 3, 3);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lake_DSL_identOrStr;
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_18);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_21, 0, x_1);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lake_DSL_depSpec() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("depSpec", 7, 7);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lake_DSL_depName;
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = l_Lake_DSL_verClause;
lean_inc(x_9);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
x_13 = l_Lake_DSL_fromClause;
lean_inc(x_9);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_9);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_6);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_6);
lean_ctor_set(x_15, 1, x_12);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lake_DSL_withClause;
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_9);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_6);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_19, 0, x_1);
lean_ctor_set(x_19, 1, x_4);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lake_DSL_requireDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("requireDecl", 11, 11);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("require ", 8, 8);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_7);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_7);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lake_DSL_depSpec;
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_5);
lean_ctor_set(x_19, 2, x_18);
return x_19;
}
}
static lean_object* _init_l_Lake_DSL_buildDeclSig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_1 = lean_mk_string_unchecked("buildDeclSig", 12, 12);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lake_DSL_identOrStr;
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lake_DSL_simpleBinder;
lean_inc(x_6);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Term", 4, 4);
x_20 = lean_mk_string_unchecked("typeSpec", 8, 8);
lean_inc(x_18);
lean_inc(x_17);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_inc(x_6);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_mk_string_unchecked("Command", 7, 7);
x_25 = lean_mk_string_unchecked("declValSimple", 13, 13);
x_26 = l_Lean_Name_mkStr4(x_17, x_18, x_24, x_25);
x_27 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_27, 0, x_26);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_6);
lean_ctor_set(x_28, 1, x_23);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_4);
lean_ctor_set(x_29, 2, x_28);
return x_29;
}
}
static lean_object* _init_l_Lake_DSL_moduleFacetDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("moduleFacetDecl", 15, 15);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("module_facet ", 13, 13);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_buildDeclSig;
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_DSL_packageFacetDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("packageFacetDecl", 16, 16);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("package_facet ", 14, 14);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_buildDeclSig;
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_DSL_libraryFacetDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("libraryFacetDecl", 16, 16);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("library_facet ", 14, 14);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_buildDeclSig;
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_DSL_targetCommand() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("targetCommand", 13, 13);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("target ", 7, 7);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_buildDeclSig;
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_DSL_leanLibCommand() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("leanLibCommand", 14, 14);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("lean_lib ", 9, 9);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_identOrStr;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lake_DSL_optConfig;
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_DSL_leanExeCommand() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("leanExeCommand", 14, 14);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("lean_exe ", 9, 9);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_identOrStr;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lake_DSL_optConfig;
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_DSL_inputFileCommand() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("inputFileCommand", 16, 16);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("input_file ", 11, 11);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_identOrStr;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lake_DSL_optConfig;
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_DSL_inputDirCommand() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("inputDirCommand", 15, 15);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("input_dir ", 10, 10);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_identOrStr;
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_24);
lean_ctor_set(x_27, 2, x_26);
x_28 = l_Lake_DSL_optConfig;
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_DSL_externLibDeclSpec() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_1 = lean_mk_string_unchecked("externLibDeclSpec", 17, 17);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lake_DSL_identOrStr;
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lake_DSL_simpleBinder;
lean_inc(x_6);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Parser", 6, 6);
x_19 = lean_mk_string_unchecked("Command", 7, 7);
x_20 = lean_mk_string_unchecked("declValSimple", 13, 13);
x_21 = l_Lean_Name_mkStr4(x_17, x_18, x_19, x_20);
x_22 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_16);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_4);
lean_ctor_set(x_24, 2, x_23);
return x_24;
}
}
static lean_object* _init_l_Lake_DSL_externLibCommand() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("externLibCommand", 16, 16);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("extern_lib ", 11, 11);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_externLibDeclSpec;
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_DSL_scriptDeclSpec() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_1 = lean_mk_string_unchecked("scriptDeclSpec", 14, 14);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lake_DSL_identOrStr;
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lake_DSL_simpleBinder;
lean_inc(x_6);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_mk_string_unchecked("orelse", 6, 6);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("Lean", 4, 4);
x_20 = lean_mk_string_unchecked("Parser", 6, 6);
x_21 = lean_mk_string_unchecked("Command", 7, 7);
x_22 = lean_mk_string_unchecked("declValSimple", 13, 13);
x_23 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_22);
x_24 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lake_DSL_declValDo;
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_6);
lean_ctor_set(x_27, 1, x_16);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_4);
lean_ctor_set(x_28, 2, x_27);
return x_28;
}
}
static lean_object* _init_l_Lake_DSL_scriptDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("scriptDecl", 10, 10);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("optional", 8, 8);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("docComment", 10, 10);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Parser", 6, 6);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("attributes", 10, 10);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
x_19 = lean_alloc_ctor(8, 1, 0);
lean_ctor_set(x_19, 0, x_18);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_19);
lean_inc(x_7);
x_21 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_mk_string_unchecked("script ", 7, 7);
x_23 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_23, 0, x_22);
lean_inc(x_7);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 2, x_23);
x_25 = l_Lake_DSL_scriptDeclSpec;
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_5);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lake_verLit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("verLit", 6, 6);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(1024u);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("v!", 2, 2);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("noWs", 4, 4);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("interpolatedStr", 15, 15);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("term", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_4);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lake_DSL_facetSuffix() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("facetSuffix", 11, 11);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("atomic", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked(":", 1, 1);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("noWs", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
lean_inc(x_6);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_10);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("ident", 5, 5);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_6);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_4);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lake_DSL_packageTargetLit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("packageTargetLit", 16, 16);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("optional", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("atomic", 6, 6);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("+", 1, 1);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_mk_string_unchecked("noWs", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_6);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_12);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("ident", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x2b______() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("term`+___", 9, 9);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("`+", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("noWs", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
lean_inc(x_7);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_7);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("many", 4, 4);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lake_DSL_facetSuffix;
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lake_DSL_term_x60_x40_______x2f________() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("term`@___/____", 14, 14);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1024u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("`@", 2, 2);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("optional", 8, 8);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("noWs", 4, 4);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_mk_string_unchecked("ident", 5, 5);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_14);
lean_inc(x_7);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_7);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_11);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_7);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_9);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("atomic", 6, 6);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("/", 1, 1);
x_24 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_14);
lean_inc(x_7);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_7);
lean_ctor_set(x_25, 1, x_14);
lean_ctor_set(x_25, 2, x_24);
lean_inc(x_14);
lean_inc(x_7);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_7);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_26, 2, x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lake_DSL_packageTargetLit;
lean_inc(x_7);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_27);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_11);
lean_ctor_set(x_30, 1, x_29);
lean_inc(x_7);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_7);
lean_ctor_set(x_31, 1, x_20);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_mk_string_unchecked("many", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Lake_DSL_facetSuffix;
lean_inc(x_7);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_7);
lean_ctor_set(x_35, 1, x_14);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_37, 0, x_7);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_38, 0, x_4);
lean_ctor_set(x_38, 1, x_5);
lean_ctor_set(x_38, 2, x_37);
return x_38;
}
}
static lean_object* _init_l_Lake_DSL_cmdDo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("cmdDo", 5, 5);
x_2 = lean_mk_string_unchecked("Lake", 4, 4);
x_3 = lean_mk_string_unchecked("DSL", 3, 3);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("orelse", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("group", 5, 5);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("andthen", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("do", 2, 2);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_mk_string_unchecked("many1Indent", 11, 11);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("command", 7, 7);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
lean_inc(x_18);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_6);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_22, 2, x_18);
x_23 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_4);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lake_DSL_metaIf() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("metaIf", 6, 6);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("meta ", 5, 5);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("if ", 3, 3);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_inc(x_7);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_9);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_7);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_12);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked(" then ", 6, 6);
x_19 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_7);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = l_Lake_DSL_cmdDo;
lean_inc(x_7);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_20);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_mk_string_unchecked("optional", 8, 8);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_mk_string_unchecked(" else ", 6, 6);
x_26 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_inc(x_7);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_7);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_21);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_7);
lean_ctor_set(x_29, 1, x_22);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_4);
lean_ctor_set(x_30, 1, x_5);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lake_DSL_runIO() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
x_2 = lean_mk_string_unchecked("DSL", 3, 3);
x_3 = lean_mk_string_unchecked("runIO", 5, 5);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_unsigned_to_nat(1022u);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_mk_string_unchecked("run_io ", 7, 7);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_mk_string_unchecked("doSeq", 5, 5);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_7);
lean_ctor_set(x_13, 1, x_9);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
lean_object* initialize_Lake_DSL_DeclUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser_Term(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_DSL_Syntax(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_DSL_DeclUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_DSL_dirConst = _init_l_Lake_DSL_dirConst();
lean_mark_persistent(l_Lake_DSL_dirConst);
l_Lake_DSL_getConfig = _init_l_Lake_DSL_getConfig();
lean_mark_persistent(l_Lake_DSL_getConfig);
l_Lake_DSL_packageCommand = _init_l_Lake_DSL_packageCommand();
lean_mark_persistent(l_Lake_DSL_packageCommand);
l_Lake_DSL_postUpdateDecl = _init_l_Lake_DSL_postUpdateDecl();
lean_mark_persistent(l_Lake_DSL_postUpdateDecl);
l_Lake_DSL_fromPath = _init_l_Lake_DSL_fromPath();
lean_mark_persistent(l_Lake_DSL_fromPath);
l_Lake_DSL_fromGit = _init_l_Lake_DSL_fromGit();
lean_mark_persistent(l_Lake_DSL_fromGit);
l_Lake_DSL_fromSource = _init_l_Lake_DSL_fromSource();
lean_mark_persistent(l_Lake_DSL_fromSource);
l_Lake_DSL_fromClause = _init_l_Lake_DSL_fromClause();
lean_mark_persistent(l_Lake_DSL_fromClause);
l_Lake_DSL_withClause = _init_l_Lake_DSL_withClause();
lean_mark_persistent(l_Lake_DSL_withClause);
l_Lake_DSL_verSpec = _init_l_Lake_DSL_verSpec();
lean_mark_persistent(l_Lake_DSL_verSpec);
l_Lake_DSL_verClause = _init_l_Lake_DSL_verClause();
lean_mark_persistent(l_Lake_DSL_verClause);
l_Lake_DSL_depName = _init_l_Lake_DSL_depName();
lean_mark_persistent(l_Lake_DSL_depName);
l_Lake_DSL_depSpec = _init_l_Lake_DSL_depSpec();
lean_mark_persistent(l_Lake_DSL_depSpec);
l_Lake_DSL_requireDecl = _init_l_Lake_DSL_requireDecl();
lean_mark_persistent(l_Lake_DSL_requireDecl);
l_Lake_DSL_buildDeclSig = _init_l_Lake_DSL_buildDeclSig();
lean_mark_persistent(l_Lake_DSL_buildDeclSig);
l_Lake_DSL_moduleFacetDecl = _init_l_Lake_DSL_moduleFacetDecl();
lean_mark_persistent(l_Lake_DSL_moduleFacetDecl);
l_Lake_DSL_packageFacetDecl = _init_l_Lake_DSL_packageFacetDecl();
lean_mark_persistent(l_Lake_DSL_packageFacetDecl);
l_Lake_DSL_libraryFacetDecl = _init_l_Lake_DSL_libraryFacetDecl();
lean_mark_persistent(l_Lake_DSL_libraryFacetDecl);
l_Lake_DSL_targetCommand = _init_l_Lake_DSL_targetCommand();
lean_mark_persistent(l_Lake_DSL_targetCommand);
l_Lake_DSL_leanLibCommand = _init_l_Lake_DSL_leanLibCommand();
lean_mark_persistent(l_Lake_DSL_leanLibCommand);
l_Lake_DSL_leanExeCommand = _init_l_Lake_DSL_leanExeCommand();
lean_mark_persistent(l_Lake_DSL_leanExeCommand);
l_Lake_DSL_inputFileCommand = _init_l_Lake_DSL_inputFileCommand();
lean_mark_persistent(l_Lake_DSL_inputFileCommand);
l_Lake_DSL_inputDirCommand = _init_l_Lake_DSL_inputDirCommand();
lean_mark_persistent(l_Lake_DSL_inputDirCommand);
l_Lake_DSL_externLibDeclSpec = _init_l_Lake_DSL_externLibDeclSpec();
lean_mark_persistent(l_Lake_DSL_externLibDeclSpec);
l_Lake_DSL_externLibCommand = _init_l_Lake_DSL_externLibCommand();
lean_mark_persistent(l_Lake_DSL_externLibCommand);
l_Lake_DSL_scriptDeclSpec = _init_l_Lake_DSL_scriptDeclSpec();
lean_mark_persistent(l_Lake_DSL_scriptDeclSpec);
l_Lake_DSL_scriptDecl = _init_l_Lake_DSL_scriptDecl();
lean_mark_persistent(l_Lake_DSL_scriptDecl);
l_Lake_verLit = _init_l_Lake_verLit();
lean_mark_persistent(l_Lake_verLit);
l_Lake_DSL_facetSuffix = _init_l_Lake_DSL_facetSuffix();
lean_mark_persistent(l_Lake_DSL_facetSuffix);
l_Lake_DSL_packageTargetLit = _init_l_Lake_DSL_packageTargetLit();
lean_mark_persistent(l_Lake_DSL_packageTargetLit);
l_Lake_DSL_term_x60_x2b______ = _init_l_Lake_DSL_term_x60_x2b______();
lean_mark_persistent(l_Lake_DSL_term_x60_x2b______);
l_Lake_DSL_term_x60_x40_______x2f________ = _init_l_Lake_DSL_term_x60_x40_______x2f________();
lean_mark_persistent(l_Lake_DSL_term_x60_x40_______x2f________);
l_Lake_DSL_cmdDo = _init_l_Lake_DSL_cmdDo();
lean_mark_persistent(l_Lake_DSL_cmdDo);
l_Lake_DSL_metaIf = _init_l_Lake_DSL_metaIf();
lean_mark_persistent(l_Lake_DSL_metaIf);
l_Lake_DSL_runIO = _init_l_Lake_DSL_runIO();
lean_mark_persistent(l_Lake_DSL_runIO);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
