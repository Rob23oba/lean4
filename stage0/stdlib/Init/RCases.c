// Lean compiler output
// Module: Init.RCases
// Imports: Init.Tactics Init.Meta
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
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintroPat_quot;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_ignore;
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_explicit;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcases;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintroPat_one;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintroPat_binder;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_tuple;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_clear;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_obtain;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_paren;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rintro;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPatMed;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_one;
extern lean_object* l_Lean_Parser_Tactic_elimTarget;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Category_rcasesPat;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPatLo;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_rcasesPat_quot;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_rintroPat;
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_quot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("rcasesPat", 9, 9);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr2(x_7, x_4);
x_9 = lean_mk_string_unchecked("andthen", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("`(rcasesPat| ", 13, 13);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Name_mkStr1(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(")", 1, 1);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_10);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Category_rcasesPat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatMed() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_1 = lean_mk_string_unchecked("rcasesPatMed", 12, 12);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_mk_string_unchecked(" | ", 3, 3);
lean_inc(x_10);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
x_14 = lean_unbox(x_12);
lean_ctor_set_uint8(x_13, sizeof(void*)*3, x_14);
x_15 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_5);
lean_ctor_set(x_15, 2, x_13);
return x_15;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPatLo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("rcasesPatLo", 11, 11);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
lean_inc(x_1);
x_5 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_1);
x_6 = lean_mk_string_unchecked("andthen", 7, 7);
x_7 = l_Lean_Name_mkStr1(x_6);
x_8 = l_Lean_Parser_Tactic_rcasesPatMed;
x_9 = lean_mk_string_unchecked("optional", 8, 8);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked(" : ", 3, 3);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
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
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_7);
lean_ctor_set(x_19, 1, x_8);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_5);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_one() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_5 = lean_mk_string_unchecked("one", 3, 3);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1022u);
x_8 = lean_mk_string_unchecked("ident", 5, 5);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_7);
lean_ctor_set(x_11, 2, x_10);
return x_11;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_ignore() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_5 = lean_mk_string_unchecked("ignore", 6, 6);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_mk_string_unchecked("_", 1, 1);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_clear() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_5 = lean_mk_string_unchecked("clear", 5, 5);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_mk_string_unchecked("-", 1, 1);
x_9 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_7);
lean_ctor_set(x_10, 2, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_explicit() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_5 = lean_mk_string_unchecked("explicit", 8, 8);
lean_inc(x_4);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1022u);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("@", 1, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("noWs", 4, 4);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_9);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lean_Name_mkStr1(x_4);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_15);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_7);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_tuple() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_5 = lean_mk_string_unchecked("tuple", 5, 5);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("⟨", 3, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Parser_Tactic_rcasesPatLo;
x_13 = lean_mk_string_unchecked(",", 1, 1);
x_14 = lean_mk_string_unchecked(", ", 2, 2);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
lean_ctor_set(x_17, 2, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*3, x_18);
lean_inc(x_9);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_17);
x_20 = lean_mk_string_unchecked("⟩", 3, 1);
x_21 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_21, 0, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_7);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcasesPat_paren() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_5 = lean_mk_string_unchecked("paren", 5, 5);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("(", 1, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = l_Lean_Parser_Tactic_rcasesPatLo;
lean_inc(x_9);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_mk_string_unchecked(")", 1, 1);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_16, 0, x_9);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_17, 0, x_6);
lean_ctor_set(x_17, 1, x_7);
lean_ctor_set(x_17, 2, x_16);
return x_17;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_quot() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Term", 4, 4);
x_4 = lean_mk_string_unchecked("quot", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1024u);
x_7 = lean_mk_string_unchecked("rintroPat", 9, 9);
lean_inc(x_7);
x_8 = l_Lean_Name_mkStr2(x_7, x_4);
x_9 = lean_mk_string_unchecked("andthen", 7, 7);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("`(rintroPat| ", 13, 13);
x_12 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = l_Lean_Name_mkStr1(x_7);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked(")", 1, 1);
x_17 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_17, 0, x_16);
lean_inc(x_10);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_10);
lean_ctor_set(x_18, 1, x_15);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_12);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Category_rintroPat() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_one() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rintroPat", 9, 9);
x_5 = lean_mk_string_unchecked("one", 3, 3);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1022u);
x_8 = lean_mk_string_unchecked("rcasesPat", 9, 9);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_7);
lean_ctor_set(x_12, 2, x_11);
return x_12;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintroPat_binder() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rintroPat", 9, 9);
x_5 = lean_mk_string_unchecked("binder", 6, 6);
lean_inc(x_4);
x_6 = l_Lean_Name_mkStr5(x_1, x_2, x_3, x_4, x_5);
x_7 = lean_unsigned_to_nat(1024u);
x_8 = lean_mk_string_unchecked("andthen", 7, 7);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_mk_string_unchecked("(", 1, 1);
x_11 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_mk_string_unchecked("many1", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Name_mkStr1(x_4);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_inc(x_9);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_11);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_mk_string_unchecked("optional", 8, 8);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked(" : ", 3, 3);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_mk_string_unchecked("term", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_15);
lean_inc(x_9);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_9);
lean_ctor_set(x_26, 1, x_22);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
lean_inc(x_9);
x_28 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_28, 0, x_9);
lean_ctor_set(x_28, 1, x_18);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_mk_string_unchecked(")", 1, 1);
x_30 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_31, 0, x_9);
lean_ctor_set(x_31, 1, x_28);
lean_ctor_set(x_31, 2, x_30);
x_32 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_32, 0, x_6);
lean_ctor_set(x_32, 1, x_7);
lean_ctor_set(x_32, 2, x_31);
return x_32;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rcases() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rcases", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = l_Lean_Parser_Tactic_elimTarget;
x_13 = lean_mk_string_unchecked(",", 1, 1);
x_14 = lean_mk_string_unchecked(", ", 2, 2);
x_15 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(10, 3, 1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
x_17 = lean_unbox(x_9);
lean_ctor_set_uint8(x_16, sizeof(void*)*3, x_17);
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_16);
x_19 = lean_mk_string_unchecked("optional", 8, 8);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked(" with ", 6, 6);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = l_Lean_Parser_Tactic_rcasesPatLo;
lean_inc(x_8);
x_24 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_24, 0, x_8);
lean_ctor_set(x_24, 1, x_22);
lean_ctor_set(x_24, 2, x_23);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_25);
x_27 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_27, 0, x_5);
lean_ctor_set(x_27, 1, x_6);
lean_ctor_set(x_27, 2, x_26);
return x_27;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_obtain() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("obtain", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("optional", 8, 8);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_Parser_Tactic_rcasesPatMed;
lean_inc(x_8);
x_18 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
lean_inc(x_13);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked(" : ", 3, 3);
x_22 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_mk_string_unchecked("term", 4, 4);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_26);
lean_inc(x_8);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_26);
lean_inc(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_27);
lean_inc(x_8);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_20);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_mk_string_unchecked(" := ", 4, 4);
x_31 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_mk_string_unchecked(",", 1, 1);
x_33 = lean_mk_string_unchecked(", ", 2, 2);
x_34 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_alloc_ctor(11, 3, 1);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_32);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_unbox(x_9);
lean_ctor_set_uint8(x_35, sizeof(void*)*3, x_36);
lean_inc(x_8);
x_37 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_31);
lean_ctor_set(x_37, 2, x_35);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_13);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_39, 0, x_8);
lean_ctor_set(x_39, 1, x_29);
lean_ctor_set(x_39, 2, x_38);
x_40 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_40, 0, x_5);
lean_ctor_set(x_40, 1, x_6);
lean_ctor_set(x_40, 2, x_39);
return x_40;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_rintro() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("rintro", 6, 6);
lean_inc(x_4);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_10, 0, x_4);
x_11 = lean_unbox(x_9);
lean_ctor_set_uint8(x_10, sizeof(void*)*1, x_11);
x_12 = lean_mk_string_unchecked("many1", 5, 5);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = lean_mk_string_unchecked("ppSpace", 7, 7);
x_15 = l_Lean_Name_mkStr1(x_14);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_mk_string_unchecked("colGt", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_8);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_mk_string_unchecked("rintroPat", 9, 9);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_20);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_13);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_8);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_10);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_mk_string_unchecked("optional", 8, 8);
x_29 = l_Lean_Name_mkStr1(x_28);
x_30 = lean_mk_string_unchecked(" : ", 3, 3);
x_31 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_mk_string_unchecked("term", 4, 4);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
lean_inc(x_8);
x_35 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_31);
lean_ctor_set(x_35, 2, x_34);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_27);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_6);
lean_ctor_set(x_38, 2, x_37);
return x_38;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Meta(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_RCases(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Meta(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Tactic_rcasesPat_quot = _init_l_Lean_Parser_Tactic_rcasesPat_quot();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_quot);
l_Lean_Parser_Category_rcasesPat = _init_l_Lean_Parser_Category_rcasesPat();
lean_mark_persistent(l_Lean_Parser_Category_rcasesPat);
l_Lean_Parser_Tactic_rcasesPatMed = _init_l_Lean_Parser_Tactic_rcasesPatMed();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatMed);
l_Lean_Parser_Tactic_rcasesPatLo = _init_l_Lean_Parser_Tactic_rcasesPatLo();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPatLo);
l_Lean_Parser_Tactic_rcasesPat_one = _init_l_Lean_Parser_Tactic_rcasesPat_one();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_one);
l_Lean_Parser_Tactic_rcasesPat_ignore = _init_l_Lean_Parser_Tactic_rcasesPat_ignore();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_ignore);
l_Lean_Parser_Tactic_rcasesPat_clear = _init_l_Lean_Parser_Tactic_rcasesPat_clear();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_clear);
l_Lean_Parser_Tactic_rcasesPat_explicit = _init_l_Lean_Parser_Tactic_rcasesPat_explicit();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_explicit);
l_Lean_Parser_Tactic_rcasesPat_tuple = _init_l_Lean_Parser_Tactic_rcasesPat_tuple();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_tuple);
l_Lean_Parser_Tactic_rcasesPat_paren = _init_l_Lean_Parser_Tactic_rcasesPat_paren();
lean_mark_persistent(l_Lean_Parser_Tactic_rcasesPat_paren);
l_Lean_Parser_Tactic_rintroPat_quot = _init_l_Lean_Parser_Tactic_rintroPat_quot();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_quot);
l_Lean_Parser_Category_rintroPat = _init_l_Lean_Parser_Category_rintroPat();
lean_mark_persistent(l_Lean_Parser_Category_rintroPat);
l_Lean_Parser_Tactic_rintroPat_one = _init_l_Lean_Parser_Tactic_rintroPat_one();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_one);
l_Lean_Parser_Tactic_rintroPat_binder = _init_l_Lean_Parser_Tactic_rintroPat_binder();
lean_mark_persistent(l_Lean_Parser_Tactic_rintroPat_binder);
l_Lean_Parser_Tactic_rcases = _init_l_Lean_Parser_Tactic_rcases();
lean_mark_persistent(l_Lean_Parser_Tactic_rcases);
l_Lean_Parser_Tactic_obtain = _init_l_Lean_Parser_Tactic_obtain();
lean_mark_persistent(l_Lean_Parser_Tactic_obtain);
l_Lean_Parser_Tactic_rintro = _init_l_Lean_Parser_Tactic_rintro();
lean_mark_persistent(l_Lean_Parser_Tactic_rintro);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
