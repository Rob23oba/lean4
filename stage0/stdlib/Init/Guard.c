// Lean compiler output
// Module: Init.Guard
// Imports: Init.Tactics Init.Conv Init.NotationExtra
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
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqA;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardTargetConv;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardExpr;
LEAN_EXPORT lean_object* l_Lean_Parser_colonA;
LEAN_EXPORT lean_object* l_Lean_Parser_Command_guardExprCmd;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEq;
LEAN_EXPORT lean_object* l_Lean_Parser_colonD;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqR;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_Command_guardCmd;
LEAN_EXPORT lean_object* l_Lean_Parser_equalA;
LEAN_EXPORT lean_object* l_Lean_Parser_equalD;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqD;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardTarget;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardHypConv;
LEAN_EXPORT lean_object* l_Lean_Parser_colonR;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardHyp;
LEAN_EXPORT lean_object* l_Lean_Parser_equalS;
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Parser_colonS;
LEAN_EXPORT lean_object* l_Lean_Parser_colon;
LEAN_EXPORT lean_object* l_Lean_Parser_equalR;
LEAN_EXPORT lean_object* l_Lean_Parser_Tactic_guardExprConv;
LEAN_EXPORT lean_object* l_Lean_Parser_equal;
LEAN_EXPORT lean_object* l_Lean_Parser_colonEqS;
static lean_object* _init_l_Lean_Parser_colonR() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonR", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" : ", 3, 3);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colonD() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonD", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" :~ ", 4, 4);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colonS() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonS", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" :ₛ ", 6, 4);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colonA() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonA", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" :ₐ ", 6, 4);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colon() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("colon", 5, 5);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("orelse", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_Parser_colonR;
x_8 = l_Lean_Parser_colonD;
x_9 = l_Lean_Parser_colonS;
x_10 = l_Lean_Parser_colonA;
lean_inc(x_6);
x_11 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_colonEqR() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonEqR", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" := ", 4, 4);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colonEqD() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonEqD", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" :=~ ", 5, 5);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colonEqS() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonEqS", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" :=ₛ ", 7, 5);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colonEqA() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("colonEqA", 8, 8);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" :=ₐ ", 7, 5);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_colonEq() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("colonEq", 7, 7);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("orelse", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_Parser_colonEqR;
x_8 = l_Lean_Parser_colonEqD;
x_9 = l_Lean_Parser_colonEqS;
x_10 = l_Lean_Parser_colonEqA;
lean_inc(x_6);
x_11 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_equalR() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("equalR", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" = ", 3, 3);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_equalD() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("equalD", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" =~ ", 4, 4);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_equalS() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("equalS", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" =ₛ ", 6, 4);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_equalA() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_mk_string_unchecked("equalA", 6, 6);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked(" =ₐ ", 6, 4);
x_6 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_4);
lean_ctor_set(x_7, 2, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Parser_equal() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("equal", 5, 5);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
lean_inc(x_1);
x_4 = l_Lean_Name_mkStr3(x_2, x_3, x_1);
x_5 = lean_mk_string_unchecked("orelse", 6, 6);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_Parser_equalR;
x_8 = l_Lean_Parser_equalD;
x_9 = l_Lean_Parser_equalS;
x_10 = l_Lean_Parser_equalA;
lean_inc(x_6);
x_11 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
lean_inc(x_6);
x_12 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_8);
lean_ctor_set(x_12, 2, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_7);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("guardExpr", 9, 9);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("guard_expr ", 11, 11);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(51u);
lean_inc(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_Lean_Parser_equal;
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardExprConv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("guardExprConv", 13, 13);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("guard_expr ", 11, 11);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(51u);
lean_inc(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = l_Lean_Parser_equal;
lean_inc(x_8);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_14);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_19);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_6);
lean_ctor_set(x_23, 2, x_22);
return x_23;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTarget() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("guardTarget", 11, 11);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("guard_target ", 13, 13);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_equal;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("term", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardTargetConv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("guardTargetConv", 15, 15);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("guard_target ", 13, 13);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = l_Lean_Parser_equal;
lean_inc(x_8);
x_14 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_mk_string_unchecked("term", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_6);
lean_ctor_set(x_20, 2, x_19);
return x_20;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHyp() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("guardHyp", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("guard_hyp ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(1024u);
lean_inc(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("optional", 8, 8);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Parser_colon;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_22);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_19);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_colonEq;
lean_inc(x_8);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lean_Parser_Tactic_guardHypConv() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Tactic", 6, 6);
x_4 = lean_mk_string_unchecked("guardHypConv", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("guard_hyp ", 10, 10);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_11, 0, x_9);
x_12 = lean_unbox(x_10);
lean_ctor_set_uint8(x_11, sizeof(void*)*1, x_12);
x_13 = lean_mk_string_unchecked("term", 4, 4);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_unsigned_to_nat(1024u);
lean_inc(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_mk_string_unchecked("optional", 8, 8);
x_19 = l_Lean_Name_mkStr1(x_18);
x_20 = l_Lean_Parser_colon;
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_14);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_22);
lean_inc(x_8);
x_23 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set(x_23, 2, x_22);
lean_inc(x_19);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_23);
lean_inc(x_8);
x_25 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_25, 0, x_8);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_colonEq;
lean_inc(x_8);
x_27 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_27, 0, x_8);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_22);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_29, 0, x_8);
lean_ctor_set(x_29, 1, x_25);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardExprCmd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Command", 7, 7);
x_4 = lean_mk_string_unchecked("guardExprCmd", 12, 12);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("#guard_expr ", 12, 12);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(51u);
lean_inc(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
lean_inc(x_8);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = l_Lean_Parser_equal;
lean_inc(x_8);
x_17 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_17, 0, x_8);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_6);
lean_ctor_set(x_21, 2, x_20);
return x_21;
}
}
static lean_object* _init_l_Lean_Parser_Command_guardCmd() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Parser", 6, 6);
x_3 = lean_mk_string_unchecked("Command", 7, 7);
x_4 = lean_mk_string_unchecked("guardCmd", 8, 8);
x_5 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(1022u);
x_7 = lean_mk_string_unchecked("andthen", 7, 7);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("#guard ", 7, 7);
x_10 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_mk_string_unchecked("term", 4, 4);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_15, 0, x_8);
lean_ctor_set(x_15, 1, x_10);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_16, 0, x_5);
lean_ctor_set(x_16, 1, x_6);
lean_ctor_set(x_16, 2, x_15);
return x_16;
}
}
lean_object* initialize_Init_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Conv(uint8_t builtin, lean_object*);
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Guard(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Conv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_colonR = _init_l_Lean_Parser_colonR();
lean_mark_persistent(l_Lean_Parser_colonR);
l_Lean_Parser_colonD = _init_l_Lean_Parser_colonD();
lean_mark_persistent(l_Lean_Parser_colonD);
l_Lean_Parser_colonS = _init_l_Lean_Parser_colonS();
lean_mark_persistent(l_Lean_Parser_colonS);
l_Lean_Parser_colonA = _init_l_Lean_Parser_colonA();
lean_mark_persistent(l_Lean_Parser_colonA);
l_Lean_Parser_colon = _init_l_Lean_Parser_colon();
lean_mark_persistent(l_Lean_Parser_colon);
l_Lean_Parser_colonEqR = _init_l_Lean_Parser_colonEqR();
lean_mark_persistent(l_Lean_Parser_colonEqR);
l_Lean_Parser_colonEqD = _init_l_Lean_Parser_colonEqD();
lean_mark_persistent(l_Lean_Parser_colonEqD);
l_Lean_Parser_colonEqS = _init_l_Lean_Parser_colonEqS();
lean_mark_persistent(l_Lean_Parser_colonEqS);
l_Lean_Parser_colonEqA = _init_l_Lean_Parser_colonEqA();
lean_mark_persistent(l_Lean_Parser_colonEqA);
l_Lean_Parser_colonEq = _init_l_Lean_Parser_colonEq();
lean_mark_persistent(l_Lean_Parser_colonEq);
l_Lean_Parser_equalR = _init_l_Lean_Parser_equalR();
lean_mark_persistent(l_Lean_Parser_equalR);
l_Lean_Parser_equalD = _init_l_Lean_Parser_equalD();
lean_mark_persistent(l_Lean_Parser_equalD);
l_Lean_Parser_equalS = _init_l_Lean_Parser_equalS();
lean_mark_persistent(l_Lean_Parser_equalS);
l_Lean_Parser_equalA = _init_l_Lean_Parser_equalA();
lean_mark_persistent(l_Lean_Parser_equalA);
l_Lean_Parser_equal = _init_l_Lean_Parser_equal();
lean_mark_persistent(l_Lean_Parser_equal);
l_Lean_Parser_Tactic_guardExpr = _init_l_Lean_Parser_Tactic_guardExpr();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExpr);
l_Lean_Parser_Tactic_guardExprConv = _init_l_Lean_Parser_Tactic_guardExprConv();
lean_mark_persistent(l_Lean_Parser_Tactic_guardExprConv);
l_Lean_Parser_Tactic_guardTarget = _init_l_Lean_Parser_Tactic_guardTarget();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTarget);
l_Lean_Parser_Tactic_guardTargetConv = _init_l_Lean_Parser_Tactic_guardTargetConv();
lean_mark_persistent(l_Lean_Parser_Tactic_guardTargetConv);
l_Lean_Parser_Tactic_guardHyp = _init_l_Lean_Parser_Tactic_guardHyp();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHyp);
l_Lean_Parser_Tactic_guardHypConv = _init_l_Lean_Parser_Tactic_guardHypConv();
lean_mark_persistent(l_Lean_Parser_Tactic_guardHypConv);
l_Lean_Parser_Command_guardExprCmd = _init_l_Lean_Parser_Command_guardExprCmd();
lean_mark_persistent(l_Lean_Parser_Command_guardExprCmd);
l_Lean_Parser_Command_guardCmd = _init_l_Lean_Parser_Command_guardCmd();
lean_mark_persistent(l_Lean_Parser_Command_guardCmd);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
