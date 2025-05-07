// Lean compiler output
// Module: Init.Data.Bool
// Imports: Init.NotationExtra
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
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instMin;
LEAN_EXPORT lean_object* l_Bool_instMin___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instMax___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableLe___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Bool_toNat(uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instMax___lam__0(uint8_t, uint8_t);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instLT;
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instMax;
LEAN_EXPORT uint8_t l_Bool_instDecidableLt(uint8_t, uint8_t);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_instLE;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_term___x5e_x5e__;
LEAN_EXPORT uint8_t l_Bool_xor(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Bool_instDecidableLt___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t);
LEAN_EXPORT uint8_t l_Bool_instDecidableLe(uint8_t, uint8_t);
LEAN_EXPORT uint8_t l_Bool_instMin___lam__0(uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred(lean_object*, lean_object*);
lean_object* l_String_toSubstring_x27(lean_object*);
LEAN_EXPORT uint8_t l_Bool_xor(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l_Bool_xor___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Bool_xor(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Bool_term___x5e_x5e__() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_1 = lean_mk_string_unchecked("Bool", 4, 4);
x_2 = lean_mk_string_unchecked("term_^^_", 8, 8);
x_3 = l_Lean_Name_mkStr2(x_1, x_2);
x_4 = lean_unsigned_to_nat(33u);
x_5 = lean_mk_string_unchecked("andthen", 7, 7);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked(" ^^ ", 4, 4);
x_8 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked("term", 4, 4);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_unsigned_to_nat(34u);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(2, 3, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_8);
lean_ctor_set(x_13, 2, x_12);
x_14 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_4);
lean_ctor_set(x_14, 3, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______macroRules__Bool__term___x5e_x5e____1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_mk_string_unchecked("Bool", 4, 4);
x_5 = lean_mk_string_unchecked("term_^^_", 8, 8);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_1, x_10);
x_12 = lean_unsigned_to_nat(2u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
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
x_20 = lean_mk_string_unchecked("Lean", 4, 4);
x_21 = lean_mk_string_unchecked("Parser", 6, 6);
x_22 = lean_mk_string_unchecked("Term", 4, 4);
x_23 = lean_mk_string_unchecked("app", 3, 3);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
x_25 = lean_mk_string_unchecked("xor", 3, 3);
lean_inc(x_25);
x_26 = l_String_toSubstring_x27(x_25);
lean_inc(x_25);
x_27 = l_Lean_Name_mkStr1(x_25);
x_28 = l_Lean_addMacroScope(x_19, x_27, x_18);
x_29 = l_Lean_Name_mkStr2(x_4, x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_inc(x_17);
x_34 = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_28);
lean_ctor_set(x_34, 3, x_33);
x_35 = lean_mk_string_unchecked("null", 4, 4);
x_36 = l_Lean_Name_mkStr1(x_35);
lean_inc(x_17);
x_37 = l_Lean_Syntax_node2(x_17, x_36, x_11, x_13);
x_38 = l_Lean_Syntax_node2(x_17, x_24, x_34, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Parser", 6, 6);
x_6 = lean_mk_string_unchecked("Term", 4, 4);
x_7 = lean_mk_string_unchecked("app", 3, 3);
x_8 = l_Lean_Name_mkStr4(x_4, x_5, x_6, x_7);
lean_inc(x_1);
x_9 = l_Lean_Syntax_isOfKind(x_1, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = l_Lean_Syntax_getArg(x_1, x_12);
x_14 = lean_mk_string_unchecked("ident", 5, 5);
x_15 = l_Lean_Name_mkStr1(x_14);
lean_inc(x_13);
x_16 = l_Lean_Syntax_isOfKind(x_13, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_13);
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_3);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = l_Lean_Syntax_getArg(x_1, x_19);
lean_dec(x_1);
x_21 = lean_unsigned_to_nat(2u);
lean_inc(x_20);
x_22 = l_Lean_Syntax_matchesNull(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_20);
lean_dec(x_13);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_3);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = l_Lean_Syntax_getArg(x_20, x_12);
x_26 = l_Lean_Syntax_getArg(x_20, x_19);
lean_dec(x_20);
x_27 = l_Lean_replaceRef(x_13, x_2);
lean_dec(x_13);
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
x_30 = l_Lean_SourceInfo_fromRef(x_27, x_29);
lean_dec(x_27);
x_31 = lean_mk_string_unchecked("Bool", 4, 4);
x_32 = lean_mk_string_unchecked("term_^^_", 8, 8);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = lean_mk_string_unchecked(" ^^ ", 4, 4);
lean_inc(x_30);
x_35 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_35, 0, x_30);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_Syntax_node3(x_30, x_33, x_25, x_35, x_26);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_3);
return x_37;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Bool___aux__Init__Data__Bool______unexpand__Bool__xor__1(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_box(1);
lean_inc(x_1);
x_4 = lean_apply_1(x_1, x_3);
x_5 = lean_unbox(x_4);
lean_dec(x_4);
if (x_5 == 0)
{
uint8_t x_6; 
lean_dec(x_1);
x_6 = lean_unbox(x_2);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_apply_1(x_1, x_2);
x_8 = lean_unbox(x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_unbox(x_2);
return x_9;
}
else
{
return x_8;
}
}
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableForallOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Bool_instDecidableForallOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Bool_instDecidableForallOfDecidablePred___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableForallOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Bool_instDecidableForallOfDecidablePred(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_box(1);
lean_inc(x_1);
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_box(x_4);
x_6 = lean_apply_1(x_1, x_5);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_unbox(x_2);
return x_8;
}
}
else
{
uint8_t x_9; 
lean_dec(x_1);
x_9 = lean_unbox(x_2);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableExistsOfDecidablePred(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Bool_instDecidableExistsOfDecidablePred___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___redArg___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Bool_instDecidableExistsOfDecidablePred___redArg(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableExistsOfDecidablePred___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Bool_instDecidableExistsOfDecidablePred(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Bool_instLE() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
static lean_object* _init_l_Bool_instLT() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLe(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(1);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Bool_instDecidableLe(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Bool_instDecidableLt(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Bool_instDecidableLt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Bool_instDecidableLt(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Bool_instMax___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_2;
}
else
{
return x_1;
}
}
}
static lean_object* _init_l_Bool_instMax() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Bool_instMax___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Bool_instMax___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Bool_instMax___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Bool_instMin___lam__0(uint8_t x_1, uint8_t x_2) {
_start:
{
if (x_1 == 0)
{
return x_1;
}
else
{
return x_2;
}
}
}
static lean_object* _init_l_Bool_instMin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Bool_instMin___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Bool_instMin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Bool_instMin___lam__0(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Bool_toNat(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
else
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Bool_toNat(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Bool_toInt(uint8_t x_1) {
_start:
{
if (x_1 == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_to_int(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_to_int(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Bool_toInt___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Bool_toInt(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_boolPredToPred(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
LEAN_EXPORT lean_object* l_boolRelToRel(lean_object* x_1) {
_start:
{
return lean_box(0);
}
}
lean_object* initialize_Init_NotationExtra(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Bool(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_NotationExtra(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Bool_term___x5e_x5e__ = _init_l_Bool_term___x5e_x5e__();
lean_mark_persistent(l_Bool_term___x5e_x5e__);
l_Bool_instLE = _init_l_Bool_instLE();
lean_mark_persistent(l_Bool_instLE);
l_Bool_instLT = _init_l_Bool_instLT();
lean_mark_persistent(l_Bool_instLT);
l_Bool_instMax = _init_l_Bool_instMax();
lean_mark_persistent(l_Bool_instMax);
l_Bool_instMin = _init_l_Bool_instMin();
lean_mark_persistent(l_Bool_instMin);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
