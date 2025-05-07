// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Util
// Imports: Lean.Expr Lean.Message
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isSupportedType(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object*);
lean_object* l_Lean_aquote(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("Nat", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Expr_isConstOf(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isIntType(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("Int", 3, 3);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Expr_isConstOf(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isIntType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isIntType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstAddNat(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
lean_inc(x_2);
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_4);
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_7 = lean_mk_string_unchecked("instHAdd", 8, 8);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = l_Lean_Expr_isConstOf(x_6, x_8);
lean_dec(x_8);
lean_dec(x_6);
if (x_9 == 0)
{
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_dec(x_4);
x_11 = l_Lean_Meta_Grind_Arith_isNatType(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_dec(x_2);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_mk_string_unchecked("instAddNat", 10, 10);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = l_Lean_Expr_isConstOf(x_12, x_14);
lean_dec(x_14);
lean_dec(x_12);
return x_15;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstAddNat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isInstLENat(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("instLENat", 9, 9);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = l_Lean_Expr_isConstOf(x_1, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isInstLENat___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isInstLENat(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_inc(x_8);
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_15 = l_Lean_Expr_isApp(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_19 = lean_box(0);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_21 = lean_mk_string_unchecked("HAdd", 4, 4);
x_22 = lean_mk_string_unchecked("hAdd", 4, 4);
x_23 = l_Lean_Name_mkStr2(x_21, x_22);
x_24 = l_Lean_Expr_isConstOf(x_20, x_23);
lean_dec(x_23);
lean_dec(x_20);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_dec(x_8);
x_27 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_5);
lean_dec(x_2);
x_28 = lean_box(0);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_32 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_32, 0, x_31);
return x_32;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isNatAdd(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_6);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_11 = l_Lean_Expr_isApp(x_10);
if (x_11 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_Expr_appFnCleanup___redArg(x_10);
x_13 = l_Lean_Expr_isApp(x_12);
if (x_13 == 0)
{
lean_dec(x_12);
lean_dec(x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_12);
x_15 = lean_mk_string_unchecked("HAdd", 4, 4);
x_16 = lean_mk_string_unchecked("hAdd", 4, 4);
x_17 = l_Lean_Name_mkStr2(x_15, x_16);
x_18 = l_Lean_Expr_isConstOf(x_14, x_17);
lean_dec(x_17);
lean_dec(x_14);
if (x_18 == 0)
{
lean_dec(x_6);
return x_18;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_6, 1);
lean_inc(x_19);
lean_dec(x_6);
x_20 = l_Lean_Meta_Grind_Arith_isInstAddNat(x_19);
return x_20;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatAdd___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isNatAdd(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isNatNum_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_12 = lean_mk_string_unchecked("OfNat", 5, 5);
x_13 = lean_mk_string_unchecked("ofNat", 5, 5);
x_14 = l_Lean_Name_mkStr2(x_12, x_13);
x_15 = l_Lean_Expr_isConstOf(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_2);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
x_18 = l_Lean_Expr_cleanupAnnotations(x_17);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
x_20 = lean_box(0);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
lean_inc(x_18);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_22 = lean_mk_string_unchecked("instOfNatNat", 12, 12);
x_23 = l_Lean_Name_mkStr1(x_22);
x_24 = l_Lean_Expr_isConstOf(x_21, x_23);
lean_dec(x_23);
lean_dec(x_21);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_18);
x_25 = lean_box(0);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
if (lean_obj_tag(x_26) == 9)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_ctor_set_tag(x_27, 1);
return x_27;
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec(x_27);
x_31 = lean_box(0);
return x_31;
}
}
else
{
lean_object* x_32; 
lean_dec(x_26);
x_32 = lean_box(0);
return x_32;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isSupportedType(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l_Lean_Meta_Grind_Arith_isNatType(x_1);
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_Arith_isIntType(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isSupportedType___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isSupportedType(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isRelevantPred(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
lean_inc(x_2);
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = lean_mk_string_unchecked("Not", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = l_Lean_Expr_isConstOf(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_2);
x_8 = l_Lean_Expr_isApp(x_4);
if (x_8 == 0)
{
lean_dec(x_4);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_10 = l_Lean_Expr_isApp(x_9);
if (x_10 == 0)
{
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_9);
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_9);
x_12 = lean_mk_string_unchecked("Eq", 2, 2);
x_13 = l_Lean_Name_mkStr1(x_12);
x_14 = l_Lean_Expr_isConstOf(x_11, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
lean_dec(x_9);
x_15 = l_Lean_Expr_isApp(x_11);
if (x_15 == 0)
{
lean_dec(x_11);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
x_17 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_18 = lean_mk_string_unchecked("Dvd", 3, 3);
x_19 = lean_mk_string_unchecked("dvd", 3, 3);
x_20 = l_Lean_Name_mkStr2(x_18, x_19);
x_21 = l_Lean_Expr_isConstOf(x_17, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_mk_string_unchecked("LE", 2, 2);
x_23 = lean_mk_string_unchecked("le", 2, 2);
x_24 = l_Lean_Name_mkStr2(x_22, x_23);
x_25 = l_Lean_Expr_isConstOf(x_17, x_24);
lean_dec(x_24);
lean_dec(x_17);
if (x_25 == 0)
{
lean_dec(x_16);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = l_Lean_Meta_Grind_Arith_isSupportedType(x_16);
lean_dec(x_16);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
x_27 = l_Lean_Meta_Grind_Arith_isSupportedType(x_16);
lean_dec(x_16);
return x_27;
}
}
}
else
{
lean_object* x_28; uint8_t x_29; 
lean_dec(x_11);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_dec(x_9);
x_29 = l_Lean_Meta_Grind_Arith_isSupportedType(x_28);
lean_dec(x_28);
return x_29;
}
}
}
}
else
{
lean_object* x_30; 
lean_dec(x_4);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
lean_dec(x_2);
x_1 = x_30;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isRelevantPred___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isRelevantPred(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_isArithTerm(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_4; uint8_t x_5; 
x_4 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_5 = l_Lean_Expr_isApp(x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = l_Lean_Expr_appFnCleanup___redArg(x_4);
x_7 = l_Lean_Expr_isApp(x_6);
if (x_7 == 0)
{
lean_dec(x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_6);
x_9 = lean_mk_string_unchecked("OfNat", 5, 5);
x_10 = lean_mk_string_unchecked("ofNat", 5, 5);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = l_Lean_Expr_isConstOf(x_8, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = lean_mk_string_unchecked("Neg", 3, 3);
x_14 = lean_mk_string_unchecked("neg", 3, 3);
x_15 = l_Lean_Name_mkStr2(x_13, x_14);
x_16 = l_Lean_Expr_isConstOf(x_8, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = l_Lean_Expr_isApp(x_8);
if (x_17 == 0)
{
lean_dec(x_8);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_19 = l_Lean_Expr_isApp(x_18);
if (x_19 == 0)
{
lean_dec(x_18);
return x_19;
}
else
{
lean_object* x_20; uint8_t x_21; 
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_18);
x_21 = l_Lean_Expr_isApp(x_20);
if (x_21 == 0)
{
lean_dec(x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_23 = lean_mk_string_unchecked("HPow", 4, 4);
x_24 = lean_mk_string_unchecked("hPow", 4, 4);
x_25 = l_Lean_Name_mkStr2(x_23, x_24);
x_26 = l_Lean_Expr_isConstOf(x_22, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_mk_string_unchecked("HMod", 4, 4);
x_28 = lean_mk_string_unchecked("hMod", 4, 4);
x_29 = l_Lean_Name_mkStr2(x_27, x_28);
x_30 = l_Lean_Expr_isConstOf(x_22, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_mk_string_unchecked("HDiv", 4, 4);
x_32 = lean_mk_string_unchecked("hDiv", 4, 4);
x_33 = l_Lean_Name_mkStr2(x_31, x_32);
x_34 = l_Lean_Expr_isConstOf(x_22, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_mk_string_unchecked("HMul", 4, 4);
x_36 = lean_mk_string_unchecked("hMul", 4, 4);
x_37 = l_Lean_Name_mkStr2(x_35, x_36);
x_38 = l_Lean_Expr_isConstOf(x_22, x_37);
lean_dec(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_mk_string_unchecked("HSub", 4, 4);
x_40 = lean_mk_string_unchecked("hSub", 4, 4);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_Expr_isConstOf(x_22, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_mk_string_unchecked("HAdd", 4, 4);
x_44 = lean_mk_string_unchecked("hAdd", 4, 4);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
x_46 = l_Lean_Expr_isConstOf(x_22, x_45);
lean_dec(x_45);
lean_dec(x_22);
return x_46;
}
else
{
lean_dec(x_22);
return x_42;
}
}
else
{
lean_dec(x_22);
return x_38;
}
}
else
{
lean_dec(x_22);
return x_34;
}
}
else
{
lean_dec(x_22);
return x_30;
}
}
else
{
lean_dec(x_22);
return x_26;
}
}
}
}
}
else
{
lean_dec(x_8);
return x_16;
}
}
else
{
lean_dec(x_8);
return x_12;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_isArithTerm___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_quoteIfArithTerm(lean_object* x_1) {
_start:
{
uint8_t x_2; 
lean_inc(x_1);
x_2 = l_Lean_Meta_Grind_Arith_isArithTerm(x_1);
if (x_2 == 0)
{
lean_object* x_3; 
x_3 = l_Lean_MessageData_ofExpr(x_1);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_MessageData_ofExpr(x_1);
x_5 = l_Lean_aquote(x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_to_int(x_3);
x_5 = lean_int_dec_eq(x_2, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_6 = lean_int_emod(x_1, x_2);
x_7 = l_Lean_Meta_Grind_Arith_gcdExt(x_2, x_6);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 1);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_int_ediv(x_1, x_2);
x_14 = lean_int_mul(x_13, x_12);
lean_dec(x_13);
x_15 = lean_int_sub(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_ctor_set(x_9, 1, x_15);
lean_ctor_set(x_9, 0, x_12);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_9, 0);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_9);
x_18 = lean_int_ediv(x_1, x_2);
x_19 = lean_int_mul(x_18, x_17);
lean_dec(x_18);
x_20 = lean_int_sub(x_16, x_19);
lean_dec(x_19);
lean_dec(x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_20);
lean_ctor_set(x_7, 1, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_7, 1);
x_23 = lean_ctor_get(x_7, 0);
lean_inc(x_22);
lean_inc(x_23);
lean_dec(x_7);
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_26 = x_22;
} else {
 lean_dec_ref(x_22);
 x_26 = lean_box(0);
}
x_27 = lean_int_ediv(x_1, x_2);
x_28 = lean_int_mul(x_27, x_25);
lean_dec(x_27);
x_29 = lean_int_sub(x_24, x_28);
lean_dec(x_28);
lean_dec(x_24);
if (lean_is_scalar(x_26)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_26;
}
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_23);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_38; 
x_32 = lean_nat_abs(x_1);
x_33 = lean_nat_to_int(x_32);
x_38 = lean_int_dec_eq(x_1, x_4);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_int_ediv(x_1, x_33);
x_34 = x_39;
goto block_37;
}
else
{
lean_inc(x_4);
x_34 = x_4;
goto block_37;
}
block_37:
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_4);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_gcdExt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_Arith_gcdExt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Message(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Util(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Message(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
