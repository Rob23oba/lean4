// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Arith.Int.Simp
// Imports: Lean.Meta.Tactic.Simp.Arith.Util Lean.Meta.Tactic.Simp.Arith.Int.Basic
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
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntLE(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatEq(lean_object*);
lean_object* lean_int_emod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isUnsatLe(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go(lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntDvd(lean_object*, lean_object*);
lean_object* l_Lean_mkPropEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntEq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object*);
uint8_t l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_gcdCoeffs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Int_Linear_Poly_isValidLe(lean_object*);
lean_object* l_Lean_mkIntLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkIntAdd(lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_norm(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object*);
lean_object* l_Lean_Meta_mkExpectedPropHint(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toContextExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_ofPoly(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_getConst(lean_object*);
lean_object* l_Int_Linear_Poly_toExpr(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_denoteExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_withAbstractAtoms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object*);
extern lean_object* l_Lean_levelOne;
extern lean_object* l_Lean_reflBoolTrue;
uint8_t l_Int_Linear_Poly_isValidEq(lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_toLinearExpr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Poly_div(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_Linear_Expr_denoteExpr___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_nat_abs(x_5);
x_7 = lean_nat_gcd(x_1, x_6);
lean_dec(x_6);
lean_dec(x_1);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_2, 0);
x_9 = lean_ctor_get(x_2, 2);
x_10 = lean_nat_abs(x_8);
x_11 = lean_nat_gcd(x_1, x_10);
lean_dec(x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_9;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_gcdAll_go(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_nat_abs(x_2);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_ctor_get(x_1, 2);
x_6 = lean_nat_abs(x_4);
x_7 = l_Int_Linear_Poly_gcdAll_go(x_6, x_5);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdAll___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdAll(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_dec_eq(x_1, x_3);
if (x_4 == 0)
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_abs(x_5);
x_8 = lean_nat_gcd(x_1, x_7);
lean_dec(x_7);
lean_dec(x_1);
x_1 = x_8;
x_2 = x_6;
goto _start;
}
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Int_Linear_Poly_gcdCoeffs_x27_go(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(1u);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_nat_abs(x_3);
x_6 = l_Int_Linear_Poly_gcdCoeffs_x27_go(x_5, x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Int_Linear_Poly_gcdCoeffs_x27___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Int_Linear_Poly_gcdCoeffs_x27(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_array_get(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_300; uint8_t x_419; 
lean_inc(x_5);
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_5);
lean_inc(x_2);
lean_inc(x_11);
x_12 = l_Int_Linear_Expr_denoteExpr___redArg(x_11, x_2, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
if (lean_is_exclusive(x_12)) {
 lean_ctor_release(x_12, 0);
 lean_ctor_release(x_12, 1);
 x_15 = x_12;
} else {
 lean_dec_ref(x_12);
 x_15 = lean_box(0);
}
lean_inc(x_3);
lean_inc(x_11);
x_16 = l_Int_Linear_Expr_denoteExpr___redArg(x_11, x_3, x_14);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_19 = x_16;
} else {
 lean_dec_ref(x_16);
 x_19 = lean_box(0);
}
x_20 = l_Lean_mkIntEq(x_13, x_17);
lean_inc(x_3);
lean_inc(x_2);
x_96 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_96, 0, x_2);
lean_ctor_set(x_96, 1, x_3);
x_97 = l_Int_Linear_Expr_norm(x_96);
lean_dec(x_96);
x_419 = l_Int_Linear_Poly_isUnsatEq(x_97);
if (x_419 == 0)
{
uint8_t x_420; 
x_420 = l_Int_Linear_Poly_isValidEq(x_97);
if (x_420 == 0)
{
lean_object* x_421; uint8_t x_422; 
lean_inc(x_97);
x_421 = l_Int_Linear_Poly_toExpr(x_97);
x_422 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_421, x_2);
lean_dec(x_421);
if (x_422 == 0)
{
x_300 = x_422;
goto block_418;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; uint8_t x_426; 
x_423 = lean_unsigned_to_nat(0u);
x_424 = lean_nat_to_int(x_423);
x_425 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_425, 0, x_424);
x_426 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_3, x_425);
lean_dec(x_425);
x_300 = x_426;
goto block_418;
}
}
else
{
lean_object* x_427; 
lean_dec(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_1);
x_427 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_427) == 0)
{
uint8_t x_428; 
x_428 = !lean_is_exclusive(x_427);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
x_429 = lean_ctor_get(x_427, 0);
x_430 = lean_mk_string_unchecked("True", 4, 4);
x_431 = l_Lean_Name_mkStr1(x_430);
x_432 = lean_box(0);
x_433 = l_Lean_Expr_const___override(x_431, x_432);
x_434 = lean_mk_string_unchecked("Linear", 6, 6);
x_435 = lean_mk_string_unchecked("eq_eq_true", 10, 10);
x_436 = l_Lean_Name_mkStr3(x_4, x_434, x_435);
x_437 = l_Lean_Expr_const___override(x_436, x_432);
x_438 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_439 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_440 = l_Lean_reflBoolTrue;
x_441 = l_Lean_mkApp4(x_437, x_429, x_438, x_439, x_440);
lean_inc(x_433);
x_442 = l_Lean_mkPropEq(x_20, x_433);
x_443 = l_Lean_Meta_mkExpectedPropHint(x_441, x_442);
x_444 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_444, 0, x_433);
lean_ctor_set(x_444, 1, x_443);
x_445 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set(x_427, 0, x_445);
return x_427;
}
else
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_446 = lean_ctor_get(x_427, 0);
x_447 = lean_ctor_get(x_427, 1);
lean_inc(x_447);
lean_inc(x_446);
lean_dec(x_427);
x_448 = lean_mk_string_unchecked("True", 4, 4);
x_449 = l_Lean_Name_mkStr1(x_448);
x_450 = lean_box(0);
x_451 = l_Lean_Expr_const___override(x_449, x_450);
x_452 = lean_mk_string_unchecked("Linear", 6, 6);
x_453 = lean_mk_string_unchecked("eq_eq_true", 10, 10);
x_454 = l_Lean_Name_mkStr3(x_4, x_452, x_453);
x_455 = l_Lean_Expr_const___override(x_454, x_450);
x_456 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_457 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_458 = l_Lean_reflBoolTrue;
x_459 = l_Lean_mkApp4(x_455, x_446, x_456, x_457, x_458);
lean_inc(x_451);
x_460 = l_Lean_mkPropEq(x_20, x_451);
x_461 = l_Lean_Meta_mkExpectedPropHint(x_459, x_460);
x_462 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_462, 0, x_451);
lean_ctor_set(x_462, 1, x_461);
x_463 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_463, 0, x_462);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_447);
return x_464;
}
}
else
{
uint8_t x_465; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_465 = !lean_is_exclusive(x_427);
if (x_465 == 0)
{
return x_427;
}
else
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_427, 0);
x_467 = lean_ctor_get(x_427, 1);
lean_inc(x_467);
lean_inc(x_466);
lean_dec(x_427);
x_468 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_468, 0, x_466);
lean_ctor_set(x_468, 1, x_467);
return x_468;
}
}
}
}
else
{
lean_object* x_469; 
lean_dec(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_1);
x_469 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_469) == 0)
{
uint8_t x_470; 
x_470 = !lean_is_exclusive(x_469);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_471 = lean_ctor_get(x_469, 0);
x_472 = lean_mk_string_unchecked("False", 5, 5);
x_473 = l_Lean_Name_mkStr1(x_472);
x_474 = lean_box(0);
x_475 = l_Lean_Expr_const___override(x_473, x_474);
x_476 = lean_mk_string_unchecked("Linear", 6, 6);
x_477 = lean_mk_string_unchecked("eq_eq_false", 11, 11);
x_478 = l_Lean_Name_mkStr3(x_4, x_476, x_477);
x_479 = l_Lean_Expr_const___override(x_478, x_474);
x_480 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_481 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_482 = l_Lean_reflBoolTrue;
x_483 = l_Lean_mkApp4(x_479, x_471, x_480, x_481, x_482);
lean_inc(x_475);
x_484 = l_Lean_mkPropEq(x_20, x_475);
x_485 = l_Lean_Meta_mkExpectedPropHint(x_483, x_484);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_475);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_487, 0, x_486);
lean_ctor_set(x_469, 0, x_487);
return x_469;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; 
x_488 = lean_ctor_get(x_469, 0);
x_489 = lean_ctor_get(x_469, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_469);
x_490 = lean_mk_string_unchecked("False", 5, 5);
x_491 = l_Lean_Name_mkStr1(x_490);
x_492 = lean_box(0);
x_493 = l_Lean_Expr_const___override(x_491, x_492);
x_494 = lean_mk_string_unchecked("Linear", 6, 6);
x_495 = lean_mk_string_unchecked("eq_eq_false", 11, 11);
x_496 = l_Lean_Name_mkStr3(x_4, x_494, x_495);
x_497 = l_Lean_Expr_const___override(x_496, x_492);
x_498 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_499 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_500 = l_Lean_reflBoolTrue;
x_501 = l_Lean_mkApp4(x_497, x_488, x_498, x_499, x_500);
lean_inc(x_493);
x_502 = l_Lean_mkPropEq(x_20, x_493);
x_503 = l_Lean_Meta_mkExpectedPropHint(x_501, x_502);
x_504 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_504, 0, x_493);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_505, 0, x_504);
x_506 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_506, 0, x_505);
lean_ctor_set(x_506, 1, x_489);
return x_506;
}
}
else
{
uint8_t x_507; 
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_507 = !lean_is_exclusive(x_469);
if (x_507 == 0)
{
return x_469;
}
else
{
lean_object* x_508; lean_object* x_509; lean_object* x_510; 
x_508 = lean_ctor_get(x_469, 0);
x_509 = lean_ctor_get(x_469, 1);
lean_inc(x_509);
lean_inc(x_508);
lean_dec(x_469);
x_510 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_510, 0, x_508);
lean_ctor_set(x_510, 1, x_509);
return x_510;
}
}
}
block_35:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = l_Lean_reflBoolTrue;
x_29 = l_Lean_mkApp5(x_22, x_26, x_21, x_25, x_27, x_28);
lean_inc(x_24);
x_30 = l_Lean_mkPropEq(x_20, x_24);
x_31 = l_Lean_Meta_mkExpectedPropHint(x_29, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_32);
if (lean_is_scalar(x_19)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_19;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
block_51:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = l_Lean_reflBoolTrue;
x_45 = l_Lean_mkApp6(x_42, x_41, x_37, x_38, x_39, x_43, x_44);
lean_inc(x_36);
x_46 = l_Lean_mkPropEq(x_20, x_36);
x_47 = l_Lean_Meta_mkExpectedPropHint(x_45, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_15)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_15;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_40);
return x_50;
}
block_95:
{
lean_object* x_55; 
x_55 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_54);
x_58 = l_Lean_mkIntEq(x_52, x_54);
x_59 = lean_mk_string_unchecked("Linear", 6, 6);
x_60 = lean_mk_string_unchecked("norm_eq_var_const", 17, 17);
x_61 = l_Lean_Name_mkStr3(x_4, x_59, x_60);
x_62 = lean_box(0);
x_63 = l_Lean_Expr_const___override(x_61, x_62);
x_64 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_65 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_66 = l_Lean_mkNatLit(x_53);
x_67 = l_Lean_reflBoolTrue;
x_68 = l_Lean_mkApp6(x_63, x_57, x_64, x_65, x_66, x_54, x_67);
lean_inc(x_58);
x_69 = l_Lean_mkPropEq(x_20, x_58);
x_70 = l_Lean_Meta_mkExpectedPropHint(x_68, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_58);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_55, 0, x_72);
return x_55;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_73 = lean_ctor_get(x_55, 0);
x_74 = lean_ctor_get(x_55, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_55);
lean_inc(x_54);
x_75 = l_Lean_mkIntEq(x_52, x_54);
x_76 = lean_mk_string_unchecked("Linear", 6, 6);
x_77 = lean_mk_string_unchecked("norm_eq_var_const", 17, 17);
x_78 = l_Lean_Name_mkStr3(x_4, x_76, x_77);
x_79 = lean_box(0);
x_80 = l_Lean_Expr_const___override(x_78, x_79);
x_81 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_82 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_83 = l_Lean_mkNatLit(x_53);
x_84 = l_Lean_reflBoolTrue;
x_85 = l_Lean_mkApp6(x_80, x_73, x_81, x_82, x_83, x_54, x_84);
lean_inc(x_75);
x_86 = l_Lean_mkPropEq(x_20, x_75);
x_87 = l_Lean_Meta_mkExpectedPropHint(x_85, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_75);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_74);
return x_90;
}
}
else
{
uint8_t x_91; 
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_55);
if (x_91 == 0)
{
return x_55;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_55, 0);
x_93 = lean_ctor_get(x_55, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_55);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
block_299:
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_102 = l_Int_Linear_Poly_gcdCoeffs_x27(x_97);
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_dec_eq(x_102, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_105 = l_Int_Linear_Poly_getConst(x_97);
x_106 = lean_nat_to_int(x_102);
x_107 = lean_int_emod(x_105, x_106);
lean_dec(x_105);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_to_int(x_108);
x_110 = lean_int_dec_eq(x_107, x_109);
lean_dec(x_107);
if (x_110 == 0)
{
lean_object* x_111; 
lean_dec(x_97);
lean_dec(x_15);
lean_dec(x_11);
x_111 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_18);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; uint8_t x_124; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
lean_dec(x_111);
x_114 = lean_mk_string_unchecked("False", 5, 5);
x_115 = l_Lean_Name_mkStr1(x_114);
x_116 = lean_box(0);
x_117 = l_Lean_Expr_const___override(x_115, x_116);
x_118 = lean_mk_string_unchecked("Linear", 6, 6);
x_119 = lean_mk_string_unchecked("eq_eq_false_of_divCoeff", 23, 23);
lean_inc(x_4);
x_120 = l_Lean_Name_mkStr3(x_4, x_118, x_119);
x_121 = l_Lean_Expr_const___override(x_120, x_116);
x_122 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_123 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_124 = lean_int_dec_le(x_109, x_106);
lean_dec(x_109);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_mk_string_unchecked("Neg", 3, 3);
x_126 = lean_mk_string_unchecked("neg", 3, 3);
x_127 = l_Lean_Name_mkStr2(x_125, x_126);
x_128 = l_Lean_Level_ofNat(x_108);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_116);
x_130 = l_Lean_Expr_const___override(x_127, x_129);
lean_inc(x_4);
x_131 = l_Lean_Name_mkStr1(x_4);
x_132 = l_Lean_Expr_const___override(x_131, x_116);
x_133 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_134 = l_Lean_Name_mkStr2(x_4, x_133);
x_135 = l_Lean_Expr_const___override(x_134, x_116);
x_136 = lean_int_neg(x_106);
lean_dec(x_106);
x_137 = l_Int_toNat(x_136);
lean_dec(x_136);
x_138 = l_Lean_instToExprInt_mkNat(x_137);
x_139 = l_Lean_mkApp3(x_130, x_132, x_135, x_138);
x_21 = x_122;
x_22 = x_121;
x_23 = x_113;
x_24 = x_117;
x_25 = x_123;
x_26 = x_112;
x_27 = x_139;
goto block_35;
}
else
{
lean_object* x_140; lean_object* x_141; 
lean_dec(x_4);
x_140 = l_Int_toNat(x_106);
lean_dec(x_106);
x_141 = l_Lean_instToExprInt_mkNat(x_140);
x_21 = x_122;
x_22 = x_121;
x_23 = x_113;
x_24 = x_117;
x_25 = x_123;
x_26 = x_112;
x_27 = x_141;
goto block_35;
}
}
else
{
uint8_t x_142; 
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_142 = !lean_is_exclusive(x_111);
if (x_142 == 0)
{
return x_111;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_111, 0);
x_144 = lean_ctor_get(x_111, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_111);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
else
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
lean_dec(x_19);
x_146 = l_Int_Linear_Poly_div(x_106, x_97);
lean_inc(x_146);
x_147 = l_Int_Linear_Poly_denoteExpr(x_11, x_146, x_98, x_99, x_100, x_101, x_18);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_149 = lean_ctor_get(x_147, 0);
x_150 = lean_ctor_get(x_147, 1);
x_151 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_150);
if (lean_obj_tag(x_151) == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; uint8_t x_164; 
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = l_Lean_mkIntLit(x_109);
x_155 = l_Lean_mkIntEq(x_149, x_154);
x_156 = lean_mk_string_unchecked("Linear", 6, 6);
x_157 = lean_mk_string_unchecked("norm_eq_coeff", 13, 13);
lean_inc(x_4);
x_158 = l_Lean_Name_mkStr3(x_4, x_156, x_157);
x_159 = lean_box(0);
x_160 = l_Lean_Expr_const___override(x_158, x_159);
x_161 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_162 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_163 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_146);
x_164 = lean_int_dec_le(x_109, x_106);
lean_dec(x_109);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_165 = lean_mk_string_unchecked("Neg", 3, 3);
x_166 = lean_mk_string_unchecked("neg", 3, 3);
x_167 = l_Lean_Name_mkStr2(x_165, x_166);
x_168 = l_Lean_Level_ofNat(x_108);
lean_ctor_set_tag(x_147, 1);
lean_ctor_set(x_147, 1, x_159);
lean_ctor_set(x_147, 0, x_168);
x_169 = l_Lean_Expr_const___override(x_167, x_147);
lean_inc(x_4);
x_170 = l_Lean_Name_mkStr1(x_4);
x_171 = l_Lean_Expr_const___override(x_170, x_159);
x_172 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_173 = l_Lean_Name_mkStr2(x_4, x_172);
x_174 = l_Lean_Expr_const___override(x_173, x_159);
x_175 = lean_int_neg(x_106);
lean_dec(x_106);
x_176 = l_Int_toNat(x_175);
lean_dec(x_175);
x_177 = l_Lean_instToExprInt_mkNat(x_176);
x_178 = l_Lean_mkApp3(x_169, x_171, x_174, x_177);
x_36 = x_155;
x_37 = x_161;
x_38 = x_162;
x_39 = x_163;
x_40 = x_153;
x_41 = x_152;
x_42 = x_160;
x_43 = x_178;
goto block_51;
}
else
{
lean_object* x_179; lean_object* x_180; 
lean_free_object(x_147);
lean_dec(x_4);
x_179 = l_Int_toNat(x_106);
lean_dec(x_106);
x_180 = l_Lean_instToExprInt_mkNat(x_179);
x_36 = x_155;
x_37 = x_161;
x_38 = x_162;
x_39 = x_163;
x_40 = x_153;
x_41 = x_152;
x_42 = x_160;
x_43 = x_180;
goto block_51;
}
}
else
{
uint8_t x_181; 
lean_free_object(x_147);
lean_dec(x_149);
lean_dec(x_146);
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_181 = !lean_is_exclusive(x_151);
if (x_181 == 0)
{
return x_151;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_151, 0);
x_183 = lean_ctor_get(x_151, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_151);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_185 = lean_ctor_get(x_147, 0);
x_186 = lean_ctor_get(x_147, 1);
lean_inc(x_186);
lean_inc(x_185);
lean_dec(x_147);
x_187 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_186);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_187, 1);
lean_inc(x_189);
lean_dec(x_187);
x_190 = l_Lean_mkIntLit(x_109);
x_191 = l_Lean_mkIntEq(x_185, x_190);
x_192 = lean_mk_string_unchecked("Linear", 6, 6);
x_193 = lean_mk_string_unchecked("norm_eq_coeff", 13, 13);
lean_inc(x_4);
x_194 = l_Lean_Name_mkStr3(x_4, x_192, x_193);
x_195 = lean_box(0);
x_196 = l_Lean_Expr_const___override(x_194, x_195);
x_197 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_198 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_199 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_146);
x_200 = lean_int_dec_le(x_109, x_106);
lean_dec(x_109);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_201 = lean_mk_string_unchecked("Neg", 3, 3);
x_202 = lean_mk_string_unchecked("neg", 3, 3);
x_203 = l_Lean_Name_mkStr2(x_201, x_202);
x_204 = l_Lean_Level_ofNat(x_108);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_204);
lean_ctor_set(x_205, 1, x_195);
x_206 = l_Lean_Expr_const___override(x_203, x_205);
lean_inc(x_4);
x_207 = l_Lean_Name_mkStr1(x_4);
x_208 = l_Lean_Expr_const___override(x_207, x_195);
x_209 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_210 = l_Lean_Name_mkStr2(x_4, x_209);
x_211 = l_Lean_Expr_const___override(x_210, x_195);
x_212 = lean_int_neg(x_106);
lean_dec(x_106);
x_213 = l_Int_toNat(x_212);
lean_dec(x_212);
x_214 = l_Lean_instToExprInt_mkNat(x_213);
x_215 = l_Lean_mkApp3(x_206, x_208, x_211, x_214);
x_36 = x_191;
x_37 = x_197;
x_38 = x_198;
x_39 = x_199;
x_40 = x_189;
x_41 = x_188;
x_42 = x_196;
x_43 = x_215;
goto block_51;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_4);
x_216 = l_Int_toNat(x_106);
lean_dec(x_106);
x_217 = l_Lean_instToExprInt_mkNat(x_216);
x_36 = x_191;
x_37 = x_197;
x_38 = x_198;
x_39 = x_199;
x_40 = x_189;
x_41 = x_188;
x_42 = x_196;
x_43 = x_217;
goto block_51;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_185);
lean_dec(x_146);
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_218 = lean_ctor_get(x_187, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_187, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_187)) {
 lean_ctor_release(x_187, 0);
 lean_ctor_release(x_187, 1);
 x_220 = x_187;
} else {
 lean_dec_ref(x_187);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
}
}
else
{
lean_object* x_222; uint8_t x_223; 
lean_dec(x_102);
lean_dec(x_19);
lean_dec(x_15);
lean_inc(x_97);
x_222 = l_Int_Linear_Poly_denoteExpr(x_11, x_97, x_98, x_99, x_100, x_101, x_18);
x_223 = !lean_is_exclusive(x_222);
if (x_223 == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_224 = lean_ctor_get(x_222, 0);
x_225 = lean_ctor_get(x_222, 1);
x_226 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_225);
if (lean_obj_tag(x_226) == 0)
{
uint8_t x_227; 
x_227 = !lean_is_exclusive(x_226);
if (x_227 == 0)
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_228 = lean_ctor_get(x_226, 0);
x_229 = lean_unsigned_to_nat(0u);
x_230 = lean_nat_to_int(x_229);
x_231 = l_Lean_mkIntLit(x_230);
lean_dec(x_230);
x_232 = l_Lean_mkIntEq(x_224, x_231);
x_233 = lean_mk_string_unchecked("Linear", 6, 6);
x_234 = lean_mk_string_unchecked("norm_eq", 7, 7);
x_235 = l_Lean_Name_mkStr3(x_4, x_233, x_234);
x_236 = lean_box(0);
x_237 = l_Lean_Expr_const___override(x_235, x_236);
x_238 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_239 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_240 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_97);
x_241 = l_Lean_reflBoolTrue;
x_242 = l_Lean_mkApp5(x_237, x_228, x_238, x_239, x_240, x_241);
lean_inc(x_232);
x_243 = l_Lean_mkPropEq(x_20, x_232);
x_244 = l_Lean_Meta_mkExpectedPropHint(x_242, x_243);
lean_ctor_set(x_222, 1, x_244);
lean_ctor_set(x_222, 0, x_232);
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_222);
lean_ctor_set(x_226, 0, x_245);
return x_226;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_246 = lean_ctor_get(x_226, 0);
x_247 = lean_ctor_get(x_226, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_226);
x_248 = lean_unsigned_to_nat(0u);
x_249 = lean_nat_to_int(x_248);
x_250 = l_Lean_mkIntLit(x_249);
lean_dec(x_249);
x_251 = l_Lean_mkIntEq(x_224, x_250);
x_252 = lean_mk_string_unchecked("Linear", 6, 6);
x_253 = lean_mk_string_unchecked("norm_eq", 7, 7);
x_254 = l_Lean_Name_mkStr3(x_4, x_252, x_253);
x_255 = lean_box(0);
x_256 = l_Lean_Expr_const___override(x_254, x_255);
x_257 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_258 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_259 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_97);
x_260 = l_Lean_reflBoolTrue;
x_261 = l_Lean_mkApp5(x_256, x_246, x_257, x_258, x_259, x_260);
lean_inc(x_251);
x_262 = l_Lean_mkPropEq(x_20, x_251);
x_263 = l_Lean_Meta_mkExpectedPropHint(x_261, x_262);
lean_ctor_set(x_222, 1, x_263);
lean_ctor_set(x_222, 0, x_251);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_222);
x_265 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_265, 0, x_264);
lean_ctor_set(x_265, 1, x_247);
return x_265;
}
}
else
{
uint8_t x_266; 
lean_free_object(x_222);
lean_dec(x_224);
lean_dec(x_97);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_266 = !lean_is_exclusive(x_226);
if (x_266 == 0)
{
return x_226;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; 
x_267 = lean_ctor_get(x_226, 0);
x_268 = lean_ctor_get(x_226, 1);
lean_inc(x_268);
lean_inc(x_267);
lean_dec(x_226);
x_269 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_269, 0, x_267);
lean_ctor_set(x_269, 1, x_268);
return x_269;
}
}
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_222, 0);
x_271 = lean_ctor_get(x_222, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_222);
x_272 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_98, x_99, x_100, x_101, x_271);
if (lean_obj_tag(x_272) == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_273 = lean_ctor_get(x_272, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_272, 1);
lean_inc(x_274);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_275 = x_272;
} else {
 lean_dec_ref(x_272);
 x_275 = lean_box(0);
}
x_276 = lean_unsigned_to_nat(0u);
x_277 = lean_nat_to_int(x_276);
x_278 = l_Lean_mkIntLit(x_277);
lean_dec(x_277);
x_279 = l_Lean_mkIntEq(x_270, x_278);
x_280 = lean_mk_string_unchecked("Linear", 6, 6);
x_281 = lean_mk_string_unchecked("norm_eq", 7, 7);
x_282 = l_Lean_Name_mkStr3(x_4, x_280, x_281);
x_283 = lean_box(0);
x_284 = l_Lean_Expr_const___override(x_282, x_283);
x_285 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_286 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_287 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_97);
x_288 = l_Lean_reflBoolTrue;
x_289 = l_Lean_mkApp5(x_284, x_273, x_285, x_286, x_287, x_288);
lean_inc(x_279);
x_290 = l_Lean_mkPropEq(x_20, x_279);
x_291 = l_Lean_Meta_mkExpectedPropHint(x_289, x_290);
x_292 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_292, 0, x_279);
lean_ctor_set(x_292, 1, x_291);
x_293 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_293, 0, x_292);
if (lean_is_scalar(x_275)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_275;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_274);
return x_294;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; 
lean_dec(x_270);
lean_dec(x_97);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_295 = lean_ctor_get(x_272, 0);
lean_inc(x_295);
x_296 = lean_ctor_get(x_272, 1);
lean_inc(x_296);
if (lean_is_exclusive(x_272)) {
 lean_ctor_release(x_272, 0);
 lean_ctor_release(x_272, 1);
 x_297 = x_272;
} else {
 lean_dec_ref(x_272);
 x_297 = lean_box(0);
}
if (lean_is_scalar(x_297)) {
 x_298 = lean_alloc_ctor(1, 2, 0);
} else {
 x_298 = x_297;
}
lean_ctor_set(x_298, 0, x_295);
lean_ctor_set(x_298, 1, x_296);
return x_298;
}
}
}
}
block_418:
{
if (x_300 == 0)
{
if (lean_obj_tag(x_97) == 0)
{
lean_dec(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
goto block_299;
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; uint8_t x_306; 
x_301 = lean_ctor_get(x_97, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_97, 1);
lean_inc(x_302);
x_303 = lean_ctor_get(x_97, 2);
lean_inc(x_303);
x_304 = lean_unsigned_to_nat(1u);
x_305 = lean_nat_to_int(x_304);
x_306 = lean_int_dec_eq(x_301, x_305);
lean_dec(x_301);
if (x_306 == 0)
{
lean_dec(x_305);
lean_dec(x_303);
lean_dec(x_302);
lean_dec(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
goto block_299;
}
else
{
if (lean_obj_tag(x_303) == 0)
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
lean_dec(x_305);
lean_dec(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
x_307 = lean_ctor_get(x_303, 0);
lean_inc(x_307);
lean_dec(x_303);
x_308 = lean_array_get(x_1, x_5, x_302);
x_309 = lean_int_neg(x_307);
lean_dec(x_307);
x_310 = lean_unsigned_to_nat(0u);
x_311 = lean_nat_to_int(x_310);
x_312 = lean_int_dec_le(x_311, x_309);
lean_dec(x_311);
if (x_312 == 0)
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_313 = lean_mk_string_unchecked("Neg", 3, 3);
x_314 = lean_mk_string_unchecked("neg", 3, 3);
x_315 = l_Lean_Name_mkStr2(x_313, x_314);
x_316 = l_Lean_Level_ofNat(x_310);
x_317 = lean_box(0);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = l_Lean_Expr_const___override(x_315, x_318);
lean_inc(x_4);
x_320 = l_Lean_Name_mkStr1(x_4);
x_321 = l_Lean_Expr_const___override(x_320, x_317);
x_322 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_4);
x_323 = l_Lean_Name_mkStr2(x_4, x_322);
x_324 = l_Lean_Expr_const___override(x_323, x_317);
x_325 = lean_int_neg(x_309);
lean_dec(x_309);
x_326 = l_Int_toNat(x_325);
lean_dec(x_325);
x_327 = l_Lean_instToExprInt_mkNat(x_326);
x_328 = l_Lean_mkApp3(x_319, x_321, x_324, x_327);
x_52 = x_308;
x_53 = x_302;
x_54 = x_328;
goto block_95;
}
else
{
lean_object* x_329; lean_object* x_330; 
x_329 = l_Int_toNat(x_309);
lean_dec(x_309);
x_330 = l_Lean_instToExprInt_mkNat(x_329);
x_52 = x_308;
x_53 = x_302;
x_54 = x_330;
goto block_95;
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_331 = lean_ctor_get(x_303, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_303, 1);
lean_inc(x_332);
x_333 = lean_ctor_get(x_303, 2);
lean_inc(x_333);
lean_dec(x_303);
x_334 = lean_int_neg(x_305);
lean_dec(x_305);
x_335 = lean_int_dec_eq(x_331, x_334);
lean_dec(x_334);
lean_dec(x_331);
if (x_335 == 0)
{
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
goto block_299;
}
else
{
if (lean_obj_tag(x_333) == 0)
{
uint8_t x_336; 
x_336 = !lean_is_exclusive(x_333);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_337 = lean_ctor_get(x_333, 0);
x_338 = lean_unsigned_to_nat(0u);
x_339 = lean_nat_to_int(x_338);
x_340 = lean_int_dec_eq(x_337, x_339);
lean_dec(x_339);
lean_dec(x_337);
if (x_340 == 0)
{
lean_free_object(x_333);
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
goto block_299;
}
else
{
lean_object* x_341; 
lean_dec(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_341 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_341) == 0)
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_341);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_343 = lean_ctor_get(x_341, 0);
lean_inc(x_1);
x_344 = lean_array_get(x_1, x_5, x_302);
x_345 = lean_array_get(x_1, x_5, x_332);
lean_dec(x_5);
x_346 = l_Lean_mkIntEq(x_344, x_345);
x_347 = lean_mk_string_unchecked("Linear", 6, 6);
x_348 = lean_mk_string_unchecked("norm_eq_var", 11, 11);
x_349 = l_Lean_Name_mkStr3(x_4, x_347, x_348);
x_350 = lean_box(0);
x_351 = l_Lean_Expr_const___override(x_349, x_350);
x_352 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_353 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_354 = l_Lean_mkNatLit(x_302);
x_355 = l_Lean_mkNatLit(x_332);
x_356 = l_Lean_reflBoolTrue;
x_357 = l_Lean_mkApp6(x_351, x_343, x_352, x_353, x_354, x_355, x_356);
lean_inc(x_346);
x_358 = l_Lean_mkPropEq(x_20, x_346);
x_359 = l_Lean_Meta_mkExpectedPropHint(x_357, x_358);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_346);
lean_ctor_set(x_360, 1, x_359);
lean_ctor_set_tag(x_333, 1);
lean_ctor_set(x_333, 0, x_360);
lean_ctor_set(x_341, 0, x_333);
return x_341;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_361 = lean_ctor_get(x_341, 0);
x_362 = lean_ctor_get(x_341, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_341);
lean_inc(x_1);
x_363 = lean_array_get(x_1, x_5, x_302);
x_364 = lean_array_get(x_1, x_5, x_332);
lean_dec(x_5);
x_365 = l_Lean_mkIntEq(x_363, x_364);
x_366 = lean_mk_string_unchecked("Linear", 6, 6);
x_367 = lean_mk_string_unchecked("norm_eq_var", 11, 11);
x_368 = l_Lean_Name_mkStr3(x_4, x_366, x_367);
x_369 = lean_box(0);
x_370 = l_Lean_Expr_const___override(x_368, x_369);
x_371 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_372 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_373 = l_Lean_mkNatLit(x_302);
x_374 = l_Lean_mkNatLit(x_332);
x_375 = l_Lean_reflBoolTrue;
x_376 = l_Lean_mkApp6(x_370, x_361, x_371, x_372, x_373, x_374, x_375);
lean_inc(x_365);
x_377 = l_Lean_mkPropEq(x_20, x_365);
x_378 = l_Lean_Meta_mkExpectedPropHint(x_376, x_377);
x_379 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_379, 0, x_365);
lean_ctor_set(x_379, 1, x_378);
lean_ctor_set_tag(x_333, 1);
lean_ctor_set(x_333, 0, x_379);
x_380 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_380, 0, x_333);
lean_ctor_set(x_380, 1, x_362);
return x_380;
}
}
else
{
uint8_t x_381; 
lean_free_object(x_333);
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_341);
if (x_381 == 0)
{
return x_341;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; 
x_382 = lean_ctor_get(x_341, 0);
x_383 = lean_ctor_get(x_341, 1);
lean_inc(x_383);
lean_inc(x_382);
lean_dec(x_341);
x_384 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_384, 0, x_382);
lean_ctor_set(x_384, 1, x_383);
return x_384;
}
}
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_385 = lean_ctor_get(x_333, 0);
lean_inc(x_385);
lean_dec(x_333);
x_386 = lean_unsigned_to_nat(0u);
x_387 = lean_nat_to_int(x_386);
x_388 = lean_int_dec_eq(x_385, x_387);
lean_dec(x_387);
lean_dec(x_385);
if (x_388 == 0)
{
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
goto block_299;
}
else
{
lean_object* x_389; 
lean_dec(x_97);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
lean_inc(x_5);
x_389 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_5, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_392 = x_389;
} else {
 lean_dec_ref(x_389);
 x_392 = lean_box(0);
}
lean_inc(x_1);
x_393 = lean_array_get(x_1, x_5, x_302);
x_394 = lean_array_get(x_1, x_5, x_332);
lean_dec(x_5);
x_395 = l_Lean_mkIntEq(x_393, x_394);
x_396 = lean_mk_string_unchecked("Linear", 6, 6);
x_397 = lean_mk_string_unchecked("norm_eq_var", 11, 11);
x_398 = l_Lean_Name_mkStr3(x_4, x_396, x_397);
x_399 = lean_box(0);
x_400 = l_Lean_Expr_const___override(x_398, x_399);
x_401 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_402 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_403 = l_Lean_mkNatLit(x_302);
x_404 = l_Lean_mkNatLit(x_332);
x_405 = l_Lean_reflBoolTrue;
x_406 = l_Lean_mkApp6(x_400, x_390, x_401, x_402, x_403, x_404, x_405);
lean_inc(x_395);
x_407 = l_Lean_mkPropEq(x_20, x_395);
x_408 = l_Lean_Meta_mkExpectedPropHint(x_406, x_407);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_395);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_409);
if (lean_is_scalar(x_392)) {
 x_411 = lean_alloc_ctor(0, 2, 0);
} else {
 x_411 = x_392;
}
lean_ctor_set(x_411, 0, x_410);
lean_ctor_set(x_411, 1, x_391);
return x_411;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_412 = lean_ctor_get(x_389, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_389, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_414 = x_389;
} else {
 lean_dec_ref(x_389);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_413);
return x_415;
}
}
}
}
else
{
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_302);
lean_dec(x_1);
x_98 = x_6;
x_99 = x_7;
x_100 = x_8;
x_101 = x_9;
goto block_299;
}
}
}
}
}
}
else
{
lean_object* x_416; lean_object* x_417; 
lean_dec(x_97);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_416 = lean_box(0);
x_417 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_417, 0, x_416);
lean_ctor_set(x_417, 1, x_18);
return x_417;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_eqCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_7, 1);
lean_inc(x_17);
lean_dec(x_7);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 1);
lean_inc(x_20);
lean_dec(x_16);
x_21 = l_Lean_instInhabitedExpr;
x_22 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_22);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__1), 10, 4);
lean_closure_set(x_23, 0, x_21);
lean_closure_set(x_23, 1, x_18);
lean_closure_set(x_23, 2, x_19);
lean_closure_set(x_23, 3, x_22);
x_24 = l_Lean_Name_mkStr1(x_22);
x_25 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_20, x_24, x_23, x_2, x_3, x_4, x_5, x_17);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_7);
if (x_26 == 0)
{
return x_7;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_7, 0);
x_28 = lean_ctor_get(x_7, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_7);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_inc(x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_6);
lean_inc(x_2);
lean_inc(x_12);
x_13 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_2, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_295; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_3);
lean_inc(x_12);
x_17 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_3, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 lean_ctor_release(x_17, 1);
 x_20 = x_17;
} else {
 lean_dec_ref(x_17);
 x_20 = lean_box(0);
}
x_21 = l_Lean_mkIntLE(x_15, x_18);
lean_inc(x_3);
lean_inc(x_2);
x_53 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_53, 0, x_2);
lean_ctor_set(x_53, 1, x_3);
x_54 = l_Int_Linear_Expr_norm(x_53);
lean_dec(x_53);
x_295 = l_Int_Linear_Poly_isUnsatLe(x_54);
if (x_295 == 0)
{
uint8_t x_296; 
x_296 = l_Int_Linear_Poly_isValidLe(x_54);
if (x_296 == 0)
{
if (x_5 == 0)
{
lean_free_object(x_13);
goto block_294;
}
else
{
lean_object* x_297; uint8_t x_298; 
lean_inc(x_54);
x_297 = l_Int_Linear_Poly_toExpr(x_54);
x_298 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_297, x_2);
lean_dec(x_297);
if (x_298 == 0)
{
lean_free_object(x_13);
goto block_294;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; uint8_t x_302; 
x_299 = lean_unsigned_to_nat(0u);
x_300 = lean_nat_to_int(x_299);
x_301 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_301, 0, x_300);
x_302 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_3, x_301);
lean_dec(x_301);
if (x_302 == 0)
{
lean_free_object(x_13);
goto block_294;
}
else
{
lean_object* x_303; 
lean_dec(x_54);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_303 = lean_box(0);
lean_ctor_set(x_13, 1, x_19);
lean_ctor_set(x_13, 0, x_303);
return x_13;
}
}
}
}
else
{
lean_object* x_304; 
lean_dec(x_54);
lean_dec(x_20);
lean_free_object(x_13);
lean_dec(x_12);
x_304 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_304) == 0)
{
uint8_t x_305; 
x_305 = !lean_is_exclusive(x_304);
if (x_305 == 0)
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; 
x_306 = lean_ctor_get(x_304, 0);
x_307 = lean_mk_string_unchecked("True", 4, 4);
x_308 = l_Lean_Name_mkStr1(x_307);
x_309 = lean_box(0);
x_310 = l_Lean_Expr_const___override(x_308, x_309);
x_311 = lean_mk_string_unchecked("Linear", 6, 6);
x_312 = lean_mk_string_unchecked("le_eq_true", 10, 10);
x_313 = l_Lean_Name_mkStr3(x_4, x_311, x_312);
x_314 = l_Lean_Expr_const___override(x_313, x_309);
x_315 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_316 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_317 = l_Lean_reflBoolTrue;
x_318 = l_Lean_mkApp4(x_314, x_306, x_315, x_316, x_317);
lean_inc(x_310);
x_319 = l_Lean_mkPropEq(x_21, x_310);
x_320 = l_Lean_Meta_mkExpectedPropHint(x_318, x_319);
x_321 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_321, 0, x_310);
lean_ctor_set(x_321, 1, x_320);
x_322 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_304, 0, x_322);
return x_304;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_323 = lean_ctor_get(x_304, 0);
x_324 = lean_ctor_get(x_304, 1);
lean_inc(x_324);
lean_inc(x_323);
lean_dec(x_304);
x_325 = lean_mk_string_unchecked("True", 4, 4);
x_326 = l_Lean_Name_mkStr1(x_325);
x_327 = lean_box(0);
x_328 = l_Lean_Expr_const___override(x_326, x_327);
x_329 = lean_mk_string_unchecked("Linear", 6, 6);
x_330 = lean_mk_string_unchecked("le_eq_true", 10, 10);
x_331 = l_Lean_Name_mkStr3(x_4, x_329, x_330);
x_332 = l_Lean_Expr_const___override(x_331, x_327);
x_333 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_334 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_335 = l_Lean_reflBoolTrue;
x_336 = l_Lean_mkApp4(x_332, x_323, x_333, x_334, x_335);
lean_inc(x_328);
x_337 = l_Lean_mkPropEq(x_21, x_328);
x_338 = l_Lean_Meta_mkExpectedPropHint(x_336, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_328);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_339);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_324);
return x_341;
}
}
else
{
uint8_t x_342; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_342 = !lean_is_exclusive(x_304);
if (x_342 == 0)
{
return x_304;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_343 = lean_ctor_get(x_304, 0);
x_344 = lean_ctor_get(x_304, 1);
lean_inc(x_344);
lean_inc(x_343);
lean_dec(x_304);
x_345 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_345, 0, x_343);
lean_ctor_set(x_345, 1, x_344);
return x_345;
}
}
}
}
else
{
lean_object* x_346; 
lean_dec(x_54);
lean_dec(x_20);
lean_free_object(x_13);
lean_dec(x_12);
x_346 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_346) == 0)
{
uint8_t x_347; 
x_347 = !lean_is_exclusive(x_346);
if (x_347 == 0)
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_348 = lean_ctor_get(x_346, 0);
x_349 = lean_mk_string_unchecked("False", 5, 5);
x_350 = l_Lean_Name_mkStr1(x_349);
x_351 = lean_box(0);
x_352 = l_Lean_Expr_const___override(x_350, x_351);
x_353 = lean_mk_string_unchecked("Linear", 6, 6);
x_354 = lean_mk_string_unchecked("le_eq_false", 11, 11);
x_355 = l_Lean_Name_mkStr3(x_4, x_353, x_354);
x_356 = l_Lean_Expr_const___override(x_355, x_351);
x_357 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_358 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_359 = l_Lean_reflBoolTrue;
x_360 = l_Lean_mkApp4(x_356, x_348, x_357, x_358, x_359);
lean_inc(x_352);
x_361 = l_Lean_mkPropEq(x_21, x_352);
x_362 = l_Lean_Meta_mkExpectedPropHint(x_360, x_361);
x_363 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_363, 0, x_352);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_364, 0, x_363);
lean_ctor_set(x_346, 0, x_364);
return x_346;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_365 = lean_ctor_get(x_346, 0);
x_366 = lean_ctor_get(x_346, 1);
lean_inc(x_366);
lean_inc(x_365);
lean_dec(x_346);
x_367 = lean_mk_string_unchecked("False", 5, 5);
x_368 = l_Lean_Name_mkStr1(x_367);
x_369 = lean_box(0);
x_370 = l_Lean_Expr_const___override(x_368, x_369);
x_371 = lean_mk_string_unchecked("Linear", 6, 6);
x_372 = lean_mk_string_unchecked("le_eq_false", 11, 11);
x_373 = l_Lean_Name_mkStr3(x_4, x_371, x_372);
x_374 = l_Lean_Expr_const___override(x_373, x_369);
x_375 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_376 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_377 = l_Lean_reflBoolTrue;
x_378 = l_Lean_mkApp4(x_374, x_365, x_375, x_376, x_377);
lean_inc(x_370);
x_379 = l_Lean_mkPropEq(x_21, x_370);
x_380 = l_Lean_Meta_mkExpectedPropHint(x_378, x_379);
x_381 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_381, 0, x_370);
lean_ctor_set(x_381, 1, x_380);
x_382 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_382, 0, x_381);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_382);
lean_ctor_set(x_383, 1, x_366);
return x_383;
}
}
else
{
uint8_t x_384; 
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_384 = !lean_is_exclusive(x_346);
if (x_384 == 0)
{
return x_346;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_346, 0);
x_386 = lean_ctor_get(x_346, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_346);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
block_30:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_inc(x_22);
x_25 = l_Lean_mkPropEq(x_21, x_22);
x_26 = l_Lean_Meta_mkExpectedPropHint(x_23, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_27);
if (lean_is_scalar(x_20)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_20;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
return x_29;
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_reflBoolTrue;
x_40 = l_Lean_mkApp6(x_37, x_32, x_36, x_35, x_34, x_38, x_39);
x_22 = x_31;
x_23 = x_40;
x_24 = x_33;
goto block_30;
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_reflBoolTrue;
x_51 = l_Lean_mkApp6(x_46, x_48, x_43, x_47, x_42, x_49, x_50);
x_22 = x_45;
x_23 = x_51;
x_24 = x_44;
goto block_30;
}
block_205:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = l_Int_Linear_Poly_div(x_58, x_54);
lean_dec(x_58);
lean_inc(x_60);
x_61 = l_Int_Linear_Poly_denoteExpr(x_12, x_60, x_7, x_8, x_9, x_10, x_19);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = lean_ctor_get(x_61, 1);
x_65 = l_Lean_mkIntLit(x_57);
x_66 = l_Lean_mkIntLE(x_63, x_65);
if (x_59 == 0)
{
lean_object* x_67; 
x_67 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
lean_dec(x_67);
x_70 = lean_mk_string_unchecked("Linear", 6, 6);
x_71 = lean_mk_string_unchecked("norm_le_coeff", 13, 13);
lean_inc(x_4);
x_72 = l_Lean_Name_mkStr3(x_4, x_70, x_71);
x_73 = lean_box(0);
x_74 = l_Lean_Expr_const___override(x_72, x_73);
x_75 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_76 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_77 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_60);
x_78 = lean_nat_to_int(x_56);
x_79 = lean_int_dec_le(x_57, x_78);
lean_dec(x_57);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_80 = lean_mk_string_unchecked("Neg", 3, 3);
x_81 = lean_mk_string_unchecked("neg", 3, 3);
x_82 = l_Lean_Name_mkStr2(x_80, x_81);
x_83 = l_Lean_Level_ofNat(x_55);
lean_dec(x_55);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 1, x_73);
lean_ctor_set(x_61, 0, x_83);
x_84 = l_Lean_Expr_const___override(x_82, x_61);
lean_inc(x_4);
x_85 = l_Lean_Name_mkStr1(x_4);
x_86 = l_Lean_Expr_const___override(x_85, x_73);
x_87 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_88 = l_Lean_Name_mkStr2(x_4, x_87);
x_89 = l_Lean_Expr_const___override(x_88, x_73);
x_90 = lean_int_neg(x_78);
lean_dec(x_78);
x_91 = l_Int_toNat(x_90);
lean_dec(x_90);
x_92 = l_Lean_instToExprInt_mkNat(x_91);
x_93 = l_Lean_mkApp3(x_84, x_86, x_89, x_92);
x_31 = x_66;
x_32 = x_68;
x_33 = x_69;
x_34 = x_77;
x_35 = x_76;
x_36 = x_75;
x_37 = x_74;
x_38 = x_93;
goto block_41;
}
else
{
lean_object* x_94; lean_object* x_95; 
lean_free_object(x_61);
lean_dec(x_55);
lean_dec(x_4);
x_94 = l_Int_toNat(x_78);
lean_dec(x_78);
x_95 = l_Lean_instToExprInt_mkNat(x_94);
x_31 = x_66;
x_32 = x_68;
x_33 = x_69;
x_34 = x_77;
x_35 = x_76;
x_36 = x_75;
x_37 = x_74;
x_38 = x_95;
goto block_41;
}
}
else
{
uint8_t x_96; 
lean_dec(x_66);
lean_free_object(x_61);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_67);
if (x_96 == 0)
{
return x_67;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_67, 0);
x_98 = lean_ctor_get(x_67, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_67);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; 
x_100 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_64);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_mk_string_unchecked("Linear", 6, 6);
x_104 = lean_mk_string_unchecked("norm_le_coeff_tight", 19, 19);
lean_inc(x_4);
x_105 = l_Lean_Name_mkStr3(x_4, x_103, x_104);
x_106 = lean_box(0);
x_107 = l_Lean_Expr_const___override(x_105, x_106);
x_108 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_109 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_110 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_60);
x_111 = lean_nat_to_int(x_56);
x_112 = lean_int_dec_le(x_57, x_111);
lean_dec(x_57);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_113 = lean_mk_string_unchecked("Neg", 3, 3);
x_114 = lean_mk_string_unchecked("neg", 3, 3);
x_115 = l_Lean_Name_mkStr2(x_113, x_114);
x_116 = l_Lean_Level_ofNat(x_55);
lean_dec(x_55);
lean_ctor_set_tag(x_61, 1);
lean_ctor_set(x_61, 1, x_106);
lean_ctor_set(x_61, 0, x_116);
x_117 = l_Lean_Expr_const___override(x_115, x_61);
lean_inc(x_4);
x_118 = l_Lean_Name_mkStr1(x_4);
x_119 = l_Lean_Expr_const___override(x_118, x_106);
x_120 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_121 = l_Lean_Name_mkStr2(x_4, x_120);
x_122 = l_Lean_Expr_const___override(x_121, x_106);
x_123 = lean_int_neg(x_111);
lean_dec(x_111);
x_124 = l_Int_toNat(x_123);
lean_dec(x_123);
x_125 = l_Lean_instToExprInt_mkNat(x_124);
x_126 = l_Lean_mkApp3(x_117, x_119, x_122, x_125);
x_42 = x_110;
x_43 = x_108;
x_44 = x_102;
x_45 = x_66;
x_46 = x_107;
x_47 = x_109;
x_48 = x_101;
x_49 = x_126;
goto block_52;
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_free_object(x_61);
lean_dec(x_55);
lean_dec(x_4);
x_127 = l_Int_toNat(x_111);
lean_dec(x_111);
x_128 = l_Lean_instToExprInt_mkNat(x_127);
x_42 = x_110;
x_43 = x_108;
x_44 = x_102;
x_45 = x_66;
x_46 = x_107;
x_47 = x_109;
x_48 = x_101;
x_49 = x_128;
goto block_52;
}
}
else
{
uint8_t x_129; 
lean_dec(x_66);
lean_free_object(x_61);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_129 = !lean_is_exclusive(x_100);
if (x_129 == 0)
{
return x_100;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_100, 0);
x_131 = lean_ctor_get(x_100, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_100);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_133 = lean_ctor_get(x_61, 0);
x_134 = lean_ctor_get(x_61, 1);
lean_inc(x_134);
lean_inc(x_133);
lean_dec(x_61);
x_135 = l_Lean_mkIntLit(x_57);
x_136 = l_Lean_mkIntLE(x_133, x_135);
if (x_59 == 0)
{
lean_object* x_137; 
x_137 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_137) == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_138 = lean_ctor_get(x_137, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
lean_dec(x_137);
x_140 = lean_mk_string_unchecked("Linear", 6, 6);
x_141 = lean_mk_string_unchecked("norm_le_coeff", 13, 13);
lean_inc(x_4);
x_142 = l_Lean_Name_mkStr3(x_4, x_140, x_141);
x_143 = lean_box(0);
x_144 = l_Lean_Expr_const___override(x_142, x_143);
x_145 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_146 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_147 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_60);
x_148 = lean_nat_to_int(x_56);
x_149 = lean_int_dec_le(x_57, x_148);
lean_dec(x_57);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_150 = lean_mk_string_unchecked("Neg", 3, 3);
x_151 = lean_mk_string_unchecked("neg", 3, 3);
x_152 = l_Lean_Name_mkStr2(x_150, x_151);
x_153 = l_Lean_Level_ofNat(x_55);
lean_dec(x_55);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_143);
x_155 = l_Lean_Expr_const___override(x_152, x_154);
lean_inc(x_4);
x_156 = l_Lean_Name_mkStr1(x_4);
x_157 = l_Lean_Expr_const___override(x_156, x_143);
x_158 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_159 = l_Lean_Name_mkStr2(x_4, x_158);
x_160 = l_Lean_Expr_const___override(x_159, x_143);
x_161 = lean_int_neg(x_148);
lean_dec(x_148);
x_162 = l_Int_toNat(x_161);
lean_dec(x_161);
x_163 = l_Lean_instToExprInt_mkNat(x_162);
x_164 = l_Lean_mkApp3(x_155, x_157, x_160, x_163);
x_31 = x_136;
x_32 = x_138;
x_33 = x_139;
x_34 = x_147;
x_35 = x_146;
x_36 = x_145;
x_37 = x_144;
x_38 = x_164;
goto block_41;
}
else
{
lean_object* x_165; lean_object* x_166; 
lean_dec(x_55);
lean_dec(x_4);
x_165 = l_Int_toNat(x_148);
lean_dec(x_148);
x_166 = l_Lean_instToExprInt_mkNat(x_165);
x_31 = x_136;
x_32 = x_138;
x_33 = x_139;
x_34 = x_147;
x_35 = x_146;
x_36 = x_145;
x_37 = x_144;
x_38 = x_166;
goto block_41;
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_136);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_167 = lean_ctor_get(x_137, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_137, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_169 = x_137;
} else {
 lean_dec_ref(x_137);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
lean_object* x_171; 
x_171 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_134);
if (lean_obj_tag(x_171) == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; uint8_t x_183; 
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
x_173 = lean_ctor_get(x_171, 1);
lean_inc(x_173);
lean_dec(x_171);
x_174 = lean_mk_string_unchecked("Linear", 6, 6);
x_175 = lean_mk_string_unchecked("norm_le_coeff_tight", 19, 19);
lean_inc(x_4);
x_176 = l_Lean_Name_mkStr3(x_4, x_174, x_175);
x_177 = lean_box(0);
x_178 = l_Lean_Expr_const___override(x_176, x_177);
x_179 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_180 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_181 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_60);
x_182 = lean_nat_to_int(x_56);
x_183 = lean_int_dec_le(x_57, x_182);
lean_dec(x_57);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_184 = lean_mk_string_unchecked("Neg", 3, 3);
x_185 = lean_mk_string_unchecked("neg", 3, 3);
x_186 = l_Lean_Name_mkStr2(x_184, x_185);
x_187 = l_Lean_Level_ofNat(x_55);
lean_dec(x_55);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_177);
x_189 = l_Lean_Expr_const___override(x_186, x_188);
lean_inc(x_4);
x_190 = l_Lean_Name_mkStr1(x_4);
x_191 = l_Lean_Expr_const___override(x_190, x_177);
x_192 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_193 = l_Lean_Name_mkStr2(x_4, x_192);
x_194 = l_Lean_Expr_const___override(x_193, x_177);
x_195 = lean_int_neg(x_182);
lean_dec(x_182);
x_196 = l_Int_toNat(x_195);
lean_dec(x_195);
x_197 = l_Lean_instToExprInt_mkNat(x_196);
x_198 = l_Lean_mkApp3(x_189, x_191, x_194, x_197);
x_42 = x_181;
x_43 = x_179;
x_44 = x_173;
x_45 = x_136;
x_46 = x_178;
x_47 = x_180;
x_48 = x_172;
x_49 = x_198;
goto block_52;
}
else
{
lean_object* x_199; lean_object* x_200; 
lean_dec(x_55);
lean_dec(x_4);
x_199 = l_Int_toNat(x_182);
lean_dec(x_182);
x_200 = l_Lean_instToExprInt_mkNat(x_199);
x_42 = x_181;
x_43 = x_179;
x_44 = x_173;
x_45 = x_136;
x_46 = x_178;
x_47 = x_180;
x_48 = x_172;
x_49 = x_200;
goto block_52;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_136);
lean_dec(x_60);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_201 = lean_ctor_get(x_171, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_171, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_203 = x_171;
} else {
 lean_dec_ref(x_171);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
}
block_294:
{
lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_206 = l_Int_Linear_Poly_gcdCoeffs_x27(x_54);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_nat_dec_eq(x_206, x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; uint8_t x_214; 
x_209 = l_Int_Linear_Poly_getConst(x_54);
lean_inc(x_206);
x_210 = lean_nat_to_int(x_206);
x_211 = lean_int_emod(x_209, x_210);
lean_dec(x_209);
x_212 = lean_unsigned_to_nat(0u);
x_213 = lean_nat_to_int(x_212);
x_214 = lean_int_dec_eq(x_211, x_213);
lean_dec(x_211);
if (x_214 == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_box(1);
x_216 = lean_unbox(x_215);
x_55 = x_212;
x_56 = x_206;
x_57 = x_213;
x_58 = x_210;
x_59 = x_216;
goto block_205;
}
else
{
x_55 = x_212;
x_56 = x_206;
x_57 = x_213;
x_58 = x_210;
x_59 = x_208;
goto block_205;
}
}
else
{
lean_object* x_217; uint8_t x_218; 
lean_dec(x_206);
lean_dec(x_20);
lean_inc(x_54);
x_217 = l_Int_Linear_Poly_denoteExpr(x_12, x_54, x_7, x_8, x_9, x_10, x_19);
x_218 = !lean_is_exclusive(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_219 = lean_ctor_get(x_217, 0);
x_220 = lean_ctor_get(x_217, 1);
x_221 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_220);
if (lean_obj_tag(x_221) == 0)
{
uint8_t x_222; 
x_222 = !lean_is_exclusive(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
x_223 = lean_ctor_get(x_221, 0);
x_224 = lean_unsigned_to_nat(0u);
x_225 = lean_nat_to_int(x_224);
x_226 = l_Lean_mkIntLit(x_225);
lean_dec(x_225);
x_227 = l_Lean_mkIntLE(x_219, x_226);
x_228 = lean_mk_string_unchecked("Linear", 6, 6);
x_229 = lean_mk_string_unchecked("norm_le", 7, 7);
x_230 = l_Lean_Name_mkStr3(x_4, x_228, x_229);
x_231 = lean_box(0);
x_232 = l_Lean_Expr_const___override(x_230, x_231);
x_233 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_234 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_235 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_54);
x_236 = l_Lean_reflBoolTrue;
x_237 = l_Lean_mkApp5(x_232, x_223, x_233, x_234, x_235, x_236);
lean_inc(x_227);
x_238 = l_Lean_mkPropEq(x_21, x_227);
x_239 = l_Lean_Meta_mkExpectedPropHint(x_237, x_238);
lean_ctor_set(x_217, 1, x_239);
lean_ctor_set(x_217, 0, x_227);
x_240 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_240, 0, x_217);
lean_ctor_set(x_221, 0, x_240);
return x_221;
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
x_241 = lean_ctor_get(x_221, 0);
x_242 = lean_ctor_get(x_221, 1);
lean_inc(x_242);
lean_inc(x_241);
lean_dec(x_221);
x_243 = lean_unsigned_to_nat(0u);
x_244 = lean_nat_to_int(x_243);
x_245 = l_Lean_mkIntLit(x_244);
lean_dec(x_244);
x_246 = l_Lean_mkIntLE(x_219, x_245);
x_247 = lean_mk_string_unchecked("Linear", 6, 6);
x_248 = lean_mk_string_unchecked("norm_le", 7, 7);
x_249 = l_Lean_Name_mkStr3(x_4, x_247, x_248);
x_250 = lean_box(0);
x_251 = l_Lean_Expr_const___override(x_249, x_250);
x_252 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_253 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_254 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_54);
x_255 = l_Lean_reflBoolTrue;
x_256 = l_Lean_mkApp5(x_251, x_241, x_252, x_253, x_254, x_255);
lean_inc(x_246);
x_257 = l_Lean_mkPropEq(x_21, x_246);
x_258 = l_Lean_Meta_mkExpectedPropHint(x_256, x_257);
lean_ctor_set(x_217, 1, x_258);
lean_ctor_set(x_217, 0, x_246);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_217);
x_260 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_260, 0, x_259);
lean_ctor_set(x_260, 1, x_242);
return x_260;
}
}
else
{
uint8_t x_261; 
lean_free_object(x_217);
lean_dec(x_219);
lean_dec(x_54);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_261 = !lean_is_exclusive(x_221);
if (x_261 == 0)
{
return x_221;
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; 
x_262 = lean_ctor_get(x_221, 0);
x_263 = lean_ctor_get(x_221, 1);
lean_inc(x_263);
lean_inc(x_262);
lean_dec(x_221);
x_264 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_264, 0, x_262);
lean_ctor_set(x_264, 1, x_263);
return x_264;
}
}
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_265 = lean_ctor_get(x_217, 0);
x_266 = lean_ctor_get(x_217, 1);
lean_inc(x_266);
lean_inc(x_265);
lean_dec(x_217);
x_267 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_266);
if (lean_obj_tag(x_267) == 0)
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_268 = lean_ctor_get(x_267, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_267, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_270 = x_267;
} else {
 lean_dec_ref(x_267);
 x_270 = lean_box(0);
}
x_271 = lean_unsigned_to_nat(0u);
x_272 = lean_nat_to_int(x_271);
x_273 = l_Lean_mkIntLit(x_272);
lean_dec(x_272);
x_274 = l_Lean_mkIntLE(x_265, x_273);
x_275 = lean_mk_string_unchecked("Linear", 6, 6);
x_276 = lean_mk_string_unchecked("norm_le", 7, 7);
x_277 = l_Lean_Name_mkStr3(x_4, x_275, x_276);
x_278 = lean_box(0);
x_279 = l_Lean_Expr_const___override(x_277, x_278);
x_280 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_281 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_282 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_54);
x_283 = l_Lean_reflBoolTrue;
x_284 = l_Lean_mkApp5(x_279, x_268, x_280, x_281, x_282, x_283);
lean_inc(x_274);
x_285 = l_Lean_mkPropEq(x_21, x_274);
x_286 = l_Lean_Meta_mkExpectedPropHint(x_284, x_285);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_274);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
if (lean_is_scalar(x_270)) {
 x_289 = lean_alloc_ctor(0, 2, 0);
} else {
 x_289 = x_270;
}
lean_ctor_set(x_289, 0, x_288);
lean_ctor_set(x_289, 1, x_269);
return x_289;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; 
lean_dec(x_265);
lean_dec(x_54);
lean_dec(x_21);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_290 = lean_ctor_get(x_267, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_267, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_267)) {
 lean_ctor_release(x_267, 0);
 lean_ctor_release(x_267, 1);
 x_292 = x_267;
} else {
 lean_dec_ref(x_267);
 x_292 = lean_box(0);
}
if (lean_is_scalar(x_292)) {
 x_293 = lean_alloc_ctor(1, 2, 0);
} else {
 x_293 = x_292;
}
lean_ctor_set(x_293, 0, x_290);
lean_ctor_set(x_293, 1, x_291);
return x_293;
}
}
}
}
}
else
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; uint8_t x_432; uint8_t x_552; 
x_388 = lean_ctor_get(x_13, 0);
x_389 = lean_ctor_get(x_13, 1);
lean_inc(x_389);
lean_inc(x_388);
lean_dec(x_13);
lean_inc(x_3);
lean_inc(x_12);
x_390 = l_Int_Linear_Expr_denoteExpr___redArg(x_12, x_3, x_389);
x_391 = lean_ctor_get(x_390, 0);
lean_inc(x_391);
x_392 = lean_ctor_get(x_390, 1);
lean_inc(x_392);
if (lean_is_exclusive(x_390)) {
 lean_ctor_release(x_390, 0);
 lean_ctor_release(x_390, 1);
 x_393 = x_390;
} else {
 lean_dec_ref(x_390);
 x_393 = lean_box(0);
}
x_394 = l_Lean_mkIntLE(x_388, x_391);
lean_inc(x_3);
lean_inc(x_2);
x_426 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_426, 0, x_2);
lean_ctor_set(x_426, 1, x_3);
x_427 = l_Int_Linear_Expr_norm(x_426);
lean_dec(x_426);
x_552 = l_Int_Linear_Poly_isUnsatLe(x_427);
if (x_552 == 0)
{
uint8_t x_553; 
x_553 = l_Int_Linear_Poly_isValidLe(x_427);
if (x_553 == 0)
{
if (x_5 == 0)
{
goto block_551;
}
else
{
lean_object* x_554; uint8_t x_555; 
lean_inc(x_427);
x_554 = l_Int_Linear_Poly_toExpr(x_427);
x_555 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_554, x_2);
lean_dec(x_554);
if (x_555 == 0)
{
goto block_551;
}
else
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; uint8_t x_559; 
x_556 = lean_unsigned_to_nat(0u);
x_557 = lean_nat_to_int(x_556);
x_558 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_558, 0, x_557);
x_559 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_3, x_558);
lean_dec(x_558);
if (x_559 == 0)
{
goto block_551;
}
else
{
lean_object* x_560; lean_object* x_561; 
lean_dec(x_427);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_560 = lean_box(0);
x_561 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_392);
return x_561;
}
}
}
}
else
{
lean_object* x_562; 
lean_dec(x_427);
lean_dec(x_393);
lean_dec(x_12);
x_562 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_392);
if (lean_obj_tag(x_562) == 0)
{
lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_563 = lean_ctor_get(x_562, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_562, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_565 = x_562;
} else {
 lean_dec_ref(x_562);
 x_565 = lean_box(0);
}
x_566 = lean_mk_string_unchecked("True", 4, 4);
x_567 = l_Lean_Name_mkStr1(x_566);
x_568 = lean_box(0);
x_569 = l_Lean_Expr_const___override(x_567, x_568);
x_570 = lean_mk_string_unchecked("Linear", 6, 6);
x_571 = lean_mk_string_unchecked("le_eq_true", 10, 10);
x_572 = l_Lean_Name_mkStr3(x_4, x_570, x_571);
x_573 = l_Lean_Expr_const___override(x_572, x_568);
x_574 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_575 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_576 = l_Lean_reflBoolTrue;
x_577 = l_Lean_mkApp4(x_573, x_563, x_574, x_575, x_576);
lean_inc(x_569);
x_578 = l_Lean_mkPropEq(x_394, x_569);
x_579 = l_Lean_Meta_mkExpectedPropHint(x_577, x_578);
x_580 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_580, 0, x_569);
lean_ctor_set(x_580, 1, x_579);
x_581 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_581, 0, x_580);
if (lean_is_scalar(x_565)) {
 x_582 = lean_alloc_ctor(0, 2, 0);
} else {
 x_582 = x_565;
}
lean_ctor_set(x_582, 0, x_581);
lean_ctor_set(x_582, 1, x_564);
return x_582;
}
else
{
lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; 
lean_dec(x_394);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_583 = lean_ctor_get(x_562, 0);
lean_inc(x_583);
x_584 = lean_ctor_get(x_562, 1);
lean_inc(x_584);
if (lean_is_exclusive(x_562)) {
 lean_ctor_release(x_562, 0);
 lean_ctor_release(x_562, 1);
 x_585 = x_562;
} else {
 lean_dec_ref(x_562);
 x_585 = lean_box(0);
}
if (lean_is_scalar(x_585)) {
 x_586 = lean_alloc_ctor(1, 2, 0);
} else {
 x_586 = x_585;
}
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_584);
return x_586;
}
}
}
else
{
lean_object* x_587; 
lean_dec(x_427);
lean_dec(x_393);
lean_dec(x_12);
x_587 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_392);
if (lean_obj_tag(x_587) == 0)
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; 
x_588 = lean_ctor_get(x_587, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_587, 1);
lean_inc(x_589);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_590 = x_587;
} else {
 lean_dec_ref(x_587);
 x_590 = lean_box(0);
}
x_591 = lean_mk_string_unchecked("False", 5, 5);
x_592 = l_Lean_Name_mkStr1(x_591);
x_593 = lean_box(0);
x_594 = l_Lean_Expr_const___override(x_592, x_593);
x_595 = lean_mk_string_unchecked("Linear", 6, 6);
x_596 = lean_mk_string_unchecked("le_eq_false", 11, 11);
x_597 = l_Lean_Name_mkStr3(x_4, x_595, x_596);
x_598 = l_Lean_Expr_const___override(x_597, x_593);
x_599 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_600 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_601 = l_Lean_reflBoolTrue;
x_602 = l_Lean_mkApp4(x_598, x_588, x_599, x_600, x_601);
lean_inc(x_594);
x_603 = l_Lean_mkPropEq(x_394, x_594);
x_604 = l_Lean_Meta_mkExpectedPropHint(x_602, x_603);
x_605 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_605, 0, x_594);
lean_ctor_set(x_605, 1, x_604);
x_606 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_606, 0, x_605);
if (lean_is_scalar(x_590)) {
 x_607 = lean_alloc_ctor(0, 2, 0);
} else {
 x_607 = x_590;
}
lean_ctor_set(x_607, 0, x_606);
lean_ctor_set(x_607, 1, x_589);
return x_607;
}
else
{
lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; 
lean_dec(x_394);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_608 = lean_ctor_get(x_587, 0);
lean_inc(x_608);
x_609 = lean_ctor_get(x_587, 1);
lean_inc(x_609);
if (lean_is_exclusive(x_587)) {
 lean_ctor_release(x_587, 0);
 lean_ctor_release(x_587, 1);
 x_610 = x_587;
} else {
 lean_dec_ref(x_587);
 x_610 = lean_box(0);
}
if (lean_is_scalar(x_610)) {
 x_611 = lean_alloc_ctor(1, 2, 0);
} else {
 x_611 = x_610;
}
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_609);
return x_611;
}
}
block_403:
{
lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_inc(x_395);
x_398 = l_Lean_mkPropEq(x_394, x_395);
x_399 = l_Lean_Meta_mkExpectedPropHint(x_396, x_398);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_395);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_400);
if (lean_is_scalar(x_393)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_393;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_397);
return x_402;
}
block_414:
{
lean_object* x_412; lean_object* x_413; 
x_412 = l_Lean_reflBoolTrue;
x_413 = l_Lean_mkApp6(x_410, x_405, x_409, x_408, x_407, x_411, x_412);
x_395 = x_404;
x_396 = x_413;
x_397 = x_406;
goto block_403;
}
block_425:
{
lean_object* x_423; lean_object* x_424; 
x_423 = l_Lean_reflBoolTrue;
x_424 = l_Lean_mkApp6(x_419, x_421, x_416, x_420, x_415, x_422, x_423);
x_395 = x_418;
x_396 = x_424;
x_397 = x_417;
goto block_403;
}
block_508:
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
x_433 = l_Int_Linear_Poly_div(x_431, x_427);
lean_dec(x_431);
lean_inc(x_433);
x_434 = l_Int_Linear_Poly_denoteExpr(x_12, x_433, x_7, x_8, x_9, x_10, x_392);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_ctor_get(x_434, 1);
lean_inc(x_436);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_437 = x_434;
} else {
 lean_dec_ref(x_434);
 x_437 = lean_box(0);
}
x_438 = l_Lean_mkIntLit(x_430);
x_439 = l_Lean_mkIntLE(x_435, x_438);
if (x_432 == 0)
{
lean_object* x_440; 
x_440 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_436);
if (lean_obj_tag(x_440) == 0)
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; uint8_t x_452; 
x_441 = lean_ctor_get(x_440, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_440, 1);
lean_inc(x_442);
lean_dec(x_440);
x_443 = lean_mk_string_unchecked("Linear", 6, 6);
x_444 = lean_mk_string_unchecked("norm_le_coeff", 13, 13);
lean_inc(x_4);
x_445 = l_Lean_Name_mkStr3(x_4, x_443, x_444);
x_446 = lean_box(0);
x_447 = l_Lean_Expr_const___override(x_445, x_446);
x_448 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_449 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_450 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_433);
x_451 = lean_nat_to_int(x_429);
x_452 = lean_int_dec_le(x_430, x_451);
lean_dec(x_430);
if (x_452 == 0)
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; lean_object* x_466; lean_object* x_467; 
x_453 = lean_mk_string_unchecked("Neg", 3, 3);
x_454 = lean_mk_string_unchecked("neg", 3, 3);
x_455 = l_Lean_Name_mkStr2(x_453, x_454);
x_456 = l_Lean_Level_ofNat(x_428);
lean_dec(x_428);
if (lean_is_scalar(x_437)) {
 x_457 = lean_alloc_ctor(1, 2, 0);
} else {
 x_457 = x_437;
 lean_ctor_set_tag(x_457, 1);
}
lean_ctor_set(x_457, 0, x_456);
lean_ctor_set(x_457, 1, x_446);
x_458 = l_Lean_Expr_const___override(x_455, x_457);
lean_inc(x_4);
x_459 = l_Lean_Name_mkStr1(x_4);
x_460 = l_Lean_Expr_const___override(x_459, x_446);
x_461 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_462 = l_Lean_Name_mkStr2(x_4, x_461);
x_463 = l_Lean_Expr_const___override(x_462, x_446);
x_464 = lean_int_neg(x_451);
lean_dec(x_451);
x_465 = l_Int_toNat(x_464);
lean_dec(x_464);
x_466 = l_Lean_instToExprInt_mkNat(x_465);
x_467 = l_Lean_mkApp3(x_458, x_460, x_463, x_466);
x_404 = x_439;
x_405 = x_441;
x_406 = x_442;
x_407 = x_450;
x_408 = x_449;
x_409 = x_448;
x_410 = x_447;
x_411 = x_467;
goto block_414;
}
else
{
lean_object* x_468; lean_object* x_469; 
lean_dec(x_437);
lean_dec(x_428);
lean_dec(x_4);
x_468 = l_Int_toNat(x_451);
lean_dec(x_451);
x_469 = l_Lean_instToExprInt_mkNat(x_468);
x_404 = x_439;
x_405 = x_441;
x_406 = x_442;
x_407 = x_450;
x_408 = x_449;
x_409 = x_448;
x_410 = x_447;
x_411 = x_469;
goto block_414;
}
}
else
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_439);
lean_dec(x_437);
lean_dec(x_433);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_470 = lean_ctor_get(x_440, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_440, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_440)) {
 lean_ctor_release(x_440, 0);
 lean_ctor_release(x_440, 1);
 x_472 = x_440;
} else {
 lean_dec_ref(x_440);
 x_472 = lean_box(0);
}
if (lean_is_scalar(x_472)) {
 x_473 = lean_alloc_ctor(1, 2, 0);
} else {
 x_473 = x_472;
}
lean_ctor_set(x_473, 0, x_470);
lean_ctor_set(x_473, 1, x_471);
return x_473;
}
}
else
{
lean_object* x_474; 
x_474 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_436);
if (lean_obj_tag(x_474) == 0)
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; uint8_t x_486; 
x_475 = lean_ctor_get(x_474, 0);
lean_inc(x_475);
x_476 = lean_ctor_get(x_474, 1);
lean_inc(x_476);
lean_dec(x_474);
x_477 = lean_mk_string_unchecked("Linear", 6, 6);
x_478 = lean_mk_string_unchecked("norm_le_coeff_tight", 19, 19);
lean_inc(x_4);
x_479 = l_Lean_Name_mkStr3(x_4, x_477, x_478);
x_480 = lean_box(0);
x_481 = l_Lean_Expr_const___override(x_479, x_480);
x_482 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_483 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_484 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_433);
x_485 = lean_nat_to_int(x_429);
x_486 = lean_int_dec_le(x_430, x_485);
lean_dec(x_430);
if (x_486 == 0)
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_487 = lean_mk_string_unchecked("Neg", 3, 3);
x_488 = lean_mk_string_unchecked("neg", 3, 3);
x_489 = l_Lean_Name_mkStr2(x_487, x_488);
x_490 = l_Lean_Level_ofNat(x_428);
lean_dec(x_428);
if (lean_is_scalar(x_437)) {
 x_491 = lean_alloc_ctor(1, 2, 0);
} else {
 x_491 = x_437;
 lean_ctor_set_tag(x_491, 1);
}
lean_ctor_set(x_491, 0, x_490);
lean_ctor_set(x_491, 1, x_480);
x_492 = l_Lean_Expr_const___override(x_489, x_491);
lean_inc(x_4);
x_493 = l_Lean_Name_mkStr1(x_4);
x_494 = l_Lean_Expr_const___override(x_493, x_480);
x_495 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_496 = l_Lean_Name_mkStr2(x_4, x_495);
x_497 = l_Lean_Expr_const___override(x_496, x_480);
x_498 = lean_int_neg(x_485);
lean_dec(x_485);
x_499 = l_Int_toNat(x_498);
lean_dec(x_498);
x_500 = l_Lean_instToExprInt_mkNat(x_499);
x_501 = l_Lean_mkApp3(x_492, x_494, x_497, x_500);
x_415 = x_484;
x_416 = x_482;
x_417 = x_476;
x_418 = x_439;
x_419 = x_481;
x_420 = x_483;
x_421 = x_475;
x_422 = x_501;
goto block_425;
}
else
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_437);
lean_dec(x_428);
lean_dec(x_4);
x_502 = l_Int_toNat(x_485);
lean_dec(x_485);
x_503 = l_Lean_instToExprInt_mkNat(x_502);
x_415 = x_484;
x_416 = x_482;
x_417 = x_476;
x_418 = x_439;
x_419 = x_481;
x_420 = x_483;
x_421 = x_475;
x_422 = x_503;
goto block_425;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_439);
lean_dec(x_437);
lean_dec(x_433);
lean_dec(x_430);
lean_dec(x_429);
lean_dec(x_428);
lean_dec(x_394);
lean_dec(x_393);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_504 = lean_ctor_get(x_474, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_474, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_474)) {
 lean_ctor_release(x_474, 0);
 lean_ctor_release(x_474, 1);
 x_506 = x_474;
} else {
 lean_dec_ref(x_474);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
}
block_551:
{
lean_object* x_509; lean_object* x_510; uint8_t x_511; 
x_509 = l_Int_Linear_Poly_gcdCoeffs_x27(x_427);
x_510 = lean_unsigned_to_nat(1u);
x_511 = lean_nat_dec_eq(x_509, x_510);
if (x_511 == 0)
{
lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; 
x_512 = l_Int_Linear_Poly_getConst(x_427);
lean_inc(x_509);
x_513 = lean_nat_to_int(x_509);
x_514 = lean_int_emod(x_512, x_513);
lean_dec(x_512);
x_515 = lean_unsigned_to_nat(0u);
x_516 = lean_nat_to_int(x_515);
x_517 = lean_int_dec_eq(x_514, x_516);
lean_dec(x_514);
if (x_517 == 0)
{
lean_object* x_518; uint8_t x_519; 
x_518 = lean_box(1);
x_519 = lean_unbox(x_518);
x_428 = x_515;
x_429 = x_509;
x_430 = x_516;
x_431 = x_513;
x_432 = x_519;
goto block_508;
}
else
{
x_428 = x_515;
x_429 = x_509;
x_430 = x_516;
x_431 = x_513;
x_432 = x_511;
goto block_508;
}
}
else
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_509);
lean_dec(x_393);
lean_inc(x_427);
x_520 = l_Int_Linear_Poly_denoteExpr(x_12, x_427, x_7, x_8, x_9, x_10, x_392);
x_521 = lean_ctor_get(x_520, 0);
lean_inc(x_521);
x_522 = lean_ctor_get(x_520, 1);
lean_inc(x_522);
if (lean_is_exclusive(x_520)) {
 lean_ctor_release(x_520, 0);
 lean_ctor_release(x_520, 1);
 x_523 = x_520;
} else {
 lean_dec_ref(x_520);
 x_523 = lean_box(0);
}
x_524 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_6, x_7, x_8, x_9, x_10, x_522);
if (lean_obj_tag(x_524) == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_525 = lean_ctor_get(x_524, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_524, 1);
lean_inc(x_526);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_527 = x_524;
} else {
 lean_dec_ref(x_524);
 x_527 = lean_box(0);
}
x_528 = lean_unsigned_to_nat(0u);
x_529 = lean_nat_to_int(x_528);
x_530 = l_Lean_mkIntLit(x_529);
lean_dec(x_529);
x_531 = l_Lean_mkIntLE(x_521, x_530);
x_532 = lean_mk_string_unchecked("Linear", 6, 6);
x_533 = lean_mk_string_unchecked("norm_le", 7, 7);
x_534 = l_Lean_Name_mkStr3(x_4, x_532, x_533);
x_535 = lean_box(0);
x_536 = l_Lean_Expr_const___override(x_534, x_535);
x_537 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_538 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_3);
x_539 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_427);
x_540 = l_Lean_reflBoolTrue;
x_541 = l_Lean_mkApp5(x_536, x_525, x_537, x_538, x_539, x_540);
lean_inc(x_531);
x_542 = l_Lean_mkPropEq(x_394, x_531);
x_543 = l_Lean_Meta_mkExpectedPropHint(x_541, x_542);
if (lean_is_scalar(x_523)) {
 x_544 = lean_alloc_ctor(0, 2, 0);
} else {
 x_544 = x_523;
}
lean_ctor_set(x_544, 0, x_531);
lean_ctor_set(x_544, 1, x_543);
x_545 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_545, 0, x_544);
if (lean_is_scalar(x_527)) {
 x_546 = lean_alloc_ctor(0, 2, 0);
} else {
 x_546 = x_527;
}
lean_ctor_set(x_546, 0, x_545);
lean_ctor_set(x_546, 1, x_526);
return x_546;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; 
lean_dec(x_523);
lean_dec(x_521);
lean_dec(x_427);
lean_dec(x_394);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_547 = lean_ctor_get(x_524, 0);
lean_inc(x_547);
x_548 = lean_ctor_get(x_524, 1);
lean_inc(x_548);
if (lean_is_exclusive(x_524)) {
 lean_ctor_release(x_524, 0);
 lean_ctor_release(x_524, 1);
 x_549 = x_524;
} else {
 lean_dec_ref(x_524);
 x_549 = lean_box(0);
}
if (lean_is_scalar(x_549)) {
 x_550 = lean_alloc_ctor(1, 2, 0);
} else {
 x_550 = x_549;
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_548);
return x_550;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_8 = l_Lean_instInhabitedExpr;
x_34 = lean_mk_string_unchecked("LE", 2, 2);
x_35 = lean_mk_string_unchecked("le", 2, 2);
x_36 = l_Lean_Name_mkStr2(x_34, x_35);
x_37 = l_Lean_Expr_isAppOf(x_1, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
x_9 = x_37;
goto block_33;
}
else
{
x_9 = x_2;
goto block_33;
}
block_33:
{
lean_object* x_10; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_10 = l_Lean_Meta_Simp_Arith_Int_leCnstr_x3f(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = !lean_is_exclusive(x_10);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_box(0);
lean_ctor_set(x_10, 0, x_14);
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 1);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_11, 0);
lean_inc(x_18);
lean_dec(x_11);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_mk_string_unchecked("Int", 3, 3);
x_25 = lean_box(x_9);
lean_inc(x_24);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed), 11, 5);
lean_closure_set(x_26, 0, x_8);
lean_closure_set(x_26, 1, x_21);
lean_closure_set(x_26, 2, x_22);
lean_closure_set(x_26, 3, x_24);
lean_closure_set(x_26, 4, x_25);
x_27 = l_Lean_Name_mkStr1(x_24);
x_28 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_23, x_27, x_26, x_3, x_4, x_5, x_6, x_20);
return x_28;
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_10);
if (x_29 == 0)
{
return x_10;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_10, 0);
x_31 = lean_ctor_get(x_10, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_10);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___lam__1(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpLe_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_4);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_4, 0);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
lean_inc(x_15);
x_18 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_15, x_17, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_unsigned_to_nat(2u);
x_22 = l_Lean_Expr_getAppNumArgs(x_1);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_sub(x_22, x_21);
x_25 = lean_nat_sub(x_22, x_23);
lean_dec(x_22);
x_26 = lean_nat_sub(x_24, x_2);
lean_dec(x_24);
x_27 = lean_nat_sub(x_25, x_2);
lean_dec(x_25);
x_28 = lean_box(0);
x_29 = l_Lean_Expr_const___override(x_5, x_28);
x_30 = l_Lean_Expr_getRevArg_x21(x_1, x_26);
x_31 = l_Lean_Expr_getRevArg_x21(x_1, x_27);
x_32 = l_Lean_mkAppB(x_29, x_30, x_31);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_33; 
lean_dec(x_3);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_15);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_4, 0, x_33);
lean_ctor_set(x_18, 0, x_4);
return x_18;
}
else
{
uint8_t x_34; 
lean_free_object(x_4);
x_34 = !lean_is_exclusive(x_20);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_20, 0);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_mk_string_unchecked("Eq", 2, 2);
x_40 = lean_mk_string_unchecked("trans", 5, 5);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_levelOne;
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
x_44 = l_Lean_Expr_const___override(x_41, x_43);
x_45 = lean_box(0);
x_46 = l_Lean_Expr_sort___override(x_45);
lean_inc(x_37);
x_47 = l_Lean_mkApp6(x_44, x_46, x_3, x_15, x_37, x_32, x_38);
lean_ctor_set(x_35, 1, x_47);
return x_18;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_48 = lean_ctor_get(x_35, 0);
x_49 = lean_ctor_get(x_35, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_35);
x_50 = lean_mk_string_unchecked("Eq", 2, 2);
x_51 = lean_mk_string_unchecked("trans", 5, 5);
x_52 = l_Lean_Name_mkStr2(x_50, x_51);
x_53 = l_Lean_levelOne;
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_28);
x_55 = l_Lean_Expr_const___override(x_52, x_54);
x_56 = lean_box(0);
x_57 = l_Lean_Expr_sort___override(x_56);
lean_inc(x_48);
x_58 = l_Lean_mkApp6(x_55, x_57, x_3, x_15, x_48, x_32, x_49);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_58);
lean_ctor_set(x_20, 0, x_59);
return x_18;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_60 = lean_ctor_get(x_20, 0);
lean_inc(x_60);
lean_dec(x_20);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_mk_string_unchecked("Eq", 2, 2);
x_65 = lean_mk_string_unchecked("trans", 5, 5);
x_66 = l_Lean_Name_mkStr2(x_64, x_65);
x_67 = l_Lean_levelOne;
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_28);
x_69 = l_Lean_Expr_const___override(x_66, x_68);
x_70 = lean_box(0);
x_71 = l_Lean_Expr_sort___override(x_70);
lean_inc(x_61);
x_72 = l_Lean_mkApp6(x_69, x_71, x_3, x_15, x_61, x_32, x_62);
if (lean_is_scalar(x_63)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_63;
}
lean_ctor_set(x_73, 0, x_61);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_18, 0, x_74);
return x_18;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_75 = lean_ctor_get(x_18, 0);
x_76 = lean_ctor_get(x_18, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_18);
x_77 = lean_unsigned_to_nat(2u);
x_78 = l_Lean_Expr_getAppNumArgs(x_1);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_nat_sub(x_78, x_77);
x_81 = lean_nat_sub(x_78, x_79);
lean_dec(x_78);
x_82 = lean_nat_sub(x_80, x_2);
lean_dec(x_80);
x_83 = lean_nat_sub(x_81, x_2);
lean_dec(x_81);
x_84 = lean_box(0);
x_85 = l_Lean_Expr_const___override(x_5, x_84);
x_86 = l_Lean_Expr_getRevArg_x21(x_1, x_82);
x_87 = l_Lean_Expr_getRevArg_x21(x_1, x_83);
x_88 = l_Lean_mkAppB(x_85, x_86, x_87);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_89; lean_object* x_90; 
lean_dec(x_3);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_15);
lean_ctor_set(x_89, 1, x_88);
lean_ctor_set(x_4, 0, x_89);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_4);
lean_ctor_set(x_90, 1, x_76);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_free_object(x_4);
x_91 = lean_ctor_get(x_75, 0);
lean_inc(x_91);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 x_92 = x_75;
} else {
 lean_dec_ref(x_75);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_mk_string_unchecked("Eq", 2, 2);
x_97 = lean_mk_string_unchecked("trans", 5, 5);
x_98 = l_Lean_Name_mkStr2(x_96, x_97);
x_99 = l_Lean_levelOne;
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_84);
x_101 = l_Lean_Expr_const___override(x_98, x_100);
x_102 = lean_box(0);
x_103 = l_Lean_Expr_sort___override(x_102);
lean_inc(x_93);
x_104 = l_Lean_mkApp6(x_101, x_103, x_3, x_15, x_93, x_88, x_94);
if (lean_is_scalar(x_95)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_95;
}
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_104);
if (lean_is_scalar(x_92)) {
 x_106 = lean_alloc_ctor(1, 1, 0);
} else {
 x_106 = x_92;
}
lean_ctor_set(x_106, 0, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_76);
return x_107;
}
}
}
else
{
lean_free_object(x_4);
lean_dec(x_15);
lean_dec(x_5);
lean_dec(x_3);
return x_18;
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; 
x_108 = lean_ctor_get(x_4, 0);
lean_inc(x_108);
lean_dec(x_4);
x_109 = lean_box(0);
x_110 = lean_unbox(x_109);
lean_inc(x_108);
x_111 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_108, x_110, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_unsigned_to_nat(2u);
x_116 = l_Lean_Expr_getAppNumArgs(x_1);
x_117 = lean_unsigned_to_nat(3u);
x_118 = lean_nat_sub(x_116, x_115);
x_119 = lean_nat_sub(x_116, x_117);
lean_dec(x_116);
x_120 = lean_nat_sub(x_118, x_2);
lean_dec(x_118);
x_121 = lean_nat_sub(x_119, x_2);
lean_dec(x_119);
x_122 = lean_box(0);
x_123 = l_Lean_Expr_const___override(x_5, x_122);
x_124 = l_Lean_Expr_getRevArg_x21(x_1, x_120);
x_125 = l_Lean_Expr_getRevArg_x21(x_1, x_121);
x_126 = l_Lean_mkAppB(x_123, x_124, x_125);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_3);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_108);
lean_ctor_set(x_127, 1, x_126);
x_128 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_128, 0, x_127);
if (lean_is_scalar(x_114)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_114;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_113);
return x_129;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_130 = lean_ctor_get(x_112, 0);
lean_inc(x_130);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 x_131 = x_112;
} else {
 lean_dec_ref(x_112);
 x_131 = lean_box(0);
}
x_132 = lean_ctor_get(x_130, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_134 = x_130;
} else {
 lean_dec_ref(x_130);
 x_134 = lean_box(0);
}
x_135 = lean_mk_string_unchecked("Eq", 2, 2);
x_136 = lean_mk_string_unchecked("trans", 5, 5);
x_137 = l_Lean_Name_mkStr2(x_135, x_136);
x_138 = l_Lean_levelOne;
x_139 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_122);
x_140 = l_Lean_Expr_const___override(x_137, x_139);
x_141 = lean_box(0);
x_142 = l_Lean_Expr_sort___override(x_141);
lean_inc(x_132);
x_143 = l_Lean_mkApp6(x_140, x_142, x_3, x_108, x_132, x_126, x_133);
if (lean_is_scalar(x_134)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_134;
}
lean_ctor_set(x_144, 0, x_132);
lean_ctor_set(x_144, 1, x_143);
if (lean_is_scalar(x_131)) {
 x_145 = lean_alloc_ctor(1, 1, 0);
} else {
 x_145 = x_131;
}
lean_ctor_set(x_145, 0, x_144);
if (lean_is_scalar(x_114)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_114;
}
lean_ctor_set(x_146, 0, x_145);
lean_ctor_set(x_146, 1, x_113);
return x_146;
}
}
else
{
lean_dec(x_108);
lean_dec(x_5);
lean_dec(x_3);
return x_111;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("Not", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = l_Lean_Expr_isAppOfArity(x_1, x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_box(1);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_Simp_Arith_Int_simpLe_x3f(x_1, x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_27; uint8_t x_28; 
x_14 = l_Lean_Expr_appArg_x21(x_1);
lean_inc(x_14);
x_15 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_14, x_3, x_6);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_box(0);
x_19 = lean_box(0);
x_27 = l_Lean_Expr_cleanupAnnotations(x_16);
x_28 = l_Lean_Expr_isApp(x_27);
if (x_28 == 0)
{
lean_dec(x_27);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
goto block_26;
}
else
{
lean_object* x_29; uint8_t x_30; 
lean_inc(x_27);
x_29 = l_Lean_Expr_appFnCleanup___redArg(x_27);
x_30 = l_Lean_Expr_isApp(x_29);
if (x_30 == 0)
{
lean_dec(x_29);
lean_dec(x_27);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
goto block_26;
}
else
{
lean_object* x_31; uint8_t x_32; 
lean_inc(x_29);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_29);
x_32 = l_Lean_Expr_isApp(x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_27);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
goto block_26;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_34 = l_Lean_Expr_isApp(x_33);
if (x_34 == 0)
{
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_27);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
goto block_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_27, 1);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
lean_dec(x_29);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
x_38 = l_Lean_Expr_appFnCleanup___redArg(x_33);
x_39 = lean_mk_string_unchecked("GT", 2, 2);
x_40 = lean_mk_string_unchecked("gt", 2, 2);
x_41 = l_Lean_Name_mkStr2(x_39, x_40);
x_42 = l_Lean_Expr_isConstOf(x_38, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_mk_string_unchecked("LT", 2, 2);
x_44 = lean_mk_string_unchecked("lt", 2, 2);
x_45 = l_Lean_Name_mkStr2(x_43, x_44);
x_46 = l_Lean_Expr_isConstOf(x_38, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_47 = lean_mk_string_unchecked("GE", 2, 2);
x_48 = lean_mk_string_unchecked("ge", 2, 2);
x_49 = l_Lean_Name_mkStr2(x_47, x_48);
x_50 = l_Lean_Expr_isConstOf(x_38, x_49);
lean_dec(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_mk_string_unchecked("LE", 2, 2);
x_52 = lean_mk_string_unchecked("le", 2, 2);
x_53 = l_Lean_Name_mkStr2(x_51, x_52);
x_54 = l_Lean_Expr_isConstOf(x_38, x_53);
lean_dec(x_53);
lean_dec(x_38);
if (x_54 == 0)
{
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_20 = x_2;
x_21 = x_3;
x_22 = x_4;
x_23 = x_5;
goto block_26;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_37, x_3, x_17);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = l_Lean_Expr_cleanupAnnotations(x_56);
x_59 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_59);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = l_Lean_Expr_isConstOf(x_58, x_60);
lean_dec(x_60);
lean_dec(x_58);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_59);
lean_dec(x_36);
lean_dec(x_35);
x_62 = lean_box(0);
x_63 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_18, x_19, x_62, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_14);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_64 = lean_nat_to_int(x_9);
x_65 = l_Lean_mkIntLit(x_64);
lean_dec(x_64);
x_66 = l_Lean_mkIntAdd(x_35, x_65);
x_67 = l_Lean_mkIntLE(x_66, x_36);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_mk_string_unchecked("not_le_eq", 9, 9);
x_70 = l_Lean_Name_mkStr2(x_59, x_69);
x_71 = lean_box(0);
x_72 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_68, x_70, x_71, x_2, x_3, x_4, x_5, x_57);
lean_dec(x_14);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
lean_dec(x_38);
x_73 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_37, x_3, x_17);
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
lean_dec(x_73);
x_76 = l_Lean_Expr_cleanupAnnotations(x_74);
x_77 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_77);
x_78 = l_Lean_Name_mkStr1(x_77);
x_79 = l_Lean_Expr_isConstOf(x_76, x_78);
lean_dec(x_78);
lean_dec(x_76);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_77);
lean_dec(x_36);
lean_dec(x_35);
x_80 = lean_box(0);
x_81 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_18, x_19, x_80, x_2, x_3, x_4, x_5, x_75);
lean_dec(x_14);
return x_81;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_82 = lean_nat_to_int(x_9);
x_83 = l_Lean_mkIntLit(x_82);
lean_dec(x_82);
x_84 = l_Lean_mkIntAdd(x_36, x_83);
x_85 = l_Lean_mkIntLE(x_84, x_35);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_mk_string_unchecked("not_ge_eq", 9, 9);
x_88 = l_Lean_Name_mkStr2(x_77, x_87);
x_89 = lean_box(0);
x_90 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_86, x_88, x_89, x_2, x_3, x_4, x_5, x_75);
lean_dec(x_14);
return x_90;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
lean_dec(x_38);
x_91 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_37, x_3, x_17);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = l_Lean_Expr_cleanupAnnotations(x_92);
x_95 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_95);
x_96 = l_Lean_Name_mkStr1(x_95);
x_97 = l_Lean_Expr_isConstOf(x_94, x_96);
lean_dec(x_96);
lean_dec(x_94);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
lean_dec(x_95);
lean_dec(x_36);
lean_dec(x_35);
x_98 = lean_box(0);
x_99 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_18, x_19, x_98, x_2, x_3, x_4, x_5, x_93);
lean_dec(x_14);
return x_99;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_100 = l_Lean_mkIntLE(x_35, x_36);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_mk_string_unchecked("not_lt_eq", 9, 9);
x_103 = l_Lean_Name_mkStr2(x_95, x_102);
x_104 = lean_box(0);
x_105 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_101, x_103, x_104, x_2, x_3, x_4, x_5, x_93);
lean_dec(x_14);
return x_105;
}
}
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
lean_dec(x_38);
x_106 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_37, x_3, x_17);
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = l_Lean_Expr_cleanupAnnotations(x_107);
x_110 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_110);
x_111 = l_Lean_Name_mkStr1(x_110);
x_112 = l_Lean_Expr_isConstOf(x_109, x_111);
lean_dec(x_111);
lean_dec(x_109);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_110);
lean_dec(x_36);
lean_dec(x_35);
x_113 = lean_box(0);
x_114 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_18, x_19, x_113, x_2, x_3, x_4, x_5, x_108);
lean_dec(x_14);
return x_114;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_115 = l_Lean_mkIntLE(x_36, x_35);
x_116 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_mk_string_unchecked("not_gt_eq", 9, 9);
x_118 = l_Lean_Name_mkStr2(x_110, x_117);
x_119 = lean_box(0);
x_120 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_116, x_118, x_119, x_2, x_3, x_4, x_5, x_108);
lean_dec(x_14);
return x_120;
}
}
}
}
}
}
block_26:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_box(0);
x_25 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_14, x_9, x_1, x_18, x_19, x_24, x_20, x_21, x_22, x_23, x_17);
lean_dec(x_14);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Simp_Arith_Int_simpRel_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_199; 
lean_inc(x_7);
x_96 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpEq_x3f___lam__0___boxed), 3, 2);
lean_closure_set(x_96, 0, x_1);
lean_closure_set(x_96, 1, x_7);
lean_inc(x_2);
lean_inc(x_96);
x_97 = l_Int_Linear_Expr_denoteExpr___redArg(x_96, x_2, x_12);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
x_199 = lean_int_dec_le(x_4, x_6);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_200 = lean_mk_string_unchecked("Neg", 3, 3);
x_201 = lean_mk_string_unchecked("neg", 3, 3);
x_202 = l_Lean_Name_mkStr2(x_200, x_201);
x_203 = l_Lean_Level_ofNat(x_5);
x_204 = lean_box(0);
x_205 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = l_Lean_Expr_const___override(x_202, x_205);
lean_inc(x_3);
x_207 = l_Lean_Name_mkStr1(x_3);
x_208 = l_Lean_Expr_const___override(x_207, x_204);
x_209 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_3);
x_210 = l_Lean_Name_mkStr2(x_3, x_209);
x_211 = l_Lean_Expr_const___override(x_210, x_204);
x_212 = lean_int_neg(x_6);
x_213 = l_Int_toNat(x_212);
lean_dec(x_212);
x_214 = l_Lean_instToExprInt_mkNat(x_213);
x_215 = l_Lean_mkApp3(x_206, x_208, x_211, x_214);
x_101 = x_215;
goto block_198;
}
else
{
lean_object* x_216; lean_object* x_217; 
x_216 = l_Int_toNat(x_6);
x_217 = l_Lean_instToExprInt_mkNat(x_216);
x_101 = x_217;
goto block_198;
}
block_22:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_inc(x_14);
x_17 = l_Lean_mkPropEq(x_13, x_14);
x_18 = l_Lean_Meta_mkExpectedPropHint(x_15, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
return x_21;
}
block_35:
{
lean_object* x_33; lean_object* x_34; 
x_33 = l_Lean_reflBoolTrue;
x_34 = l_Lean_mkApp7(x_23, x_26, x_31, x_27, x_28, x_30, x_32, x_33);
x_13 = x_24;
x_14 = x_25;
x_15 = x_34;
x_16 = x_29;
goto block_22;
}
block_95:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_inc(x_42);
x_43 = l_Lean_mkIntDvd(x_42, x_37);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_to_int(x_44);
x_46 = lean_int_dec_eq(x_38, x_45);
lean_dec(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11, x_39);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = lean_mk_string_unchecked("Linear", 6, 6);
x_51 = lean_mk_string_unchecked("norm_dvd_gcd", 12, 12);
lean_inc(x_3);
x_52 = l_Lean_Name_mkStr3(x_3, x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_55 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_56 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_41);
x_57 = lean_int_dec_le(x_4, x_38);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_58 = lean_mk_string_unchecked("Neg", 3, 3);
x_59 = lean_mk_string_unchecked("neg", 3, 3);
x_60 = l_Lean_Name_mkStr2(x_58, x_59);
x_61 = l_Lean_Level_ofNat(x_5);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_53);
x_63 = l_Lean_Expr_const___override(x_60, x_62);
lean_inc(x_3);
x_64 = l_Lean_Name_mkStr1(x_3);
x_65 = l_Lean_Expr_const___override(x_64, x_53);
x_66 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_67 = l_Lean_Name_mkStr2(x_3, x_66);
x_68 = l_Lean_Expr_const___override(x_67, x_53);
x_69 = lean_int_neg(x_38);
lean_dec(x_38);
x_70 = l_Int_toNat(x_69);
lean_dec(x_69);
x_71 = l_Lean_instToExprInt_mkNat(x_70);
x_72 = l_Lean_mkApp3(x_63, x_65, x_68, x_71);
x_23 = x_54;
x_24 = x_36;
x_25 = x_43;
x_26 = x_48;
x_27 = x_55;
x_28 = x_42;
x_29 = x_49;
x_30 = x_56;
x_31 = x_40;
x_32 = x_72;
goto block_35;
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_3);
x_73 = l_Int_toNat(x_38);
lean_dec(x_38);
x_74 = l_Lean_instToExprInt_mkNat(x_73);
x_23 = x_54;
x_24 = x_36;
x_25 = x_43;
x_26 = x_48;
x_27 = x_55;
x_28 = x_42;
x_29 = x_49;
x_30 = x_56;
x_31 = x_40;
x_32 = x_74;
goto block_35;
}
}
else
{
uint8_t x_75; 
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_2);
x_75 = !lean_is_exclusive(x_47);
if (x_75 == 0)
{
return x_47;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_47, 0);
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_47);
x_78 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
return x_78;
}
}
}
else
{
lean_object* x_79; 
lean_dec(x_42);
lean_dec(x_38);
x_79 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11, x_39);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_mk_string_unchecked("Linear", 6, 6);
x_83 = lean_mk_string_unchecked("norm_dvd", 8, 8);
x_84 = l_Lean_Name_mkStr3(x_3, x_82, x_83);
x_85 = lean_box(0);
x_86 = l_Lean_Expr_const___override(x_84, x_85);
x_87 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_88 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_41);
x_89 = l_Lean_reflBoolTrue;
x_90 = l_Lean_mkApp5(x_86, x_80, x_40, x_87, x_88, x_89);
x_13 = x_36;
x_14 = x_43;
x_15 = x_90;
x_16 = x_81;
goto block_22;
}
else
{
uint8_t x_91; 
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_3);
lean_dec(x_2);
x_91 = !lean_is_exclusive(x_79);
if (x_91 == 0)
{
return x_79;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_79, 0);
x_93 = lean_ctor_get(x_79, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_79);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
}
block_198:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
lean_inc(x_101);
x_102 = l_Lean_mkIntDvd(x_101, x_98);
x_103 = l_Int_Linear_Expr_norm(x_2);
lean_inc(x_6);
x_104 = l_Int_Linear_Poly_gcdCoeffs(x_103, x_6);
x_105 = l_Int_Linear_Poly_getConst(x_103);
x_106 = lean_int_emod(x_105, x_104);
lean_dec(x_105);
x_107 = lean_int_dec_eq(x_106, x_4);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_100);
lean_dec(x_96);
lean_dec(x_6);
x_108 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_7, x_8, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_108) == 0)
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_110 = lean_ctor_get(x_108, 0);
x_111 = lean_mk_string_unchecked("False", 5, 5);
x_112 = l_Lean_Name_mkStr1(x_111);
x_113 = lean_box(0);
x_114 = l_Lean_Expr_const___override(x_112, x_113);
x_115 = lean_mk_string_unchecked("Linear", 6, 6);
x_116 = lean_mk_string_unchecked("dvd_eq_false", 12, 12);
x_117 = l_Lean_Name_mkStr3(x_3, x_115, x_116);
x_118 = l_Lean_Expr_const___override(x_117, x_113);
x_119 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_120 = l_Lean_reflBoolTrue;
x_121 = l_Lean_mkApp4(x_118, x_110, x_101, x_119, x_120);
lean_inc(x_114);
x_122 = l_Lean_mkPropEq(x_102, x_114);
x_123 = l_Lean_Meta_mkExpectedPropHint(x_121, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_108, 0, x_125);
return x_108;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_126 = lean_ctor_get(x_108, 0);
x_127 = lean_ctor_get(x_108, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_108);
x_128 = lean_mk_string_unchecked("False", 5, 5);
x_129 = l_Lean_Name_mkStr1(x_128);
x_130 = lean_box(0);
x_131 = l_Lean_Expr_const___override(x_129, x_130);
x_132 = lean_mk_string_unchecked("Linear", 6, 6);
x_133 = lean_mk_string_unchecked("dvd_eq_false", 12, 12);
x_134 = l_Lean_Name_mkStr3(x_3, x_132, x_133);
x_135 = l_Lean_Expr_const___override(x_134, x_130);
x_136 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_2);
x_137 = l_Lean_reflBoolTrue;
x_138 = l_Lean_mkApp4(x_135, x_126, x_101, x_136, x_137);
lean_inc(x_131);
x_139 = l_Lean_mkPropEq(x_102, x_131);
x_140 = l_Lean_Meta_mkExpectedPropHint(x_138, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_131);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_127);
return x_143;
}
}
else
{
uint8_t x_144; 
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_3);
lean_dec(x_2);
x_144 = !lean_is_exclusive(x_108);
if (x_144 == 0)
{
return x_108;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_145 = lean_ctor_get(x_108, 0);
x_146 = lean_ctor_get(x_108, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_108);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_145);
lean_ctor_set(x_147, 1, x_146);
return x_147;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_148 = l_Int_Linear_Poly_div(x_104, x_103);
lean_inc(x_148);
x_149 = l_Int_Linear_Poly_toExpr(x_148);
x_150 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_2, x_149);
lean_dec(x_149);
if (x_150 == 0)
{
lean_object* x_151; uint8_t x_152; 
lean_dec(x_100);
lean_inc(x_148);
x_151 = l_Int_Linear_Poly_denoteExpr(x_96, x_148, x_8, x_9, x_10, x_11, x_99);
x_152 = !lean_is_exclusive(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; uint8_t x_156; 
x_153 = lean_ctor_get(x_151, 0);
x_154 = lean_ctor_get(x_151, 1);
x_155 = lean_int_ediv(x_6, x_104);
lean_dec(x_6);
x_156 = lean_int_dec_le(x_4, x_155);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_157 = lean_mk_string_unchecked("Neg", 3, 3);
x_158 = lean_mk_string_unchecked("neg", 3, 3);
x_159 = l_Lean_Name_mkStr2(x_157, x_158);
x_160 = l_Lean_Level_ofNat(x_5);
x_161 = lean_box(0);
lean_ctor_set_tag(x_151, 1);
lean_ctor_set(x_151, 1, x_161);
lean_ctor_set(x_151, 0, x_160);
x_162 = l_Lean_Expr_const___override(x_159, x_151);
lean_inc(x_3);
x_163 = l_Lean_Name_mkStr1(x_3);
x_164 = l_Lean_Expr_const___override(x_163, x_161);
x_165 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_3);
x_166 = l_Lean_Name_mkStr2(x_3, x_165);
x_167 = l_Lean_Expr_const___override(x_166, x_161);
x_168 = lean_int_neg(x_155);
lean_dec(x_155);
x_169 = l_Int_toNat(x_168);
lean_dec(x_168);
x_170 = l_Lean_instToExprInt_mkNat(x_169);
x_171 = l_Lean_mkApp3(x_162, x_164, x_167, x_170);
x_36 = x_102;
x_37 = x_153;
x_38 = x_104;
x_39 = x_154;
x_40 = x_101;
x_41 = x_148;
x_42 = x_171;
goto block_95;
}
else
{
lean_object* x_172; lean_object* x_173; 
lean_free_object(x_151);
x_172 = l_Int_toNat(x_155);
lean_dec(x_155);
x_173 = l_Lean_instToExprInt_mkNat(x_172);
x_36 = x_102;
x_37 = x_153;
x_38 = x_104;
x_39 = x_154;
x_40 = x_101;
x_41 = x_148;
x_42 = x_173;
goto block_95;
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; 
x_174 = lean_ctor_get(x_151, 0);
x_175 = lean_ctor_get(x_151, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_151);
x_176 = lean_int_ediv(x_6, x_104);
lean_dec(x_6);
x_177 = lean_int_dec_le(x_4, x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_178 = lean_mk_string_unchecked("Neg", 3, 3);
x_179 = lean_mk_string_unchecked("neg", 3, 3);
x_180 = l_Lean_Name_mkStr2(x_178, x_179);
x_181 = l_Lean_Level_ofNat(x_5);
x_182 = lean_box(0);
x_183 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_183, 0, x_181);
lean_ctor_set(x_183, 1, x_182);
x_184 = l_Lean_Expr_const___override(x_180, x_183);
lean_inc(x_3);
x_185 = l_Lean_Name_mkStr1(x_3);
x_186 = l_Lean_Expr_const___override(x_185, x_182);
x_187 = lean_mk_string_unchecked("instNegInt", 10, 10);
lean_inc(x_3);
x_188 = l_Lean_Name_mkStr2(x_3, x_187);
x_189 = l_Lean_Expr_const___override(x_188, x_182);
x_190 = lean_int_neg(x_176);
lean_dec(x_176);
x_191 = l_Int_toNat(x_190);
lean_dec(x_190);
x_192 = l_Lean_instToExprInt_mkNat(x_191);
x_193 = l_Lean_mkApp3(x_184, x_186, x_189, x_192);
x_36 = x_102;
x_37 = x_174;
x_38 = x_104;
x_39 = x_175;
x_40 = x_101;
x_41 = x_148;
x_42 = x_193;
goto block_95;
}
else
{
lean_object* x_194; lean_object* x_195; 
x_194 = l_Int_toNat(x_176);
lean_dec(x_176);
x_195 = l_Lean_instToExprInt_mkNat(x_194);
x_36 = x_102;
x_37 = x_174;
x_38 = x_104;
x_39 = x_175;
x_40 = x_101;
x_41 = x_148;
x_42 = x_195;
goto block_95;
}
}
}
else
{
lean_object* x_196; lean_object* x_197; 
lean_dec(x_148);
lean_dec(x_104);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_96);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_196 = lean_box(0);
if (lean_is_scalar(x_100)) {
 x_197 = lean_alloc_ctor(0, 2, 0);
} else {
 x_197 = x_100;
}
lean_ctor_set(x_197, 0, x_196);
lean_ctor_set(x_197, 1, x_99);
return x_197;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_7 = l_Lean_Meta_Simp_Arith_Int_dvdCnstr_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = lean_ctor_get(x_8, 0);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_7);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_18 = lean_ctor_get(x_7, 1);
x_19 = lean_ctor_get(x_7, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_to_int(x_23);
x_25 = lean_int_dec_eq(x_20, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_free_object(x_7);
x_26 = l_Lean_instInhabitedExpr;
x_27 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed), 12, 6);
lean_closure_set(x_28, 0, x_26);
lean_closure_set(x_28, 1, x_21);
lean_closure_set(x_28, 2, x_27);
lean_closure_set(x_28, 3, x_24);
lean_closure_set(x_28, 4, x_23);
lean_closure_set(x_28, 5, x_20);
x_29 = l_Lean_Name_mkStr1(x_27);
x_30 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_22, x_29, x_28, x_2, x_3, x_4, x_5, x_18);
return x_30;
}
else
{
lean_object* x_31; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_31 = lean_box(0);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_ctor_get(x_16, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_dec(x_16);
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_nat_to_int(x_36);
x_38 = lean_int_dec_eq(x_33, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = l_Lean_instInhabitedExpr;
x_40 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_40);
x_41 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed), 12, 6);
lean_closure_set(x_41, 0, x_39);
lean_closure_set(x_41, 1, x_34);
lean_closure_set(x_41, 2, x_40);
lean_closure_set(x_41, 3, x_37);
lean_closure_set(x_41, 4, x_36);
lean_closure_set(x_41, 5, x_33);
x_42 = l_Lean_Name_mkStr1(x_40);
x_43 = l_Lean_Meta_Simp_Arith_withAbstractAtoms(x_35, x_42, x_41, x_2, x_3, x_4, x_5, x_32);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_32);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_46 = !lean_is_exclusive(x_7);
if (x_46 == 0)
{
return x_7;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_7, 0);
x_48 = lean_ctor_get(x_7, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_7);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Simp_Arith_Int_simpDvd_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_instInhabitedExpr;
x_4 = lean_array_get(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_Simp_Arith_Int_toLinearExpr(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_9, 0);
x_13 = lean_ctor_get(x_9, 1);
x_14 = l_Int_Linear_Expr_norm(x_12);
lean_inc(x_14);
x_15 = l_Int_Linear_Poly_toExpr(x_14);
x_16 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_12, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_free_object(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_13);
x_17 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_13, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_20, 0, x_13);
x_21 = lean_mk_string_unchecked("Int", 3, 3);
x_22 = lean_mk_string_unchecked("Linear", 6, 6);
x_23 = lean_mk_string_unchecked("Expr", 4, 4);
x_24 = lean_mk_string_unchecked("eq_of_norm_eq", 13, 13);
lean_inc(x_14);
x_25 = l_Int_Linear_Poly_denoteExpr(x_20, x_14, x_2, x_3, x_4, x_5, x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_28, x_29);
x_31 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_12);
x_32 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_14);
x_33 = l_Lean_reflBoolTrue;
x_34 = l_Lean_mkApp4(x_30, x_18, x_31, x_32, x_33);
lean_inc(x_27);
x_35 = l_Lean_mkIntEq(x_1, x_27);
x_36 = l_Lean_Meta_mkExpectedPropHint(x_34, x_35);
lean_ctor_set(x_9, 1, x_36);
lean_ctor_set(x_9, 0, x_27);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_9);
lean_ctor_set(x_25, 0, x_37);
return x_25;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_38 = lean_ctor_get(x_25, 0);
x_39 = lean_ctor_get(x_25, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_25);
x_40 = l_Lean_Name_mkStr4(x_21, x_22, x_23, x_24);
x_41 = lean_box(0);
x_42 = l_Lean_Expr_const___override(x_40, x_41);
x_43 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_12);
x_44 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_14);
x_45 = l_Lean_reflBoolTrue;
x_46 = l_Lean_mkApp4(x_42, x_18, x_43, x_44, x_45);
lean_inc(x_38);
x_47 = l_Lean_mkIntEq(x_1, x_38);
x_48 = l_Lean_Meta_mkExpectedPropHint(x_46, x_47);
lean_ctor_set(x_9, 1, x_48);
lean_ctor_set(x_9, 0, x_38);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_9);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_39);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_17);
if (x_51 == 0)
{
return x_17;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_17, 0);
x_53 = lean_ctor_get(x_17, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_17);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; 
lean_dec(x_14);
lean_free_object(x_9);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = lean_box(0);
lean_ctor_set(x_7, 0, x_55);
return x_7;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_56 = lean_ctor_get(x_7, 1);
x_57 = lean_ctor_get(x_9, 0);
x_58 = lean_ctor_get(x_9, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_9);
x_59 = l_Int_Linear_Expr_norm(x_57);
lean_inc(x_59);
x_60 = l_Int_Linear_Poly_toExpr(x_59);
x_61 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_57, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
lean_free_object(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_58);
x_62 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_58, x_2, x_3, x_4, x_5, x_56);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_65, 0, x_58);
x_66 = lean_mk_string_unchecked("Int", 3, 3);
x_67 = lean_mk_string_unchecked("Linear", 6, 6);
x_68 = lean_mk_string_unchecked("Expr", 4, 4);
x_69 = lean_mk_string_unchecked("eq_of_norm_eq", 13, 13);
lean_inc(x_59);
x_70 = l_Int_Linear_Poly_denoteExpr(x_65, x_59, x_2, x_3, x_4, x_5, x_64);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_73 = x_70;
} else {
 lean_dec_ref(x_70);
 x_73 = lean_box(0);
}
x_74 = l_Lean_Name_mkStr4(x_66, x_67, x_68, x_69);
x_75 = lean_box(0);
x_76 = l_Lean_Expr_const___override(x_74, x_75);
x_77 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_57);
x_78 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_59);
x_79 = l_Lean_reflBoolTrue;
x_80 = l_Lean_mkApp4(x_76, x_63, x_77, x_78, x_79);
lean_inc(x_71);
x_81 = l_Lean_mkIntEq(x_1, x_71);
x_82 = l_Lean_Meta_mkExpectedPropHint(x_80, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
if (lean_is_scalar(x_73)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_73;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_72);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = lean_ctor_get(x_62, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_62, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_88 = x_62;
} else {
 lean_dec_ref(x_62);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_object* x_90; 
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_box(0);
lean_ctor_set(x_7, 0, x_90);
return x_7;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_91 = lean_ctor_get(x_7, 0);
x_92 = lean_ctor_get(x_7, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_7);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = l_Int_Linear_Expr_norm(x_93);
lean_inc(x_96);
x_97 = l_Int_Linear_Poly_toExpr(x_96);
x_98 = l___private_Init_Data_Int_Linear_0__Int_Linear_beqExpr____x40_Init_Data_Int_Linear___hyg_133_(x_93, x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_94);
x_99 = l_Lean_Meta_Simp_Arith_Int_toContextExpr(x_94, x_2, x_3, x_4, x_5, x_92);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed), 2, 1);
lean_closure_set(x_102, 0, x_94);
x_103 = lean_mk_string_unchecked("Int", 3, 3);
x_104 = lean_mk_string_unchecked("Linear", 6, 6);
x_105 = lean_mk_string_unchecked("Expr", 4, 4);
x_106 = lean_mk_string_unchecked("eq_of_norm_eq", 13, 13);
lean_inc(x_96);
x_107 = l_Int_Linear_Poly_denoteExpr(x_102, x_96, x_2, x_3, x_4, x_5, x_101);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
x_111 = l_Lean_Name_mkStr4(x_103, x_104, x_105, x_106);
x_112 = lean_box(0);
x_113 = l_Lean_Expr_const___override(x_111, x_112);
x_114 = l_Lean_Meta_Simp_Arith_Int_ofLinearExpr(x_93);
x_115 = l_Lean_Meta_Simp_Arith_Int_ofPoly(x_96);
x_116 = l_Lean_reflBoolTrue;
x_117 = l_Lean_mkApp4(x_113, x_100, x_114, x_115, x_116);
lean_inc(x_108);
x_118 = l_Lean_mkIntEq(x_1, x_108);
x_119 = l_Lean_Meta_mkExpectedPropHint(x_117, x_118);
if (lean_is_scalar(x_95)) {
 x_120 = lean_alloc_ctor(0, 2, 0);
} else {
 x_120 = x_95;
}
lean_ctor_set(x_120, 0, x_108);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
if (lean_is_scalar(x_110)) {
 x_122 = lean_alloc_ctor(0, 2, 0);
} else {
 x_122 = x_110;
}
lean_ctor_set(x_122, 0, x_121);
lean_ctor_set(x_122, 1, x_109);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_123 = lean_ctor_get(x_99, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_99, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_125 = x_99;
} else {
 lean_dec_ref(x_99);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_127 = lean_box(0);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_92);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_7);
if (x_129 == 0)
{
return x_7;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_7, 0);
x_131 = lean_ctor_get(x_7, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_7);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Arith_Int_simpExpr_x3f___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Arith_Int_Simp(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Simp_Arith_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Arith_Int_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
