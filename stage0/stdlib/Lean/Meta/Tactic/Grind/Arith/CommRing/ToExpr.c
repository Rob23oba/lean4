// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.ToExpr
// Imports: Init.Grind.CommRing.Poly Lean.ToExpr
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
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly;
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofNullCert(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprMon;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprPower;
lean_object* l_Int_toNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr;
lean_object* l_Lean_instToExprInt_mkNat(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_instToExprNullCert;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPower(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("Power", 5, 5);
x_6 = lean_mk_string_unchecked("mk", 2, 2);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = l_Lean_mkNatLit(x_10);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_mkNatLit(x_12);
x_14 = l_Lean_mkAppB(x_9, x_11, x_13);
return x_14;
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_ofPower), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("Power", 5, 5);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofMon(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("Mon", 3, 3);
x_6 = lean_mk_string_unchecked("unit", 4, 4);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Grind", 5, 5);
x_14 = lean_mk_string_unchecked("CommRing", 8, 8);
x_15 = lean_mk_string_unchecked("Mon", 3, 3);
x_16 = lean_mk_string_unchecked("mult", 4, 4);
x_17 = l_Lean_Name_mkStr5(x_12, x_13, x_14, x_15, x_16);
x_18 = lean_box(0);
x_19 = l_Lean_Expr_const___override(x_17, x_18);
x_20 = l_Lean_Meta_Grind_Arith_CommRing_ofPower(x_10);
x_21 = l_Lean_Meta_Grind_Arith_CommRing_ofMon(x_11);
x_22 = l_Lean_mkAppB(x_19, x_20, x_21);
return x_22;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_ofMon), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("Mon", 3, 3);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofPoly(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Grind", 5, 5);
x_5 = lean_mk_string_unchecked("CommRing", 8, 8);
x_6 = lean_mk_string_unchecked("Poly", 4, 4);
x_7 = lean_mk_string_unchecked("num", 3, 3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_dec_le(x_12, x_2);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_mk_string_unchecked("Neg", 3, 3);
x_15 = lean_mk_string_unchecked("neg", 3, 3);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
x_17 = l_Lean_Level_ofNat(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = l_Lean_Expr_const___override(x_16, x_18);
x_20 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_20);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Expr_const___override(x_21, x_9);
x_23 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_24 = l_Lean_Name_mkStr2(x_20, x_23);
x_25 = l_Lean_Expr_const___override(x_24, x_9);
x_26 = lean_int_neg(x_2);
lean_dec(x_2);
x_27 = l_Int_toNat(x_26);
lean_dec(x_26);
x_28 = l_Lean_instToExprInt_mkNat(x_27);
x_29 = l_Lean_mkApp3(x_19, x_22, x_25, x_28);
x_30 = l_Lean_Expr_app___override(x_10, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Int_toNat(x_2);
lean_dec(x_2);
x_32 = l_Lean_instToExprInt_mkNat(x_31);
x_33 = l_Lean_Expr_app___override(x_10, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_mk_string_unchecked("Lean", 4, 4);
x_38 = lean_mk_string_unchecked("Grind", 5, 5);
x_39 = lean_mk_string_unchecked("CommRing", 8, 8);
x_40 = lean_mk_string_unchecked("Poly", 4, 4);
x_41 = lean_mk_string_unchecked("add", 3, 3);
x_42 = l_Lean_Name_mkStr5(x_37, x_38, x_39, x_40, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Expr_const___override(x_42, x_43);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_nat_to_int(x_50);
x_52 = lean_int_dec_le(x_51, x_34);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_53 = lean_mk_string_unchecked("Neg", 3, 3);
x_54 = lean_mk_string_unchecked("neg", 3, 3);
x_55 = l_Lean_Name_mkStr2(x_53, x_54);
x_56 = l_Lean_Level_ofNat(x_50);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_43);
x_58 = l_Lean_Expr_const___override(x_55, x_57);
x_59 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_59);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = l_Lean_Expr_const___override(x_60, x_43);
x_62 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_63 = l_Lean_Name_mkStr2(x_59, x_62);
x_64 = l_Lean_Expr_const___override(x_63, x_43);
x_65 = lean_int_neg(x_34);
lean_dec(x_34);
x_66 = l_Int_toNat(x_65);
lean_dec(x_65);
x_67 = l_Lean_instToExprInt_mkNat(x_66);
x_68 = l_Lean_mkApp3(x_58, x_61, x_64, x_67);
x_45 = x_68;
goto block_49;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = l_Int_toNat(x_34);
lean_dec(x_34);
x_70 = l_Lean_instToExprInt_mkNat(x_69);
x_45 = x_70;
goto block_49;
}
block_49:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = l_Lean_Meta_Grind_Arith_CommRing_ofMon(x_35);
x_47 = l_Lean_Meta_Grind_Arith_CommRing_ofPoly(x_36);
x_48 = l_Lean_mkApp3(x_44, x_45, x_46, x_47);
return x_48;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_ofPoly), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("Poly", 4, 4);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
lean_dec(x_1);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Grind", 5, 5);
x_5 = lean_mk_string_unchecked("CommRing", 8, 8);
x_6 = lean_mk_string_unchecked("Expr", 4, 4);
x_7 = lean_mk_string_unchecked("num", 3, 3);
x_8 = l_Lean_Name_mkStr5(x_3, x_4, x_5, x_6, x_7);
x_9 = lean_box(0);
x_10 = l_Lean_Expr_const___override(x_8, x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_to_int(x_11);
x_13 = lean_int_dec_le(x_12, x_2);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_14 = lean_mk_string_unchecked("Neg", 3, 3);
x_15 = lean_mk_string_unchecked("neg", 3, 3);
x_16 = l_Lean_Name_mkStr2(x_14, x_15);
x_17 = l_Lean_Level_ofNat(x_11);
x_18 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = l_Lean_Expr_const___override(x_16, x_18);
x_20 = lean_mk_string_unchecked("Int", 3, 3);
lean_inc(x_20);
x_21 = l_Lean_Name_mkStr1(x_20);
x_22 = l_Lean_Expr_const___override(x_21, x_9);
x_23 = lean_mk_string_unchecked("instNegInt", 10, 10);
x_24 = l_Lean_Name_mkStr2(x_20, x_23);
x_25 = l_Lean_Expr_const___override(x_24, x_9);
x_26 = lean_int_neg(x_2);
lean_dec(x_2);
x_27 = l_Int_toNat(x_26);
lean_dec(x_26);
x_28 = l_Lean_instToExprInt_mkNat(x_27);
x_29 = l_Lean_mkApp3(x_19, x_22, x_25, x_28);
x_30 = l_Lean_Expr_app___override(x_10, x_29);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Int_toNat(x_2);
lean_dec(x_2);
x_32 = l_Lean_instToExprInt_mkNat(x_31);
x_33 = l_Lean_Expr_app___override(x_10, x_32);
return x_33;
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_mk_string_unchecked("Lean", 4, 4);
x_36 = lean_mk_string_unchecked("Grind", 5, 5);
x_37 = lean_mk_string_unchecked("CommRing", 8, 8);
x_38 = lean_mk_string_unchecked("Expr", 4, 4);
x_39 = lean_mk_string_unchecked("var", 3, 3);
x_40 = l_Lean_Name_mkStr5(x_35, x_36, x_37, x_38, x_39);
x_41 = lean_box(0);
x_42 = l_Lean_Expr_const___override(x_40, x_41);
x_43 = l_Lean_mkNatLit(x_34);
x_44 = l_Lean_Expr_app___override(x_42, x_43);
return x_44;
}
case 2:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
lean_dec(x_1);
x_46 = lean_mk_string_unchecked("Lean", 4, 4);
x_47 = lean_mk_string_unchecked("Grind", 5, 5);
x_48 = lean_mk_string_unchecked("CommRing", 8, 8);
x_49 = lean_mk_string_unchecked("Expr", 4, 4);
x_50 = lean_mk_string_unchecked("neg", 3, 3);
x_51 = l_Lean_Name_mkStr5(x_46, x_47, x_48, x_49, x_50);
x_52 = lean_box(0);
x_53 = l_Lean_Expr_const___override(x_51, x_52);
x_54 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_45);
x_55 = l_Lean_Expr_app___override(x_53, x_54);
return x_55;
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
lean_dec(x_1);
x_58 = lean_mk_string_unchecked("Lean", 4, 4);
x_59 = lean_mk_string_unchecked("Grind", 5, 5);
x_60 = lean_mk_string_unchecked("CommRing", 8, 8);
x_61 = lean_mk_string_unchecked("Expr", 4, 4);
x_62 = lean_mk_string_unchecked("add", 3, 3);
x_63 = l_Lean_Name_mkStr5(x_58, x_59, x_60, x_61, x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Expr_const___override(x_63, x_64);
x_66 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_56);
x_67 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_57);
x_68 = l_Lean_mkAppB(x_65, x_66, x_67);
return x_68;
}
case 4:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
lean_dec(x_1);
x_71 = lean_mk_string_unchecked("Lean", 4, 4);
x_72 = lean_mk_string_unchecked("Grind", 5, 5);
x_73 = lean_mk_string_unchecked("CommRing", 8, 8);
x_74 = lean_mk_string_unchecked("Expr", 4, 4);
x_75 = lean_mk_string_unchecked("sub", 3, 3);
x_76 = l_Lean_Name_mkStr5(x_71, x_72, x_73, x_74, x_75);
x_77 = lean_box(0);
x_78 = l_Lean_Expr_const___override(x_76, x_77);
x_79 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_69);
x_80 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_70);
x_81 = l_Lean_mkAppB(x_78, x_79, x_80);
return x_81;
}
case 5:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_mk_string_unchecked("Lean", 4, 4);
x_85 = lean_mk_string_unchecked("Grind", 5, 5);
x_86 = lean_mk_string_unchecked("CommRing", 8, 8);
x_87 = lean_mk_string_unchecked("Expr", 4, 4);
x_88 = lean_mk_string_unchecked("mul", 3, 3);
x_89 = l_Lean_Name_mkStr5(x_84, x_85, x_86, x_87, x_88);
x_90 = lean_box(0);
x_91 = l_Lean_Expr_const___override(x_89, x_90);
x_92 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_82);
x_93 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_83);
x_94 = l_Lean_mkAppB(x_91, x_92, x_93);
return x_94;
}
default: 
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
lean_dec(x_1);
x_97 = lean_mk_string_unchecked("Lean", 4, 4);
x_98 = lean_mk_string_unchecked("Grind", 5, 5);
x_99 = lean_mk_string_unchecked("CommRing", 8, 8);
x_100 = lean_mk_string_unchecked("Expr", 4, 4);
x_101 = lean_mk_string_unchecked("pow", 3, 3);
x_102 = l_Lean_Name_mkStr5(x_97, x_98, x_99, x_100, x_101);
x_103 = lean_box(0);
x_104 = l_Lean_Expr_const___override(x_102, x_103);
x_105 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_95);
x_106 = l_Lean_mkNatLit(x_96);
x_107 = l_Lean_mkAppB(x_104, x_105, x_106);
return x_107;
}
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("Expr", 4, 4);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_ofNullCert(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("NullCert", 8, 8);
x_6 = lean_mk_string_unchecked("empty", 5, 5);
x_7 = l_Lean_Name_mkStr5(x_2, x_3, x_4, x_5, x_6);
x_8 = lean_box(0);
x_9 = l_Lean_Expr_const___override(x_7, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Grind", 5, 5);
x_16 = lean_mk_string_unchecked("CommRing", 8, 8);
x_17 = lean_mk_string_unchecked("NullCert", 8, 8);
x_18 = lean_mk_string_unchecked("add", 3, 3);
x_19 = l_Lean_Name_mkStr5(x_14, x_15, x_16, x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Expr_const___override(x_19, x_20);
x_22 = l_Lean_Meta_Grind_Arith_CommRing_ofPoly(x_10);
x_23 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_11);
x_24 = l_Lean_Meta_Grind_Arith_CommRing_ofRingExpr(x_12);
x_25 = l_Lean_Meta_Grind_Arith_CommRing_ofNullCert(x_13);
x_26 = l_Lean_mkApp4(x_21, x_22, x_23, x_24, x_25);
return x_26;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprNullCert() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Arith_CommRing_ofNullCert), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("CommRing", 8, 8);
x_5 = lean_mk_string_unchecked("NullCert", 8, 8);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* initialize_Init_Grind_CommRing_Poly(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_ToExpr(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_CommRing_Poly(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_CommRing_instToExprPower = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPower();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprPower);
l_Lean_Meta_Grind_Arith_CommRing_instToExprMon = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprMon();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprMon);
l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprPoly);
l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprExpr);
l_Lean_Meta_Grind_Arith_CommRing_instToExprNullCert = _init_l_Lean_Meta_Grind_Arith_CommRing_instToExprNullCert();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_CommRing_instToExprNullCert);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
