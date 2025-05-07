// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Offset.Proof
// Imports: Init.Grind.Offset Init.Grind.Lemmas Lean.Meta.Tactic.Grind.Types
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqTrueProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkOfNegEqFalse(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(lean_object*);
lean_object* l_Lean_mkApp7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkTrans(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN___boxed(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_rfl__true;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkOfNegEqFalse___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkUnsatProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_get_x21___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqFalseProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_outOfBounds___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqTrueProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkUnsatProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Int_toNat(lean_object*);
uint8_t lean_int_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqFalseProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkTrans___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* l_Lean_mkApp5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Grind_Arith_Offset_rfl__true() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_mk_string_unchecked("Lean", 4, 4);
x_2 = lean_mk_string_unchecked("Grind", 5, 5);
x_3 = lean_mk_string_unchecked("rfl_true", 8, 8);
x_4 = l_Lean_Name_mkStr3(x_1, x_2, x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_nat_to_int(x_2);
x_4 = lean_int_dec_le(x_3, x_1);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_6 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.Arith.Offset.Proof.0.Lean.Meta.Grind.Arith.Offset.toExprN", 89, 89);
x_7 = lean_unsigned_to_nat(20u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_mk_string_unchecked("assertion violation: n >= 0\n  ", 30, 30);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Int_toNat(x_1);
x_13 = l_Lean_mkNatLit(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_nat_dec_lt(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkTrans(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_141; uint8_t x_146; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_3, 2);
lean_inc(x_10);
if (lean_is_exclusive(x_3)) {
 lean_ctor_release(x_3, 0);
 lean_ctor_release(x_3, 1);
 lean_ctor_release(x_3, 2);
 x_11 = x_3;
} else {
 lean_dec_ref(x_3);
 x_11 = lean_box(0);
}
x_134 = l_Lean_instInhabitedExpr;
x_146 = l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(x_1, x_5);
if (x_146 == 0)
{
lean_object* x_147; 
x_147 = l_outOfBounds___redArg(x_134);
x_141 = x_147;
goto block_145;
}
else
{
lean_object* x_148; 
lean_inc(x_1);
x_148 = l_Lean_PersistentArray_get_x21___redArg(x_134, x_1, x_5);
x_141 = x_148;
goto block_145;
}
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_int_add(x_6, x_9);
lean_dec(x_9);
lean_dec(x_6);
if (lean_is_scalar(x_11)) {
 x_14 = lean_alloc_ctor(0, 3, 0);
} else {
 x_14 = x_11;
}
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_13);
lean_ctor_set(x_14, 2, x_12);
return x_14;
}
block_133:
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_to_int(x_19);
x_21 = lean_int_dec_eq(x_6, x_20);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = lean_int_dec_lt(x_6, x_20);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_6);
x_24 = lean_int_dec_eq(x_9, x_20);
if (x_24 == 0)
{
uint8_t x_25; 
x_25 = lean_int_dec_lt(x_9, x_20);
lean_dec(x_20);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_9);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Grind", 5, 5);
x_29 = lean_mk_string_unchecked("Nat", 3, 3);
x_30 = lean_mk_string_unchecked("ro_ro", 5, 5);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_const___override(x_31, x_32);
x_34 = l_Lean_mkApp7(x_33, x_17, x_16, x_18, x_23, x_26, x_7, x_10);
x_12 = x_34;
goto block_15;
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_int_neg(x_9);
x_36 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_35);
x_37 = lean_int_dec_lt(x_6, x_35);
lean_dec(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_38 = lean_mk_string_unchecked("Lean", 4, 4);
x_39 = lean_mk_string_unchecked("Grind", 5, 5);
x_40 = lean_mk_string_unchecked("Nat", 3, 3);
x_41 = lean_mk_string_unchecked("ro_lo_1", 7, 7);
x_42 = l_Lean_Name_mkStr4(x_38, x_39, x_40, x_41);
x_43 = lean_box(0);
x_44 = l_Lean_Expr_const___override(x_42, x_43);
x_45 = l_Lean_mkApp7(x_44, x_17, x_16, x_18, x_23, x_36, x_7, x_10);
x_12 = x_45;
goto block_15;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_46 = lean_mk_string_unchecked("Lean", 4, 4);
x_47 = lean_mk_string_unchecked("Grind", 5, 5);
x_48 = lean_mk_string_unchecked("Nat", 3, 3);
x_49 = lean_mk_string_unchecked("ro_lo_2", 7, 7);
x_50 = l_Lean_Name_mkStr4(x_46, x_47, x_48, x_49);
x_51 = lean_box(0);
x_52 = l_Lean_Expr_const___override(x_50, x_51);
x_53 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_54 = l_Lean_mkApp8(x_52, x_17, x_16, x_18, x_23, x_36, x_53, x_7, x_10);
x_12 = x_54;
goto block_15;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_20);
x_55 = lean_mk_string_unchecked("Lean", 4, 4);
x_56 = lean_mk_string_unchecked("Grind", 5, 5);
x_57 = lean_mk_string_unchecked("Nat", 3, 3);
x_58 = lean_mk_string_unchecked("ro_le", 5, 5);
x_59 = l_Lean_Name_mkStr4(x_55, x_56, x_57, x_58);
x_60 = lean_box(0);
x_61 = l_Lean_Expr_const___override(x_59, x_60);
x_62 = l_Lean_mkApp6(x_61, x_17, x_16, x_18, x_23, x_7, x_10);
x_12 = x_62;
goto block_15;
}
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_int_neg(x_6);
x_64 = lean_int_dec_eq(x_9, x_20);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = lean_int_dec_lt(x_9, x_20);
lean_dec(x_20);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_66 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_63);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_9);
x_68 = lean_int_dec_lt(x_9, x_63);
lean_dec(x_63);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Grind", 5, 5);
x_71 = lean_mk_string_unchecked("Nat", 3, 3);
x_72 = lean_mk_string_unchecked("lo_ro_2", 7, 7);
x_73 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_72);
x_74 = lean_box(0);
x_75 = l_Lean_Expr_const___override(x_73, x_74);
x_76 = l_Lean_mkApp7(x_75, x_17, x_16, x_18, x_66, x_67, x_7, x_10);
x_12 = x_76;
goto block_15;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_77 = lean_mk_string_unchecked("Lean", 4, 4);
x_78 = lean_mk_string_unchecked("Grind", 5, 5);
x_79 = lean_mk_string_unchecked("Nat", 3, 3);
x_80 = lean_mk_string_unchecked("lo_ro_1", 7, 7);
x_81 = l_Lean_Name_mkStr4(x_77, x_78, x_79, x_80);
x_82 = lean_box(0);
x_83 = l_Lean_Expr_const___override(x_81, x_82);
x_84 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_85 = l_Lean_mkApp8(x_83, x_17, x_16, x_18, x_66, x_67, x_84, x_7, x_10);
x_12 = x_85;
goto block_15;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_86 = lean_int_neg(x_9);
x_87 = lean_mk_string_unchecked("Lean", 4, 4);
x_88 = lean_mk_string_unchecked("Grind", 5, 5);
x_89 = lean_mk_string_unchecked("Nat", 3, 3);
x_90 = lean_mk_string_unchecked("lo_lo", 5, 5);
x_91 = l_Lean_Name_mkStr4(x_87, x_88, x_89, x_90);
x_92 = lean_box(0);
x_93 = l_Lean_Expr_const___override(x_91, x_92);
x_94 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_63);
lean_dec(x_63);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_86);
lean_dec(x_86);
x_96 = l_Lean_mkApp7(x_93, x_17, x_16, x_18, x_94, x_95, x_7, x_10);
x_12 = x_96;
goto block_15;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_20);
x_97 = lean_mk_string_unchecked("Lean", 4, 4);
x_98 = lean_mk_string_unchecked("Grind", 5, 5);
x_99 = lean_mk_string_unchecked("Nat", 3, 3);
x_100 = lean_mk_string_unchecked("lo_le", 5, 5);
x_101 = l_Lean_Name_mkStr4(x_97, x_98, x_99, x_100);
x_102 = lean_box(0);
x_103 = l_Lean_Expr_const___override(x_101, x_102);
x_104 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_63);
lean_dec(x_63);
x_105 = l_Lean_mkApp6(x_103, x_17, x_16, x_18, x_104, x_7, x_10);
x_12 = x_105;
goto block_15;
}
}
}
else
{
uint8_t x_106; 
x_106 = lean_int_dec_eq(x_9, x_20);
if (x_106 == 0)
{
uint8_t x_107; 
x_107 = lean_int_dec_lt(x_20, x_9);
lean_dec(x_20);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_108 = lean_int_neg(x_9);
x_109 = lean_mk_string_unchecked("Lean", 4, 4);
x_110 = lean_mk_string_unchecked("Grind", 5, 5);
x_111 = lean_mk_string_unchecked("Nat", 3, 3);
x_112 = lean_mk_string_unchecked("le_lo", 5, 5);
x_113 = l_Lean_Name_mkStr4(x_109, x_110, x_111, x_112);
x_114 = lean_box(0);
x_115 = l_Lean_Expr_const___override(x_113, x_114);
x_116 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_108);
lean_dec(x_108);
x_117 = l_Lean_mkApp6(x_115, x_17, x_16, x_18, x_116, x_7, x_10);
x_12 = x_117;
goto block_15;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_mk_string_unchecked("Lean", 4, 4);
x_119 = lean_mk_string_unchecked("Grind", 5, 5);
x_120 = lean_mk_string_unchecked("Nat", 3, 3);
x_121 = lean_mk_string_unchecked("le_ro", 5, 5);
x_122 = l_Lean_Name_mkStr4(x_118, x_119, x_120, x_121);
x_123 = lean_box(0);
x_124 = l_Lean_Expr_const___override(x_122, x_123);
x_125 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_9);
x_126 = l_Lean_mkApp6(x_124, x_17, x_16, x_18, x_125, x_7, x_10);
x_12 = x_126;
goto block_15;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_20);
x_127 = lean_mk_string_unchecked("Nat", 3, 3);
x_128 = lean_mk_string_unchecked("le_trans", 8, 8);
x_129 = l_Lean_Name_mkStr2(x_127, x_128);
x_130 = lean_box(0);
x_131 = l_Lean_Expr_const___override(x_129, x_130);
x_132 = l_Lean_mkApp5(x_131, x_17, x_16, x_18, x_7, x_10);
x_12 = x_132;
goto block_15;
}
}
}
block_140:
{
uint8_t x_137; 
x_137 = l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(x_1, x_4);
if (x_137 == 0)
{
lean_object* x_138; 
lean_dec(x_1);
x_138 = l_outOfBounds___redArg(x_134);
x_16 = x_136;
x_17 = x_135;
x_18 = x_138;
goto block_133;
}
else
{
lean_object* x_139; 
x_139 = l_Lean_PersistentArray_get_x21___redArg(x_134, x_1, x_4);
x_16 = x_136;
x_17 = x_135;
x_18 = x_139;
goto block_133;
}
}
block_145:
{
uint8_t x_142; 
x_142 = l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(x_1, x_8);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_8);
x_143 = l_outOfBounds___redArg(x_134);
x_135 = x_141;
x_136 = x_143;
goto block_140;
}
else
{
lean_object* x_144; 
lean_inc(x_1);
x_144 = l_Lean_PersistentArray_get_x21___redArg(x_134, x_1, x_8);
lean_dec(x_8);
x_135 = x_141;
x_136 = x_144;
goto block_140;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkTrans___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_Arith_Offset_mkTrans(x_1, x_2, x_3, x_4);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkOfNegEqFalse(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_51; lean_object* x_52; lean_object* x_58; uint8_t x_59; 
x_51 = l_Lean_instInhabitedExpr;
x_58 = lean_ctor_get(x_2, 0);
x_59 = l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(x_1, x_58);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = l_outOfBounds___redArg(x_51);
x_52 = x_60;
goto block_57;
}
else
{
lean_object* x_61; 
lean_inc(x_1);
x_61 = l_Lean_PersistentArray_get_x21___redArg(x_51, x_1, x_58);
x_52 = x_61;
goto block_57;
}
block_50:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_nat_to_int(x_7);
x_9 = lean_int_dec_eq(x_6, x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_to_int(x_10);
x_12 = lean_int_neg(x_11);
lean_dec(x_11);
x_13 = lean_int_dec_eq(x_6, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = lean_int_dec_lt(x_6, x_8);
lean_dec(x_8);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Grind", 5, 5);
x_17 = lean_mk_string_unchecked("Nat", 3, 3);
x_18 = lean_mk_string_unchecked("of_ro_eq_false", 14, 14);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Expr_const___override(x_19, x_20);
x_22 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_6);
x_23 = l_Lean_mkApp4(x_21, x_4, x_5, x_22, x_3);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_24 = lean_mk_string_unchecked("Lean", 4, 4);
x_25 = lean_mk_string_unchecked("Grind", 5, 5);
x_26 = lean_mk_string_unchecked("Nat", 3, 3);
x_27 = lean_mk_string_unchecked("of_lo_eq_false", 14, 14);
x_28 = l_Lean_Name_mkStr4(x_24, x_25, x_26, x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_28, x_29);
x_31 = lean_int_neg(x_6);
x_32 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_31);
lean_dec(x_31);
x_33 = l_Lean_mkApp4(x_30, x_4, x_5, x_32, x_3);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Grind", 5, 5);
x_36 = lean_mk_string_unchecked("Nat", 3, 3);
x_37 = lean_mk_string_unchecked("of_lo_eq_false_1", 16, 16);
x_38 = l_Lean_Name_mkStr4(x_34, x_35, x_36, x_37);
x_39 = lean_box(0);
x_40 = l_Lean_Expr_const___override(x_38, x_39);
x_41 = l_Lean_mkApp3(x_40, x_4, x_5, x_3);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
x_42 = lean_mk_string_unchecked("Lean", 4, 4);
x_43 = lean_mk_string_unchecked("Grind", 5, 5);
x_44 = lean_mk_string_unchecked("Nat", 3, 3);
x_45 = lean_mk_string_unchecked("of_le_eq_false", 14, 14);
x_46 = l_Lean_Name_mkStr4(x_42, x_43, x_44, x_45);
x_47 = lean_box(0);
x_48 = l_Lean_Expr_const___override(x_46, x_47);
x_49 = l_Lean_mkApp3(x_48, x_4, x_5, x_3);
return x_49;
}
}
block_57:
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_2, 1);
x_54 = l_Lean_Meta_Grind_Arith_Offset_mkTrans___lam__0(x_1, x_53);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_1);
x_55 = l_outOfBounds___redArg(x_51);
x_4 = x_52;
x_5 = x_55;
goto block_50;
}
else
{
lean_object* x_56; 
x_56 = l_Lean_PersistentArray_get_x21___redArg(x_51, x_1, x_53);
x_4 = x_52;
x_5 = x_56;
goto block_50;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkOfNegEqFalse___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_Arith_Offset_mkOfNegEqFalse(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkUnsatProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_nat_to_int(x_28);
x_30 = lean_int_dec_eq(x_3, x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_int_dec_eq(x_5, x_29);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = lean_int_dec_lt(x_3, x_29);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = lean_int_dec_lt(x_29, x_3);
if (x_33 == 0)
{
lean_dec(x_29);
x_7 = x_33;
goto block_27;
}
else
{
uint8_t x_34; 
x_34 = lean_int_dec_lt(x_5, x_29);
lean_dec(x_29);
x_7 = x_34;
goto block_27;
}
}
else
{
uint8_t x_35; 
x_35 = lean_int_dec_lt(x_29, x_5);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = lean_int_dec_lt(x_5, x_29);
lean_dec(x_29);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_37 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_38 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkUnsatProof", 41, 41);
x_39 = lean_unsigned_to_nat(104u);
x_40 = lean_unsigned_to_nat(6u);
x_41 = lean_mk_string_unchecked("assertion violation: kvu < 0\n      ", 35, 35);
x_42 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_37, x_38, x_39, x_40, x_41);
lean_dec(x_41);
lean_dec(x_38);
lean_dec(x_37);
x_43 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_42);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_44 = lean_mk_string_unchecked("Lean", 4, 4);
x_45 = lean_mk_string_unchecked("Grind", 5, 5);
x_46 = lean_mk_string_unchecked("Nat", 3, 3);
x_47 = lean_mk_string_unchecked("unsat_lo_lo", 11, 11);
x_48 = l_Lean_Name_mkStr4(x_44, x_45, x_46, x_47);
x_49 = lean_box(0);
x_50 = l_Lean_Expr_const___override(x_48, x_49);
x_51 = lean_int_neg(x_3);
x_52 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_51);
lean_dec(x_51);
x_53 = lean_int_neg(x_5);
x_54 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_53);
lean_dec(x_53);
x_55 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_56 = l_Lean_mkApp7(x_50, x_1, x_2, x_52, x_54, x_55, x_4, x_6);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_29);
x_57 = lean_mk_string_unchecked("Lean", 4, 4);
x_58 = lean_mk_string_unchecked("Grind", 5, 5);
x_59 = lean_mk_string_unchecked("Nat", 3, 3);
x_60 = lean_mk_string_unchecked("unsat_lo_ro", 11, 11);
x_61 = l_Lean_Name_mkStr4(x_57, x_58, x_59, x_60);
x_62 = lean_box(0);
x_63 = l_Lean_Expr_const___override(x_61, x_62);
x_64 = lean_int_neg(x_3);
x_65 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_64);
lean_dec(x_64);
x_66 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_5);
x_67 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_68 = l_Lean_mkApp7(x_63, x_1, x_2, x_65, x_66, x_67, x_4, x_6);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_29);
x_69 = lean_mk_string_unchecked("Lean", 4, 4);
x_70 = lean_mk_string_unchecked("Grind", 5, 5);
x_71 = lean_mk_string_unchecked("Nat", 3, 3);
x_72 = lean_mk_string_unchecked("unsat_le_lo", 11, 11);
x_73 = l_Lean_Name_mkStr4(x_69, x_70, x_71, x_72);
x_74 = lean_box(0);
x_75 = l_Lean_Expr_const___override(x_73, x_74);
x_76 = lean_int_neg(x_3);
x_77 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_76);
lean_dec(x_76);
x_78 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_79 = l_Lean_mkApp6(x_75, x_2, x_1, x_77, x_78, x_6, x_4);
return x_79;
}
}
else
{
uint8_t x_80; 
x_80 = lean_int_dec_lt(x_5, x_29);
lean_dec(x_29);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_82 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkUnsatProof", 41, 41);
x_83 = lean_unsigned_to_nat(96u);
x_84 = lean_unsigned_to_nat(4u);
x_85 = lean_mk_string_unchecked("assertion violation: kvu < 0\n    ", 33, 33);
x_86 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_81, x_82, x_83, x_84, x_85);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_81);
x_87 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_mk_string_unchecked("Lean", 4, 4);
x_89 = lean_mk_string_unchecked("Grind", 5, 5);
x_90 = lean_mk_string_unchecked("Nat", 3, 3);
x_91 = lean_mk_string_unchecked("unsat_le_lo", 11, 11);
x_92 = l_Lean_Name_mkStr4(x_88, x_89, x_90, x_91);
x_93 = lean_box(0);
x_94 = l_Lean_Expr_const___override(x_92, x_93);
x_95 = lean_int_neg(x_5);
x_96 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_95);
lean_dec(x_95);
x_97 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_98 = l_Lean_mkApp6(x_94, x_1, x_2, x_96, x_97, x_4, x_6);
return x_98;
}
}
block_27:
{
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_9 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkUnsatProof", 41, 41);
x_10 = lean_unsigned_to_nat(107u);
x_11 = lean_unsigned_to_nat(4u);
x_12 = lean_mk_string_unchecked("assertion violation: kuv > 0 && kvu < 0\n    ", 44, 44);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
x_16 = lean_mk_string_unchecked("Grind", 5, 5);
x_17 = lean_mk_string_unchecked("Nat", 3, 3);
x_18 = lean_mk_string_unchecked("unsat_lo_ro", 11, 11);
x_19 = l_Lean_Name_mkStr4(x_15, x_16, x_17, x_18);
x_20 = lean_box(0);
x_21 = l_Lean_Expr_const___override(x_19, x_20);
x_22 = lean_int_neg(x_5);
x_23 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_22);
lean_dec(x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_3);
x_25 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_26 = l_Lean_mkApp7(x_21, x_2, x_1, x_23, x_24, x_25, x_6, x_4);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkUnsatProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Arith_Offset_mkUnsatProof(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqTrueProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_dec_eq(x_3, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_int_dec_lt(x_3, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_int_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_12 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqTrueProof", 51, 51);
x_13 = lean_unsigned_to_nat(133u);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_mk_string_unchecked("assertion violation: k > 0\n    ", 31, 31);
x_16 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_17 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_int_dec_lt(x_7, x_5);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_20 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqTrueProof", 51, 51);
x_21 = lean_unsigned_to_nat(134u);
x_22 = lean_unsigned_to_nat(4u);
x_23 = lean_mk_string_unchecked("assertion violation: k' > 0\n    ", 32, 32);
x_24 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_19, x_20, x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_25 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_26 = lean_mk_string_unchecked("Lean", 4, 4);
x_27 = lean_mk_string_unchecked("Grind", 5, 5);
x_28 = lean_mk_string_unchecked("Nat", 3, 3);
x_29 = lean_mk_string_unchecked("ro_eq_true_of_ro", 16, 16);
x_30 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_29);
x_31 = lean_box(0);
x_32 = l_Lean_Expr_const___override(x_30, x_31);
x_33 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_3);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_5);
x_35 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_36 = l_Lean_mkApp6(x_32, x_1, x_2, x_33, x_34, x_35, x_4);
return x_36;
}
}
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_int_neg(x_3);
x_38 = lean_int_dec_eq(x_5, x_7);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = lean_int_dec_lt(x_5, x_7);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_int_dec_lt(x_7, x_5);
lean_dec(x_7);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_37);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_42 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqTrueProof", 51, 51);
x_43 = lean_unsigned_to_nat(130u);
x_44 = lean_unsigned_to_nat(6u);
x_45 = lean_mk_string_unchecked("assertion violation: k' > 0\n      ", 34, 34);
x_46 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
x_47 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_48 = lean_mk_string_unchecked("Lean", 4, 4);
x_49 = lean_mk_string_unchecked("Grind", 5, 5);
x_50 = lean_mk_string_unchecked("Nat", 3, 3);
x_51 = lean_mk_string_unchecked("ro_eq_true_of_lo", 16, 16);
x_52 = l_Lean_Name_mkStr4(x_48, x_49, x_50, x_51);
x_53 = lean_box(0);
x_54 = l_Lean_Expr_const___override(x_52, x_53);
x_55 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_37);
lean_dec(x_37);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_5);
x_57 = l_Lean_mkApp5(x_54, x_1, x_2, x_55, x_56, x_4);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_7);
x_58 = lean_int_neg(x_5);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_mk_string_unchecked("Grind", 5, 5);
x_61 = lean_mk_string_unchecked("Nat", 3, 3);
x_62 = lean_mk_string_unchecked("lo_eq_true_of_lo", 16, 16);
x_63 = l_Lean_Name_mkStr4(x_59, x_60, x_61, x_62);
x_64 = lean_box(0);
x_65 = l_Lean_Expr_const___override(x_63, x_64);
x_66 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_37);
lean_dec(x_37);
x_67 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_58);
lean_dec(x_58);
x_68 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_69 = l_Lean_mkApp6(x_65, x_1, x_2, x_66, x_67, x_68, x_4);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_7);
x_70 = lean_mk_string_unchecked("Lean", 4, 4);
x_71 = lean_mk_string_unchecked("Grind", 5, 5);
x_72 = lean_mk_string_unchecked("Nat", 3, 3);
x_73 = lean_mk_string_unchecked("le_eq_true_of_lo", 16, 16);
x_74 = l_Lean_Name_mkStr4(x_70, x_71, x_72, x_73);
x_75 = lean_box(0);
x_76 = l_Lean_Expr_const___override(x_74, x_75);
x_77 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_37);
lean_dec(x_37);
x_78 = l_Lean_mkApp4(x_76, x_1, x_2, x_77, x_4);
return x_78;
}
}
}
else
{
uint8_t x_79; 
x_79 = lean_int_dec_eq(x_5, x_7);
if (x_79 == 0)
{
uint8_t x_80; 
x_80 = lean_int_dec_lt(x_7, x_5);
lean_dec(x_7);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_81 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_82 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqTrueProof", 51, 51);
x_83 = lean_unsigned_to_nat(120u);
x_84 = lean_unsigned_to_nat(6u);
x_85 = lean_mk_string_unchecked("assertion violation: k' > 0\n      ", 34, 34);
x_86 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_81, x_82, x_83, x_84, x_85);
lean_dec(x_85);
lean_dec(x_82);
lean_dec(x_81);
x_87 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_86);
return x_87;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_88 = lean_mk_string_unchecked("Lean", 4, 4);
x_89 = lean_mk_string_unchecked("Grind", 5, 5);
x_90 = lean_mk_string_unchecked("Nat", 3, 3);
x_91 = lean_mk_string_unchecked("ro_eq_true_of_le", 16, 16);
x_92 = l_Lean_Name_mkStr4(x_88, x_89, x_90, x_91);
x_93 = lean_box(0);
x_94 = l_Lean_Expr_const___override(x_92, x_93);
x_95 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_5);
x_96 = l_Lean_mkApp4(x_94, x_1, x_2, x_95, x_4);
return x_96;
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_7);
x_97 = lean_mk_string_unchecked("Lean", 4, 4);
x_98 = lean_mk_string_unchecked("Grind", 5, 5);
x_99 = lean_mk_string_unchecked("Nat", 3, 3);
x_100 = lean_mk_string_unchecked("le_eq_true_of_le", 16, 16);
x_101 = l_Lean_Name_mkStr4(x_97, x_98, x_99, x_100);
x_102 = lean_box(0);
x_103 = l_Lean_Expr_const___override(x_101, x_102);
x_104 = l_Lean_mkApp3(x_103, x_1, x_2, x_4);
return x_104;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqTrueProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqTrueProof(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqFalseProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_nat_to_int(x_6);
x_8 = lean_int_dec_eq(x_3, x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_int_dec_lt(x_3, x_7);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = lean_int_dec_lt(x_7, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_12 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqFalseProof", 52, 52);
x_13 = lean_unsigned_to_nat(158u);
x_14 = lean_unsigned_to_nat(4u);
x_15 = lean_mk_string_unchecked("assertion violation: k > 0\n    ", 31, 31);
x_16 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_11, x_12, x_13, x_14, x_15);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
x_17 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_16);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_int_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_20 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqFalseProof", 52, 52);
x_21 = lean_unsigned_to_nat(159u);
x_22 = lean_unsigned_to_nat(4u);
x_23 = lean_mk_string_unchecked("assertion violation: k' < 0\n    ", 32, 32);
x_24 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_19, x_20, x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_25 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_24);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_26 = lean_int_neg(x_5);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Grind", 5, 5);
x_29 = lean_mk_string_unchecked("Nat", 3, 3);
x_30 = lean_mk_string_unchecked("lo_eq_false_of_ro", 17, 17);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_const___override(x_31, x_32);
x_34 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_3);
x_35 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_26);
lean_dec(x_26);
x_36 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_37 = l_Lean_mkApp6(x_33, x_1, x_2, x_34, x_35, x_36, x_4);
return x_37;
}
}
}
else
{
lean_object* x_38; uint8_t x_39; 
x_38 = lean_int_neg(x_3);
x_39 = lean_int_dec_eq(x_5, x_7);
if (x_39 == 0)
{
uint8_t x_40; 
x_40 = lean_int_dec_lt(x_5, x_7);
if (x_40 == 0)
{
uint8_t x_41; 
x_41 = lean_int_dec_lt(x_7, x_5);
lean_dec(x_7);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_38);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_42 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_43 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqFalseProof", 52, 52);
x_44 = lean_unsigned_to_nat(155u);
x_45 = lean_unsigned_to_nat(6u);
x_46 = lean_mk_string_unchecked("assertion violation: k' > 0\n      ", 34, 34);
x_47 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_42, x_43, x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_42);
x_48 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_49 = lean_mk_string_unchecked("Lean", 4, 4);
x_50 = lean_mk_string_unchecked("Grind", 5, 5);
x_51 = lean_mk_string_unchecked("Nat", 3, 3);
x_52 = lean_mk_string_unchecked("ro_eq_false_of_lo", 17, 17);
x_53 = l_Lean_Name_mkStr4(x_49, x_50, x_51, x_52);
x_54 = lean_box(0);
x_55 = l_Lean_Expr_const___override(x_53, x_54);
x_56 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_38);
lean_dec(x_38);
x_57 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_5);
x_58 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_59 = l_Lean_mkApp6(x_55, x_1, x_2, x_56, x_57, x_58, x_4);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_7);
x_60 = lean_int_neg(x_5);
x_61 = lean_mk_string_unchecked("Lean", 4, 4);
x_62 = lean_mk_string_unchecked("Grind", 5, 5);
x_63 = lean_mk_string_unchecked("Nat", 3, 3);
x_64 = lean_mk_string_unchecked("lo_eq_false_of_lo", 17, 17);
x_65 = l_Lean_Name_mkStr4(x_61, x_62, x_63, x_64);
x_66 = lean_box(0);
x_67 = l_Lean_Expr_const___override(x_65, x_66);
x_68 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_38);
lean_dec(x_38);
x_69 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_60);
lean_dec(x_60);
x_70 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_71 = l_Lean_mkApp6(x_67, x_1, x_2, x_68, x_69, x_70, x_4);
return x_71;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_7);
x_72 = lean_mk_string_unchecked("Lean", 4, 4);
x_73 = lean_mk_string_unchecked("Grind", 5, 5);
x_74 = lean_mk_string_unchecked("Nat", 3, 3);
x_75 = lean_mk_string_unchecked("le_eq_false_of_lo", 17, 17);
x_76 = l_Lean_Name_mkStr4(x_72, x_73, x_74, x_75);
x_77 = lean_box(0);
x_78 = l_Lean_Expr_const___override(x_76, x_77);
x_79 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_38);
lean_dec(x_38);
x_80 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_81 = l_Lean_mkApp5(x_78, x_1, x_2, x_79, x_80, x_4);
return x_81;
}
}
}
else
{
uint8_t x_82; 
x_82 = lean_int_dec_lt(x_5, x_7);
lean_dec(x_7);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.Arith.Offset.Proof", 41, 41);
x_84 = lean_mk_string_unchecked("Lean.Meta.Grind.Arith.Offset.mkPropagateEqFalseProof", 52, 52);
x_85 = lean_unsigned_to_nat(144u);
x_86 = lean_unsigned_to_nat(4u);
x_87 = lean_mk_string_unchecked("assertion violation: k' < 0\n    ", 32, 32);
x_88 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_83, x_84, x_85, x_86, x_87);
lean_dec(x_87);
lean_dec(x_84);
lean_dec(x_83);
x_89 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_88);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_90 = lean_int_neg(x_5);
x_91 = lean_mk_string_unchecked("Lean", 4, 4);
x_92 = lean_mk_string_unchecked("Grind", 5, 5);
x_93 = lean_mk_string_unchecked("Nat", 3, 3);
x_94 = lean_mk_string_unchecked("lo_eq_false_of_le", 17, 17);
x_95 = l_Lean_Name_mkStr4(x_91, x_92, x_93, x_94);
x_96 = lean_box(0);
x_97 = l_Lean_Expr_const___override(x_95, x_96);
x_98 = l___private_Lean_Meta_Tactic_Grind_Arith_Offset_Proof_0__Lean_Meta_Grind_Arith_Offset_toExprN(x_90);
lean_dec(x_90);
x_99 = l_Lean_Meta_Grind_Arith_Offset_rfl__true;
x_100 = l_Lean_mkApp5(x_97, x_1, x_2, x_98, x_99, x_4);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqFalseProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Arith_Offset_mkPropagateEqFalseProof(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_3);
return x_6;
}
}
lean_object* initialize_Init_Grind_Offset(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Offset_Proof(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Offset(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_Arith_Offset_rfl__true = _init_l_Lean_Meta_Grind_Arith_Offset_rfl__true();
lean_mark_persistent(l_Lean_Meta_Grind_Arith_Offset_rfl__true);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
