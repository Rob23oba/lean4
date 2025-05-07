// Lean compiler output
// Module: Lean.Meta.DiscrTreeTypes
// Imports: Lean.Expr Lean.ToExpr
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Lean_mkNatLit(lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instHashableKey;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instBEqKey;
lean_object* lean_nat_to_int(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_356____boxed(lean_object*, lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToExprKey;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_356_(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34_(lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102____boxed(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instReprKey;
static lean_object* _init_l_Lean_Meta_DiscrTree_instInhabitedKey() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_1, 1);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_name_eq(x_3, x_5);
if (x_7 == 0)
{
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_eq(x_4, x_6);
return x_8;
}
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
return x_10;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_11, x_13);
if (x_15 == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_eq(x_12, x_14);
return x_16;
}
}
else
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_1, 0);
x_20 = lean_ctor_get(x_2, 0);
x_21 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34_(x_19, x_20);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
return x_27;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_box(1);
x_29 = lean_unbox(x_28);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
return x_31;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_box(1);
x_33 = lean_unbox(x_32);
return x_33;
}
else
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_box(0);
x_35 = lean_unbox(x_34);
return x_35;
}
}
default: 
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_1, 0);
x_37 = lean_ctor_get(x_1, 1);
x_38 = lean_ctor_get(x_1, 2);
x_39 = lean_ctor_get(x_2, 0);
x_40 = lean_ctor_get(x_2, 1);
x_41 = lean_ctor_get(x_2, 2);
x_42 = lean_name_eq(x_36, x_39);
if (x_42 == 0)
{
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_eq(x_37, x_40);
if (x_43 == 0)
{
return x_43;
}
else
{
uint8_t x_44; 
x_44 = lean_nat_dec_eq(x_38, x_41);
return x_44;
}
}
}
else
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_box(0);
x_46 = lean_unbox(x_45);
return x_46;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instBEqKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_beqKey____x40_Lean_Meta_DiscrTreeTypes___hyg_102____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_356_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_51; uint8_t x_52; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_32 = x_1;
} else {
 lean_dec_ref(x_1);
 x_32 = lean_box(0);
}
x_51 = lean_unsigned_to_nat(1024u);
x_52 = lean_nat_dec_le(x_51, x_2);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_to_int(x_53);
x_33 = x_54;
goto block_50;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_to_int(x_55);
x_33 = x_56;
goto block_50;
}
block_50:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_34 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.Key.const", 29, 29);
x_35 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_box(1);
if (lean_is_scalar(x_32)) {
 x_37 = lean_alloc_ctor(5, 2, 0);
} else {
 x_37 = x_32;
 lean_ctor_set_tag(x_37, 5);
}
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_unsigned_to_nat(1024u);
x_39 = l_Lean_Name_reprPrec(x_30, x_38);
x_40 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
x_42 = l___private_Init_Data_Repr_0__Nat_reprFast(x_31);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_45, 0, x_33);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_47, 0, x_45);
x_48 = lean_unbox(x_46);
lean_ctor_set_uint8(x_47, sizeof(void*)*1, x_48);
x_49 = l_Repr_addAppParen(x_47, x_2);
return x_49;
}
}
case 1:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_78; uint8_t x_79; 
x_57 = lean_ctor_get(x_1, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_59 = x_1;
} else {
 lean_dec_ref(x_1);
 x_59 = lean_box(0);
}
x_78 = lean_unsigned_to_nat(1024u);
x_79 = lean_nat_dec_le(x_78, x_2);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_nat_to_int(x_80);
x_60 = x_81;
goto block_77;
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_to_int(x_82);
x_60 = x_83;
goto block_77;
}
block_77:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; 
x_61 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.Key.fvar", 28, 28);
x_62 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_box(1);
if (lean_is_scalar(x_59)) {
 x_64 = lean_alloc_ctor(5, 2, 0);
} else {
 x_64 = x_59;
 lean_ctor_set_tag(x_64, 5);
}
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_unsigned_to_nat(1024u);
x_66 = l_Lean_Name_reprPrec(x_57, x_65);
x_67 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_63);
x_69 = l___private_Init_Data_Repr_0__Nat_reprFast(x_58);
x_70 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_70, 0, x_69);
x_71 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_72, 0, x_60);
lean_ctor_set(x_72, 1, x_71);
x_73 = lean_box(0);
x_74 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_74, 0, x_72);
x_75 = lean_unbox(x_73);
lean_ctor_set_uint8(x_74, sizeof(void*)*1, x_75);
x_76 = l_Repr_addAppParen(x_74, x_2);
return x_76;
}
}
case 2:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_100; uint8_t x_101; 
x_84 = lean_ctor_get(x_1, 0);
lean_inc(x_84);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_85 = x_1;
} else {
 lean_dec_ref(x_1);
 x_85 = lean_box(0);
}
x_100 = lean_unsigned_to_nat(1024u);
x_101 = lean_nat_dec_le(x_100, x_2);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_unsigned_to_nat(2u);
x_103 = lean_nat_to_int(x_102);
x_86 = x_103;
goto block_99;
}
else
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_unsigned_to_nat(1u);
x_105 = lean_nat_to_int(x_104);
x_86 = x_105;
goto block_99;
}
block_99:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; 
x_87 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.Key.lit", 27, 27);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(3, 1, 0);
} else {
 x_88 = x_85;
 lean_ctor_set_tag(x_88, 3);
}
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_box(1);
x_90 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
x_91 = lean_unsigned_to_nat(1024u);
x_92 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(x_84, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_94, 0, x_86);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_box(0);
x_96 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_96, 0, x_94);
x_97 = lean_unbox(x_95);
lean_ctor_set_uint8(x_96, sizeof(void*)*1, x_97);
x_98 = l_Repr_addAppParen(x_96, x_2);
return x_98;
}
}
case 3:
{
lean_object* x_106; uint8_t x_107; 
x_106 = lean_unsigned_to_nat(1024u);
x_107 = lean_nat_dec_le(x_106, x_2);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_unsigned_to_nat(2u);
x_109 = lean_nat_to_int(x_108);
x_21 = x_109;
goto block_29;
}
else
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_nat_to_int(x_110);
x_21 = x_111;
goto block_29;
}
}
case 4:
{
lean_object* x_112; uint8_t x_113; 
x_112 = lean_unsigned_to_nat(1024u);
x_113 = lean_nat_dec_le(x_112, x_2);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; 
x_114 = lean_unsigned_to_nat(2u);
x_115 = lean_nat_to_int(x_114);
x_12 = x_115;
goto block_20;
}
else
{
lean_object* x_116; lean_object* x_117; 
x_116 = lean_unsigned_to_nat(1u);
x_117 = lean_nat_to_int(x_116);
x_12 = x_117;
goto block_20;
}
}
case 5:
{
lean_object* x_118; uint8_t x_119; 
x_118 = lean_unsigned_to_nat(1024u);
x_119 = lean_nat_dec_le(x_118, x_2);
if (x_119 == 0)
{
lean_object* x_120; lean_object* x_121; 
x_120 = lean_unsigned_to_nat(2u);
x_121 = lean_nat_to_int(x_120);
x_3 = x_121;
goto block_11;
}
else
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_unsigned_to_nat(1u);
x_123 = lean_nat_to_int(x_122);
x_3 = x_123;
goto block_11;
}
}
default: 
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_149; uint8_t x_150; 
x_124 = lean_ctor_get(x_1, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_1, 1);
lean_inc(x_125);
x_126 = lean_ctor_get(x_1, 2);
lean_inc(x_126);
lean_dec(x_1);
x_149 = lean_unsigned_to_nat(1024u);
x_150 = lean_nat_dec_le(x_149, x_2);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_unsigned_to_nat(2u);
x_152 = lean_nat_to_int(x_151);
x_127 = x_152;
goto block_148;
}
else
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_nat_to_int(x_153);
x_127 = x_154;
goto block_148;
}
block_148:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; 
x_128 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.Key.proj", 28, 28);
x_129 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_box(1);
x_131 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_unsigned_to_nat(1024u);
x_133 = l_Lean_Name_reprPrec(x_124, x_132);
x_134 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
x_136 = l___private_Init_Data_Repr_0__Nat_reprFast(x_125);
x_137 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_137, 0, x_136);
x_138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_137);
x_139 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_130);
x_140 = l___private_Init_Data_Repr_0__Nat_reprFast(x_126);
x_141 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_141, 0, x_140);
x_142 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_143, 0, x_127);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_box(0);
x_145 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_145, 0, x_143);
x_146 = lean_unbox(x_144);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_146);
x_147 = l_Repr_addAppParen(x_145, x_2);
return x_147;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.Key.arrow", 29, 29);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.Key.other", 29, 29);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.Key.star", 28, 28);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_356____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_356_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instReprKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_DiscrTreeTypes_0__Lean_Meta_DiscrTree_reprKey____x40_Lean_Meta_DiscrTreeTypes___hyg_356____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint64_t x_5; uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_unsigned_to_nat(5237u);
x_5 = lean_uint64_of_nat(x_4);
x_6 = l_Lean_Name_hash___override(x_2);
x_7 = lean_uint64_of_nat(x_3);
x_8 = lean_uint64_mix_hash(x_6, x_7);
x_9 = lean_uint64_mix_hash(x_5, x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_ctor_get(x_1, 1);
x_12 = lean_unsigned_to_nat(3541u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_10);
x_15 = lean_uint64_of_nat(x_11);
x_16 = lean_uint64_mix_hash(x_14, x_15);
x_17 = lean_uint64_mix_hash(x_13, x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_unsigned_to_nat(1879u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = l_Lean_Literal_hash(x_18);
x_22 = lean_uint64_mix_hash(x_20, x_21);
return x_22;
}
case 3:
{
lean_object* x_23; uint64_t x_24; 
x_23 = lean_unsigned_to_nat(7883u);
x_24 = lean_uint64_of_nat(x_23);
return x_24;
}
case 4:
{
lean_object* x_25; uint64_t x_26; 
x_25 = lean_unsigned_to_nat(2411u);
x_26 = lean_uint64_of_nat(x_25);
return x_26;
}
case 5:
{
lean_object* x_27; uint64_t x_28; 
x_27 = lean_unsigned_to_nat(17u);
x_28 = lean_uint64_of_nat(x_27);
return x_28;
}
default: 
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; 
x_29 = lean_ctor_get(x_1, 0);
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 2);
x_32 = lean_uint64_of_nat(x_31);
x_33 = l_Lean_Name_hash___override(x_29);
x_34 = lean_uint64_of_nat(x_30);
x_35 = lean_uint64_mix_hash(x_33, x_34);
x_36 = lean_uint64_mix_hash(x_32, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_Key_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_Key_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instHashableKey() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_Key_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_instToExprKey___lam__0(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
x_5 = lean_mk_string_unchecked("Meta", 4, 4);
x_6 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_7 = lean_mk_string_unchecked("Key", 3, 3);
x_8 = lean_mk_string_unchecked("const", 5, 5);
x_9 = l_Lean_Name_mkStr5(x_4, x_5, x_6, x_7, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_const___override(x_9, x_10);
x_12 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_2);
x_13 = l_Lean_mkNatLit(x_3);
x_14 = l_Lean_mkAppB(x_11, x_12, x_13);
return x_14;
}
case 1:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_mk_string_unchecked("Lean", 4, 4);
x_18 = lean_mk_string_unchecked("Meta", 4, 4);
x_19 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_20 = lean_mk_string_unchecked("Key", 3, 3);
x_21 = lean_mk_string_unchecked("fvar", 4, 4);
lean_inc(x_17);
x_22 = l_Lean_Name_mkStr5(x_17, x_18, x_19, x_20, x_21);
x_23 = lean_box(0);
x_24 = l_Lean_Expr_const___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("FVarId", 6, 6);
x_26 = lean_mk_string_unchecked("mk", 2, 2);
x_27 = l_Lean_Name_mkStr3(x_17, x_25, x_26);
x_28 = l_Lean_Expr_const___override(x_27, x_23);
x_29 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_15);
x_30 = l_Lean_Expr_app___override(x_28, x_29);
x_31 = l_Lean_mkNatLit(x_16);
x_32 = l_Lean_mkAppB(x_24, x_30, x_31);
return x_32;
}
case 2:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_mk_string_unchecked("Lean", 4, 4);
x_35 = lean_mk_string_unchecked("Meta", 4, 4);
x_36 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_37 = lean_mk_string_unchecked("Key", 3, 3);
x_38 = lean_mk_string_unchecked("lit", 3, 3);
lean_inc(x_34);
x_39 = l_Lean_Name_mkStr5(x_34, x_35, x_36, x_37, x_38);
x_40 = lean_box(0);
x_41 = l_Lean_Expr_const___override(x_39, x_40);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_42 = lean_mk_string_unchecked("Literal", 7, 7);
x_43 = lean_mk_string_unchecked("natVal", 6, 6);
x_44 = l_Lean_Name_mkStr3(x_34, x_42, x_43);
x_45 = l_Lean_Expr_const___override(x_44, x_40);
x_46 = l_Lean_Expr_lit___override(x_33);
x_47 = l_Lean_Expr_app___override(x_45, x_46);
x_48 = l_Lean_Expr_app___override(x_41, x_47);
return x_48;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_49 = lean_mk_string_unchecked("Literal", 7, 7);
x_50 = lean_mk_string_unchecked("strVal", 6, 6);
x_51 = l_Lean_Name_mkStr3(x_34, x_49, x_50);
x_52 = l_Lean_Expr_const___override(x_51, x_40);
x_53 = l_Lean_Expr_lit___override(x_33);
x_54 = l_Lean_Expr_app___override(x_52, x_53);
x_55 = l_Lean_Expr_app___override(x_41, x_54);
return x_55;
}
}
case 3:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_mk_string_unchecked("Lean", 4, 4);
x_57 = lean_mk_string_unchecked("Meta", 4, 4);
x_58 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_59 = lean_mk_string_unchecked("Key", 3, 3);
x_60 = lean_mk_string_unchecked("star", 4, 4);
x_61 = l_Lean_Name_mkStr5(x_56, x_57, x_58, x_59, x_60);
x_62 = lean_box(0);
x_63 = l_Lean_Expr_const___override(x_61, x_62);
return x_63;
}
case 4:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_64 = lean_mk_string_unchecked("Lean", 4, 4);
x_65 = lean_mk_string_unchecked("Meta", 4, 4);
x_66 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_67 = lean_mk_string_unchecked("Key", 3, 3);
x_68 = lean_mk_string_unchecked("other", 5, 5);
x_69 = l_Lean_Name_mkStr5(x_64, x_65, x_66, x_67, x_68);
x_70 = lean_box(0);
x_71 = l_Lean_Expr_const___override(x_69, x_70);
return x_71;
}
case 5:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_72 = lean_mk_string_unchecked("Lean", 4, 4);
x_73 = lean_mk_string_unchecked("Meta", 4, 4);
x_74 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_75 = lean_mk_string_unchecked("Key", 3, 3);
x_76 = lean_mk_string_unchecked("arrow", 5, 5);
x_77 = l_Lean_Name_mkStr5(x_72, x_73, x_74, x_75, x_76);
x_78 = lean_box(0);
x_79 = l_Lean_Expr_const___override(x_77, x_78);
return x_79;
}
default: 
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_80 = lean_ctor_get(x_1, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_1, 1);
lean_inc(x_81);
x_82 = lean_ctor_get(x_1, 2);
lean_inc(x_82);
lean_dec(x_1);
x_83 = lean_mk_string_unchecked("Lean", 4, 4);
x_84 = lean_mk_string_unchecked("Meta", 4, 4);
x_85 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_86 = lean_mk_string_unchecked("Key", 3, 3);
x_87 = lean_mk_string_unchecked("proj", 4, 4);
x_88 = l_Lean_Name_mkStr5(x_83, x_84, x_85, x_86, x_87);
x_89 = lean_box(0);
x_90 = l_Lean_Expr_const___override(x_88, x_89);
x_91 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_80);
x_92 = l_Lean_mkNatLit(x_81);
x_93 = l_Lean_mkNatLit(x_82);
x_94 = l_Lean_mkApp3(x_90, x_91, x_92, x_93);
return x_94;
}
}
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_instToExprKey() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_DiscrTree_instToExprKey___lam__0), 1, 0);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Meta", 4, 4);
x_4 = lean_mk_string_unchecked("DiscrTree", 9, 9);
x_5 = lean_mk_string_unchecked("Key", 3, 3);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_ToExpr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_DiscrTreeTypes(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_DiscrTree_instInhabitedKey = _init_l_Lean_Meta_DiscrTree_instInhabitedKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instInhabitedKey);
l_Lean_Meta_DiscrTree_instBEqKey = _init_l_Lean_Meta_DiscrTree_instBEqKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instBEqKey);
l_Lean_Meta_DiscrTree_instReprKey = _init_l_Lean_Meta_DiscrTree_instReprKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instReprKey);
l_Lean_Meta_DiscrTree_instHashableKey = _init_l_Lean_Meta_DiscrTree_instHashableKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instHashableKey);
l_Lean_Meta_DiscrTree_instToExprKey = _init_l_Lean_Meta_DiscrTree_instToExprKey();
lean_mark_persistent(l_Lean_Meta_DiscrTree_instToExprKey);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
