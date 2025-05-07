// Lean compiler output
// Module: Lean.HeadIndex
// Imports: Lean.Expr
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
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_reprHeadIndex____x40_Lean_HeadIndex___hyg_288____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs_go(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_instInhabitedHeadIndex;
LEAN_EXPORT lean_object* l_Lean_instReprHeadIndex;
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_reprHeadIndex____x40_Lean_HeadIndex___hyg_288_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instBEqHeadIndex;
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs_go___boxed(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
lean_object* lean_nat_to_int(lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
uint64_t l_Lean_Literal_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instHashableHeadIndex;
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69____boxed(lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object*);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34_(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_HeadIndex_hash(lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
static lean_object* _init_l_Lean_instInhabitedHeadIndex() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_name_eq(x_8, x_9);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_name_eq(x_13, x_14);
return x_15;
}
else
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
return x_17;
}
}
case 3:
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = lean_ctor_get(x_1, 1);
x_20 = lean_ctor_get(x_2, 0);
x_21 = lean_ctor_get(x_2, 1);
x_22 = lean_name_eq(x_18, x_20);
if (x_22 == 0)
{
return x_22;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_eq(x_19, x_21);
return x_23;
}
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
case 4:
{
if (lean_obj_tag(x_2) == 4)
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_1, 0);
x_27 = lean_ctor_get(x_2, 0);
x_28 = l___private_Lean_Expr_0__Lean_beqLiteral____x40_Lean_Expr___hyg_34_(x_26, x_27);
return x_28;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
return x_30;
}
}
case 5:
{
if (lean_obj_tag(x_2) == 5)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_box(1);
x_32 = lean_unbox(x_31);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
return x_34;
}
}
case 6:
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(1);
x_36 = lean_unbox(x_35);
return x_36;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_box(0);
x_38 = lean_unbox(x_37);
return x_38;
}
}
default: 
{
if (lean_obj_tag(x_2) == 7)
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_box(1);
x_40 = lean_unbox(x_39);
return x_40;
}
else
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_box(0);
x_42 = lean_unbox(x_41);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_instBEqHeadIndex() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_reprHeadIndex____x40_Lean_HeadIndex___hyg_288_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_46; uint8_t x_47; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_31 = x_1;
} else {
 lean_dec_ref(x_1);
 x_31 = lean_box(0);
}
x_46 = lean_unsigned_to_nat(1024u);
x_47 = lean_nat_dec_le(x_46, x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_to_int(x_48);
x_32 = x_49;
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_to_int(x_50);
x_32 = x_51;
goto block_45;
}
block_45:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_33 = lean_mk_string_unchecked("Lean.HeadIndex.fvar", 19, 19);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(3, 1, 0);
} else {
 x_34 = x_31;
 lean_ctor_set_tag(x_34, 3);
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_unsigned_to_nat(1024u);
x_38 = l_Lean_Name_reprPrec(x_30, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = l_Repr_addAppParen(x_42, x_2);
return x_44;
}
}
case 1:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_68; uint8_t x_69; 
x_52 = lean_ctor_get(x_1, 0);
lean_inc(x_52);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_53 = x_1;
} else {
 lean_dec_ref(x_1);
 x_53 = lean_box(0);
}
x_68 = lean_unsigned_to_nat(1024u);
x_69 = lean_nat_dec_le(x_68, x_2);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_to_int(x_70);
x_54 = x_71;
goto block_67;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_nat_to_int(x_72);
x_54 = x_73;
goto block_67;
}
block_67:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; lean_object* x_66; 
x_55 = lean_mk_string_unchecked("Lean.HeadIndex.mvar", 19, 19);
if (lean_is_scalar(x_53)) {
 x_56 = lean_alloc_ctor(3, 1, 0);
} else {
 x_56 = x_53;
 lean_ctor_set_tag(x_56, 3);
}
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_box(1);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_unsigned_to_nat(1024u);
x_60 = l_Lean_Name_reprPrec(x_52, x_59);
x_61 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_62, 0, x_54);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_64, 0, x_62);
x_65 = lean_unbox(x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*1, x_65);
x_66 = l_Repr_addAppParen(x_64, x_2);
return x_66;
}
}
case 2:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_90; uint8_t x_91; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_75 = x_1;
} else {
 lean_dec_ref(x_1);
 x_75 = lean_box(0);
}
x_90 = lean_unsigned_to_nat(1024u);
x_91 = lean_nat_dec_le(x_90, x_2);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_unsigned_to_nat(2u);
x_93 = lean_nat_to_int(x_92);
x_76 = x_93;
goto block_89;
}
else
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_unsigned_to_nat(1u);
x_95 = lean_nat_to_int(x_94);
x_76 = x_95;
goto block_89;
}
block_89:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_77 = lean_mk_string_unchecked("Lean.HeadIndex.const", 20, 20);
if (lean_is_scalar(x_75)) {
 x_78 = lean_alloc_ctor(3, 1, 0);
} else {
 x_78 = x_75;
 lean_ctor_set_tag(x_78, 3);
}
lean_ctor_set(x_78, 0, x_77);
x_79 = lean_box(1);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
x_81 = lean_unsigned_to_nat(1024u);
x_82 = l_Lean_Name_reprPrec(x_74, x_81);
x_83 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_84, 0, x_76);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_86, 0, x_84);
x_87 = lean_unbox(x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*1, x_87);
x_88 = l_Repr_addAppParen(x_86, x_2);
return x_88;
}
}
case 3:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_117; uint8_t x_118; 
x_96 = lean_ctor_get(x_1, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_1, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_98 = x_1;
} else {
 lean_dec_ref(x_1);
 x_98 = lean_box(0);
}
x_117 = lean_unsigned_to_nat(1024u);
x_118 = lean_nat_dec_le(x_117, x_2);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_unsigned_to_nat(2u);
x_120 = lean_nat_to_int(x_119);
x_99 = x_120;
goto block_116;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_to_int(x_121);
x_99 = x_122;
goto block_116;
}
block_116:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
x_100 = lean_mk_string_unchecked("Lean.HeadIndex.proj", 19, 19);
x_101 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_101, 0, x_100);
x_102 = lean_box(1);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(5, 2, 0);
} else {
 x_103 = x_98;
 lean_ctor_set_tag(x_103, 5);
}
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_unsigned_to_nat(1024u);
x_105 = l_Lean_Name_reprPrec(x_96, x_104);
x_106 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_102);
x_108 = l___private_Init_Data_Repr_0__Nat_reprFast(x_97);
x_109 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_111, 0, x_99);
lean_ctor_set(x_111, 1, x_110);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_113, 0, x_111);
x_114 = lean_unbox(x_112);
lean_ctor_set_uint8(x_113, sizeof(void*)*1, x_114);
x_115 = l_Repr_addAppParen(x_113, x_2);
return x_115;
}
}
case 4:
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_139; uint8_t x_140; 
x_123 = lean_ctor_get(x_1, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_124 = x_1;
} else {
 lean_dec_ref(x_1);
 x_124 = lean_box(0);
}
x_139 = lean_unsigned_to_nat(1024u);
x_140 = lean_nat_dec_le(x_139, x_2);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; 
x_141 = lean_unsigned_to_nat(2u);
x_142 = lean_nat_to_int(x_141);
x_125 = x_142;
goto block_138;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_unsigned_to_nat(1u);
x_144 = lean_nat_to_int(x_143);
x_125 = x_144;
goto block_138;
}
block_138:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; 
x_126 = lean_mk_string_unchecked("Lean.HeadIndex.lit", 18, 18);
if (lean_is_scalar(x_124)) {
 x_127 = lean_alloc_ctor(3, 1, 0);
} else {
 x_127 = x_124;
 lean_ctor_set_tag(x_127, 3);
}
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_box(1);
x_129 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_unsigned_to_nat(1024u);
x_131 = l___private_Lean_Expr_0__Lean_reprLiteral____x40_Lean_Expr___hyg_113_(x_123, x_130);
x_132 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_133, 0, x_125);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_135, 0, x_133);
x_136 = lean_unbox(x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*1, x_136);
x_137 = l_Repr_addAppParen(x_135, x_2);
return x_137;
}
}
case 5:
{
lean_object* x_145; uint8_t x_146; 
x_145 = lean_unsigned_to_nat(1024u);
x_146 = lean_nat_dec_le(x_145, x_2);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; 
x_147 = lean_unsigned_to_nat(2u);
x_148 = lean_nat_to_int(x_147);
x_3 = x_148;
goto block_11;
}
else
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_unsigned_to_nat(1u);
x_150 = lean_nat_to_int(x_149);
x_3 = x_150;
goto block_11;
}
}
case 6:
{
lean_object* x_151; uint8_t x_152; 
x_151 = lean_unsigned_to_nat(1024u);
x_152 = lean_nat_dec_le(x_151, x_2);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; 
x_153 = lean_unsigned_to_nat(2u);
x_154 = lean_nat_to_int(x_153);
x_12 = x_154;
goto block_20;
}
else
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_unsigned_to_nat(1u);
x_156 = lean_nat_to_int(x_155);
x_12 = x_156;
goto block_20;
}
}
default: 
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_unsigned_to_nat(1024u);
x_158 = lean_nat_dec_le(x_157, x_2);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_unsigned_to_nat(2u);
x_160 = lean_nat_to_int(x_159);
x_21 = x_160;
goto block_29;
}
else
{
lean_object* x_161; lean_object* x_162; 
x_161 = lean_unsigned_to_nat(1u);
x_162 = lean_nat_to_int(x_161);
x_21 = x_162;
goto block_29;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.HeadIndex.sort", 19, 19);
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
x_13 = lean_mk_string_unchecked("Lean.HeadIndex.lam", 18, 18);
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
x_22 = lean_mk_string_unchecked("Lean.HeadIndex.forallE", 22, 22);
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
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_reprHeadIndex____x40_Lean_HeadIndex___hyg_288____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_HeadIndex_0__Lean_reprHeadIndex____x40_Lean_HeadIndex___hyg_288_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instReprHeadIndex() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_HeadIndex_0__Lean_reprHeadIndex____x40_Lean_HeadIndex___hyg_288____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l_Lean_HeadIndex_hash(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(11u);
x_4 = lean_uint64_of_nat(x_3);
x_5 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_unsigned_to_nat(13u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = l___private_Lean_Expr_0__Lean_hashMVarId____x40_Lean_Expr___hyg_1984_(x_7);
x_11 = lean_uint64_mix_hash(x_9, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_unsigned_to_nat(17u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = l_Lean_Name_hash___override(x_12);
x_16 = lean_uint64_mix_hash(x_14, x_15);
return x_16;
}
case 3:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; 
x_17 = lean_ctor_get(x_1, 0);
x_18 = lean_ctor_get(x_1, 1);
x_19 = lean_unsigned_to_nat(19u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = l_Lean_Name_hash___override(x_17);
x_22 = lean_uint64_of_nat(x_18);
x_23 = lean_uint64_mix_hash(x_21, x_22);
x_24 = lean_uint64_mix_hash(x_20, x_23);
return x_24;
}
case 4:
{
lean_object* x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; 
x_25 = lean_ctor_get(x_1, 0);
x_26 = lean_unsigned_to_nat(23u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = l_Lean_Literal_hash(x_25);
x_29 = lean_uint64_mix_hash(x_27, x_28);
return x_29;
}
case 5:
{
lean_object* x_30; uint64_t x_31; 
x_30 = lean_unsigned_to_nat(29u);
x_31 = lean_uint64_of_nat(x_30);
return x_31;
}
case 6:
{
lean_object* x_32; uint64_t x_33; 
x_32 = lean_unsigned_to_nat(31u);
x_33 = lean_uint64_of_nat(x_32);
return x_33;
}
default: 
{
lean_object* x_34; uint64_t x_35; 
x_34 = lean_unsigned_to_nat(37u);
x_35 = lean_uint64_of_nat(x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_HeadIndex_hash___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_HeadIndex_hash(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_instHashableHeadIndex() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_HeadIndex_hash___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_1 = x_3;
x_2 = x_5;
goto _start;
}
case 8:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 3);
x_1 = x_7;
goto _start;
}
case 10:
{
lean_object* x_9; 
x_9 = lean_ctor_get(x_1, 1);
x_1 = x_9;
goto _start;
}
default: 
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_headNumArgs_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = l_Lean_Expr_headNumArgs_go(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_headNumArgs___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Expr_headNumArgs(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
case 1:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
case 2:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
case 3:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(5);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 4:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
case 5:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 0);
x_1 = x_14;
goto _start;
}
case 6:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(6);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
return x_17;
}
case 7:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(7);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
case 8:
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_1, 3);
x_1 = x_20;
goto _start;
}
case 9:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_1, 0);
lean_inc(x_22);
x_23 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
return x_24;
}
case 10:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_1, 1);
x_1 = x_25;
goto _start;
}
default: 
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_1, 0);
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_inc(x_27);
x_29 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_instInhabitedHeadIndex;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_2 = lean_mk_string_unchecked("Lean.HeadIndex", 14, 14);
x_3 = lean_mk_string_unchecked("_private.Lean.HeadIndex.0.Lean.Expr.toHeadIndexSlow", 51, 51);
x_4 = lean_unsigned_to_nat(100u);
x_5 = lean_unsigned_to_nat(31u);
x_6 = lean_mk_string_unchecked("unexpected expression kind", 26, 26);
x_7 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_panic___at_____private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow_spec__0(x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
case 2:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
case 3:
{
lean_object* x_13; 
lean_dec(x_1);
x_13 = lean_box(5);
return x_13;
}
case 4:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
case 5:
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_1 = x_16;
goto _start;
}
case 6:
{
lean_object* x_18; 
lean_dec(x_1);
x_18 = lean_box(6);
return x_18;
}
case 7:
{
lean_object* x_19; 
lean_dec(x_1);
x_19 = lean_box(7);
return x_19;
}
case 8:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_1, 2);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 3);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_expr_instantiate1(x_21, x_20);
lean_dec(x_20);
lean_dec(x_21);
x_1 = x_22;
goto _start;
}
case 9:
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_1, 0);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_25, 0, x_24);
return x_25;
}
case 10:
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_1 = x_26;
goto _start;
}
default: 
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_toHeadIndex(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexQuick_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = l___private_Lean_HeadIndex_0__Lean_Expr_toHeadIndexSlow(x_1);
return x_3;
}
else
{
lean_object* x_4; 
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
return x_4;
}
}
}
lean_object* initialize_Lean_Expr(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Expr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_instInhabitedHeadIndex = _init_l_Lean_instInhabitedHeadIndex();
lean_mark_persistent(l_Lean_instInhabitedHeadIndex);
l_Lean_instBEqHeadIndex = _init_l_Lean_instBEqHeadIndex();
lean_mark_persistent(l_Lean_instBEqHeadIndex);
l_Lean_instReprHeadIndex = _init_l_Lean_instReprHeadIndex();
lean_mark_persistent(l_Lean_instReprHeadIndex);
l_Lean_instHashableHeadIndex = _init_l_Lean_instHashableHeadIndex();
lean_mark_persistent(l_Lean_instHashableHeadIndex);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
