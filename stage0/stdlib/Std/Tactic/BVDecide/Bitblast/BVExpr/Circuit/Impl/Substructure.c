// Lean compiler output
// Module: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Substructure
// Imports: Std.Tactic.BVDecide.Bitblast.BVExpr.Circuit.Impl.Pred
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_Tactic_BVDecide_BVPred_bitblast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object*);
LEAN_EXPORT lean_object* l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
x_6 = l_Std_Tactic_BVDecide_BVPred_bitblast(x_1, x_5);
return x_6;
}
case 1:
{
uint8_t x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get_uint8(x_2, 0);
lean_dec(x_2);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_1);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_12, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_15, sizeof(void*)*1);
if (x_16 == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_13);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_13, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_14);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_14, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_box(1);
x_23 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_23, 0, x_21);
x_24 = lean_unbox(x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*1, x_24);
lean_ctor_set(x_14, 1, x_23);
return x_13;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_14, 0);
lean_inc(x_25);
lean_dec(x_14);
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_28, 0, x_26);
x_29 = lean_unbox(x_27);
lean_ctor_set_uint8(x_28, sizeof(void*)*1, x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_13, 0, x_30);
return x_13;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_31 = lean_ctor_get(x_13, 1);
lean_inc(x_31);
lean_dec(x_13);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_33 = x_14;
} else {
 lean_dec_ref(x_14);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_15, 0);
lean_inc(x_34);
lean_dec(x_15);
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_36, 0, x_34);
x_37 = lean_unbox(x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*1, x_37);
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_33;
}
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_14, 1);
lean_dec(x_43);
x_44 = lean_ctor_get(x_15, 0);
lean_inc(x_44);
lean_dec(x_15);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_46, 0, x_44);
x_47 = lean_unbox(x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*1, x_47);
lean_ctor_set(x_14, 1, x_46);
return x_13;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_48 = lean_ctor_get(x_14, 0);
lean_inc(x_48);
lean_dec(x_14);
x_49 = lean_ctor_get(x_15, 0);
lean_inc(x_49);
lean_dec(x_15);
x_50 = lean_box(0);
x_51 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_51, 0, x_49);
x_52 = lean_unbox(x_50);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_48);
lean_ctor_set(x_53, 1, x_51);
lean_ctor_set(x_13, 0, x_53);
return x_13;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_dec(x_13);
x_55 = lean_ctor_get(x_14, 0);
lean_inc(x_55);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_56 = x_14;
} else {
 lean_dec_ref(x_14);
 x_56 = lean_box(0);
}
x_57 = lean_ctor_get(x_15, 0);
lean_inc(x_57);
lean_dec(x_15);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
if (lean_is_scalar(x_56)) {
 x_61 = lean_alloc_ctor(0, 2, 0);
} else {
 x_61 = x_56;
}
lean_ctor_set(x_61, 0, x_55);
lean_ctor_set(x_61, 1, x_59);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_54);
return x_62;
}
}
}
case 3:
{
uint8_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_63 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_64 = lean_ctor_get(x_2, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_2, 1);
lean_inc(x_65);
lean_dec(x_2);
x_66 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_64, x_3);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_dec(x_67);
x_71 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_69, x_65, x_68);
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_73, 0);
x_76 = lean_ctor_get(x_70, 0);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_70, sizeof(void*)*1);
lean_dec(x_70);
x_78 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set_uint8(x_78, sizeof(void*)*1, x_77);
lean_ctor_set(x_73, 0, x_78);
switch (x_63) {
case 0:
{
lean_object* x_79; 
x_79 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_75, x_73);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_79);
return x_71;
}
case 1:
{
lean_object* x_80; 
x_80 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_75, x_73);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_80);
return x_71;
}
case 2:
{
lean_object* x_81; 
x_81 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_75, x_73);
lean_dec(x_73);
lean_ctor_set(x_71, 0, x_81);
return x_71;
}
default: 
{
lean_object* x_82; 
x_82 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_75, x_73);
lean_ctor_set(x_71, 0, x_82);
return x_71;
}
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_73, 0);
x_84 = lean_ctor_get(x_73, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_73);
x_85 = lean_ctor_get(x_70, 0);
lean_inc(x_85);
x_86 = lean_ctor_get_uint8(x_70, sizeof(void*)*1);
lean_dec(x_70);
x_87 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set_uint8(x_87, sizeof(void*)*1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_84);
switch (x_63) {
case 0:
{
lean_object* x_89; 
x_89 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_83, x_88);
lean_dec(x_88);
lean_ctor_set(x_71, 0, x_89);
return x_71;
}
case 1:
{
lean_object* x_90; 
x_90 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_83, x_88);
lean_dec(x_88);
lean_ctor_set(x_71, 0, x_90);
return x_71;
}
case 2:
{
lean_object* x_91; 
x_91 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_83, x_88);
lean_dec(x_88);
lean_ctor_set(x_71, 0, x_91);
return x_71;
}
default: 
{
lean_object* x_92; 
x_92 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_83, x_88);
lean_ctor_set(x_71, 0, x_92);
return x_71;
}
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; lean_object* x_101; 
x_93 = lean_ctor_get(x_71, 0);
x_94 = lean_ctor_get(x_71, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_71);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_97 = x_93;
} else {
 lean_dec_ref(x_93);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_70, 0);
lean_inc(x_98);
x_99 = lean_ctor_get_uint8(x_70, sizeof(void*)*1);
lean_dec(x_70);
x_100 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set_uint8(x_100, sizeof(void*)*1, x_99);
if (lean_is_scalar(x_97)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_97;
}
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_101, 1, x_96);
switch (x_63) {
case 0:
{
lean_object* x_102; lean_object* x_103; 
x_102 = l_Std_Sat_AIG_mkGateCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__4(x_95, x_101);
lean_dec(x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_94);
return x_103;
}
case 1:
{
lean_object* x_104; lean_object* x_105; 
x_104 = l_Std_Sat_AIG_mkXorCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__12(x_95, x_101);
lean_dec(x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_94);
return x_105;
}
case 2:
{
lean_object* x_106; lean_object* x_107; 
x_106 = l_Std_Sat_AIG_mkBEqCached___at___Std_Tactic_BVDecide_BVPred_mkEq___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastUdiv___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__34_spec__34_spec__34(x_95, x_101);
lean_dec(x_101);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_94);
return x_107;
}
default: 
{
lean_object* x_108; lean_object* x_109; 
x_108 = l_Std_Sat_AIG_mkOrCached___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__9(x_95, x_101);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_94);
return x_109;
}
}
}
}
default: 
{
uint8_t x_110; 
x_110 = !lean_is_exclusive(x_2);
if (x_110 == 0)
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_111 = lean_ctor_get(x_2, 0);
x_112 = lean_ctor_get(x_2, 1);
x_113 = lean_ctor_get(x_2, 2);
x_114 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_111, x_3);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_119 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_117, x_112, x_116);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_120, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_124 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_122, x_113, x_121);
x_125 = !lean_is_exclusive(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; uint8_t x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_126 = lean_ctor_get(x_124, 0);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
x_129 = lean_ctor_get(x_118, 0);
lean_inc(x_129);
x_130 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
lean_dec(x_118);
x_131 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set_uint8(x_131, sizeof(void*)*1, x_130);
x_132 = lean_ctor_get(x_123, 0);
lean_inc(x_132);
x_133 = lean_ctor_get_uint8(x_123, sizeof(void*)*1);
lean_dec(x_123);
x_134 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*1, x_133);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_128);
lean_ctor_set(x_2, 1, x_134);
lean_ctor_set(x_2, 0, x_131);
x_135 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_127, x_2);
lean_dec(x_2);
lean_ctor_set(x_124, 0, x_135);
return x_124;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_136 = lean_ctor_get(x_124, 0);
x_137 = lean_ctor_get(x_124, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_124);
x_138 = lean_ctor_get(x_136, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = lean_ctor_get(x_118, 0);
lean_inc(x_140);
x_141 = lean_ctor_get_uint8(x_118, sizeof(void*)*1);
lean_dec(x_118);
x_142 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set_uint8(x_142, sizeof(void*)*1, x_141);
x_143 = lean_ctor_get(x_123, 0);
lean_inc(x_143);
x_144 = lean_ctor_get_uint8(x_123, sizeof(void*)*1);
lean_dec(x_123);
x_145 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set_uint8(x_145, sizeof(void*)*1, x_144);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 2, x_139);
lean_ctor_set(x_2, 1, x_145);
lean_ctor_set(x_2, 0, x_142);
x_146 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_138, x_2);
lean_dec(x_2);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_137);
return x_147;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_148 = lean_ctor_get(x_2, 0);
x_149 = lean_ctor_get(x_2, 1);
x_150 = lean_ctor_get(x_2, 2);
lean_inc(x_150);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_2);
x_151 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_1, x_148, x_3);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_151, 1);
lean_inc(x_153);
lean_dec(x_151);
x_154 = lean_ctor_get(x_152, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_152, 1);
lean_inc(x_155);
lean_dec(x_152);
x_156 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_154, x_149, x_153);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_159, x_150, x_158);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_164 = x_161;
} else {
 lean_dec_ref(x_161);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_162, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_162, 1);
lean_inc(x_166);
lean_dec(x_162);
x_167 = lean_ctor_get(x_155, 0);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_155, sizeof(void*)*1);
lean_dec(x_155);
x_169 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_169, 0, x_167);
lean_ctor_set_uint8(x_169, sizeof(void*)*1, x_168);
x_170 = lean_ctor_get(x_160, 0);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_160, sizeof(void*)*1);
lean_dec(x_160);
x_172 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*1, x_171);
x_173 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_173, 0, x_169);
lean_ctor_set(x_173, 1, x_172);
lean_ctor_set(x_173, 2, x_166);
x_174 = l_Std_Sat_AIG_mkIfCached___at___Std_Sat_AIG_RefVec_ite_go___at___Std_Sat_AIG_RefVec_ite___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul_blast___at___Std_Tactic_BVDecide_BVExpr_bitblast_blastMul___at___Std_Tactic_BVDecide_BVExpr_bitblast_go_spec__24_spec__24_spec__24_spec__24_spec__24(x_165, x_173);
lean_dec(x_173);
if (lean_is_scalar(x_164)) {
 x_175 = lean_alloc_ctor(0, 2, 0);
} else {
 x_175 = x_164;
}
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_163);
return x_175;
}
}
}
}
}
static lean_object* _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(1u);
x_3 = lean_mk_empty_array_with_capacity(x_2);
x_4 = lean_array_push(x_3, x_1);
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_shiftl(x_5, x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_nextPowerOfTwo(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0;
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_shiftl(x_3, x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_nat_div(x_6, x_7);
lean_dec(x_6);
x_9 = l_Nat_nextPowerOfTwo(x_8);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go(x_2, x_1, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_apply_1(x_2, x_7);
return x_8;
}
case 1:
{
uint8_t x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_9 = lean_ctor_get_uint8(x_1, 0);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_apply_1(x_3, x_10);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_1(x_4, x_12);
return x_13;
}
case 3:
{
uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_box(x_14);
x_18 = lean_apply_3(x_6, x_17, x_15, x_16);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = lean_ctor_get(x_1, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 2);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_apply_3(x_5, x_19, x_20, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure_0__Std_Tactic_BVDecide_BVLogicalExpr_bitblast_go_match__3_splitter___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Substructure(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Bitblast_BVExpr_Circuit_Impl_Pred(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0 = _init_l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0();
lean_mark_persistent(l_Std_Sat_AIG_empty___at___Std_Tactic_BVDecide_BVLogicalExpr_bitblast_spec__0);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
