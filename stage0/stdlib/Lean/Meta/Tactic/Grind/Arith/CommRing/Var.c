// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.CommRing.Var
// Imports: Lean.Meta.Tactic.Grind.Arith.CommRing.Util
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
lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_hashRoot_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsCommRingTerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Arith_CommRing_mkVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_Arith_CommRing_RingM_getRing(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_14, 14);
lean_inc(x_16);
x_17 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_hashRoot_spec__0(lean_box(0), x_16, x_1);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_free_object(x_12);
x_18 = lean_st_ref_take(x_3, x_15);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_ctor_get(x_14, 13);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_19, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_19, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_19, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_19, 6);
lean_inc(x_30);
x_31 = lean_ctor_get(x_19, 7);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_19, sizeof(void*)*16);
x_33 = lean_ctor_get(x_19, 8);
lean_inc(x_33);
x_34 = lean_ctor_get(x_19, 9);
lean_inc(x_34);
x_35 = lean_ctor_get(x_19, 10);
lean_inc(x_35);
x_36 = lean_ctor_get(x_19, 11);
lean_inc(x_36);
x_37 = lean_ctor_get(x_19, 12);
lean_inc(x_37);
x_38 = lean_ctor_get(x_19, 13);
lean_inc(x_38);
x_39 = lean_ctor_get(x_19, 14);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 2);
lean_inc(x_42);
lean_dec(x_39);
x_65 = lean_ctor_get(x_42, 0);
lean_inc(x_65);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_23, x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_dec(x_23);
x_43 = x_65;
goto block_64;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; lean_object* x_97; lean_object* x_98; 
x_68 = lean_array_fget(x_65, x_23);
x_69 = lean_box(0);
x_70 = lean_array_fset(x_65, x_23, x_69);
x_71 = lean_ctor_get(x_68, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_68, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_68, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_68, 3);
lean_inc(x_74);
x_75 = lean_ctor_get(x_68, 4);
lean_inc(x_75);
x_76 = lean_ctor_get(x_68, 5);
lean_inc(x_76);
x_77 = lean_ctor_get(x_68, 6);
lean_inc(x_77);
x_78 = lean_ctor_get(x_68, 7);
lean_inc(x_78);
x_79 = lean_ctor_get(x_68, 8);
lean_inc(x_79);
x_80 = lean_ctor_get(x_68, 9);
lean_inc(x_80);
x_81 = lean_ctor_get(x_68, 10);
lean_inc(x_81);
x_82 = lean_ctor_get(x_68, 11);
lean_inc(x_82);
x_83 = lean_ctor_get(x_68, 12);
lean_inc(x_83);
x_84 = lean_ctor_get(x_68, 13);
lean_inc(x_84);
lean_inc(x_1);
x_85 = l_Lean_PersistentArray_push___redArg(x_84, x_1);
x_86 = lean_ctor_get(x_68, 14);
lean_inc(x_86);
lean_inc(x_22);
lean_inc(x_1);
x_87 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(x_86, x_1, x_22);
x_88 = lean_ctor_get(x_68, 15);
lean_inc(x_88);
x_89 = lean_ctor_get(x_68, 16);
lean_inc(x_89);
x_90 = lean_ctor_get(x_68, 17);
lean_inc(x_90);
x_91 = lean_ctor_get(x_68, 18);
lean_inc(x_91);
x_92 = lean_ctor_get(x_68, 19);
lean_inc(x_92);
x_93 = lean_box(0);
x_94 = l_Lean_PersistentArray_push___redArg(x_92, x_93);
x_95 = lean_ctor_get(x_68, 20);
lean_inc(x_95);
x_96 = lean_ctor_get_uint8(x_68, sizeof(void*)*21);
lean_dec(x_68);
x_97 = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(x_97, 0, x_71);
lean_ctor_set(x_97, 1, x_72);
lean_ctor_set(x_97, 2, x_73);
lean_ctor_set(x_97, 3, x_74);
lean_ctor_set(x_97, 4, x_75);
lean_ctor_set(x_97, 5, x_76);
lean_ctor_set(x_97, 6, x_77);
lean_ctor_set(x_97, 7, x_78);
lean_ctor_set(x_97, 8, x_79);
lean_ctor_set(x_97, 9, x_80);
lean_ctor_set(x_97, 10, x_81);
lean_ctor_set(x_97, 11, x_82);
lean_ctor_set(x_97, 12, x_83);
lean_ctor_set(x_97, 13, x_85);
lean_ctor_set(x_97, 14, x_87);
lean_ctor_set(x_97, 15, x_88);
lean_ctor_set(x_97, 16, x_89);
lean_ctor_set(x_97, 17, x_90);
lean_ctor_set(x_97, 18, x_91);
lean_ctor_set(x_97, 19, x_94);
lean_ctor_set(x_97, 20, x_95);
lean_ctor_set_uint8(x_97, sizeof(void*)*21, x_96);
x_98 = lean_array_fset(x_70, x_23, x_97);
lean_dec(x_23);
x_43 = x_98;
goto block_64;
}
block_64:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 3);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_44);
lean_ctor_set(x_47, 2, x_45);
lean_ctor_set(x_47, 3, x_46);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_40);
lean_ctor_set(x_48, 1, x_41);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_ctor_get(x_19, 15);
lean_inc(x_49);
lean_dec(x_19);
x_50 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_50, 0, x_24);
lean_ctor_set(x_50, 1, x_25);
lean_ctor_set(x_50, 2, x_26);
lean_ctor_set(x_50, 3, x_27);
lean_ctor_set(x_50, 4, x_28);
lean_ctor_set(x_50, 5, x_29);
lean_ctor_set(x_50, 6, x_30);
lean_ctor_set(x_50, 7, x_31);
lean_ctor_set(x_50, 8, x_33);
lean_ctor_set(x_50, 9, x_34);
lean_ctor_set(x_50, 10, x_35);
lean_ctor_set(x_50, 11, x_36);
lean_ctor_set(x_50, 12, x_37);
lean_ctor_set(x_50, 13, x_38);
lean_ctor_set(x_50, 14, x_48);
lean_ctor_set(x_50, 15, x_49);
lean_ctor_set_uint8(x_50, sizeof(void*)*16, x_32);
x_51 = lean_st_ref_set(x_3, x_50, x_20);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
lean_inc(x_1);
x_53 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_52);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_54);
if (lean_obj_tag(x_55) == 0)
{
uint8_t x_56; 
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
lean_ctor_set(x_55, 0, x_22);
return x_55;
}
else
{
lean_object* x_58; lean_object* x_59; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_22);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
else
{
uint8_t x_60; 
lean_dec(x_22);
x_60 = !lean_is_exclusive(x_55);
if (x_60 == 0)
{
return x_55;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_55, 0);
x_62 = lean_ctor_get(x_55, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_55);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_99 = lean_ctor_get(x_17, 0);
lean_inc(x_99);
lean_dec(x_17);
lean_ctor_set(x_12, 0, x_99);
return x_12;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_12, 0);
x_101 = lean_ctor_get(x_12, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_12);
x_102 = lean_ctor_get(x_100, 14);
lean_inc(x_102);
x_103 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_Tactic_Grind_Types_0__Lean_Meta_Grind_hashRoot_spec__0(lean_box(0), x_102, x_1);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_104 = lean_st_ref_take(x_3, x_101);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_ctor_get(x_100, 13);
lean_inc(x_107);
lean_dec(x_100);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_ctor_get(x_2, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
x_112 = lean_ctor_get(x_105, 2);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 3);
lean_inc(x_113);
x_114 = lean_ctor_get(x_105, 4);
lean_inc(x_114);
x_115 = lean_ctor_get(x_105, 5);
lean_inc(x_115);
x_116 = lean_ctor_get(x_105, 6);
lean_inc(x_116);
x_117 = lean_ctor_get(x_105, 7);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_105, sizeof(void*)*16);
x_119 = lean_ctor_get(x_105, 8);
lean_inc(x_119);
x_120 = lean_ctor_get(x_105, 9);
lean_inc(x_120);
x_121 = lean_ctor_get(x_105, 10);
lean_inc(x_121);
x_122 = lean_ctor_get(x_105, 11);
lean_inc(x_122);
x_123 = lean_ctor_get(x_105, 12);
lean_inc(x_123);
x_124 = lean_ctor_get(x_105, 13);
lean_inc(x_124);
x_125 = lean_ctor_get(x_105, 14);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_125, 2);
lean_inc(x_128);
lean_dec(x_125);
x_150 = lean_ctor_get(x_128, 0);
lean_inc(x_150);
x_151 = lean_array_get_size(x_150);
x_152 = lean_nat_dec_lt(x_109, x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_dec(x_109);
x_129 = x_150;
goto block_149;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; lean_object* x_182; lean_object* x_183; 
x_153 = lean_array_fget(x_150, x_109);
x_154 = lean_box(0);
x_155 = lean_array_fset(x_150, x_109, x_154);
x_156 = lean_ctor_get(x_153, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_153, 1);
lean_inc(x_157);
x_158 = lean_ctor_get(x_153, 2);
lean_inc(x_158);
x_159 = lean_ctor_get(x_153, 3);
lean_inc(x_159);
x_160 = lean_ctor_get(x_153, 4);
lean_inc(x_160);
x_161 = lean_ctor_get(x_153, 5);
lean_inc(x_161);
x_162 = lean_ctor_get(x_153, 6);
lean_inc(x_162);
x_163 = lean_ctor_get(x_153, 7);
lean_inc(x_163);
x_164 = lean_ctor_get(x_153, 8);
lean_inc(x_164);
x_165 = lean_ctor_get(x_153, 9);
lean_inc(x_165);
x_166 = lean_ctor_get(x_153, 10);
lean_inc(x_166);
x_167 = lean_ctor_get(x_153, 11);
lean_inc(x_167);
x_168 = lean_ctor_get(x_153, 12);
lean_inc(x_168);
x_169 = lean_ctor_get(x_153, 13);
lean_inc(x_169);
lean_inc(x_1);
x_170 = l_Lean_PersistentArray_push___redArg(x_169, x_1);
x_171 = lean_ctor_get(x_153, 14);
lean_inc(x_171);
lean_inc(x_108);
lean_inc(x_1);
x_172 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_registerParent_spec__0___redArg(x_171, x_1, x_108);
x_173 = lean_ctor_get(x_153, 15);
lean_inc(x_173);
x_174 = lean_ctor_get(x_153, 16);
lean_inc(x_174);
x_175 = lean_ctor_get(x_153, 17);
lean_inc(x_175);
x_176 = lean_ctor_get(x_153, 18);
lean_inc(x_176);
x_177 = lean_ctor_get(x_153, 19);
lean_inc(x_177);
x_178 = lean_box(0);
x_179 = l_Lean_PersistentArray_push___redArg(x_177, x_178);
x_180 = lean_ctor_get(x_153, 20);
lean_inc(x_180);
x_181 = lean_ctor_get_uint8(x_153, sizeof(void*)*21);
lean_dec(x_153);
x_182 = lean_alloc_ctor(0, 21, 1);
lean_ctor_set(x_182, 0, x_156);
lean_ctor_set(x_182, 1, x_157);
lean_ctor_set(x_182, 2, x_158);
lean_ctor_set(x_182, 3, x_159);
lean_ctor_set(x_182, 4, x_160);
lean_ctor_set(x_182, 5, x_161);
lean_ctor_set(x_182, 6, x_162);
lean_ctor_set(x_182, 7, x_163);
lean_ctor_set(x_182, 8, x_164);
lean_ctor_set(x_182, 9, x_165);
lean_ctor_set(x_182, 10, x_166);
lean_ctor_set(x_182, 11, x_167);
lean_ctor_set(x_182, 12, x_168);
lean_ctor_set(x_182, 13, x_170);
lean_ctor_set(x_182, 14, x_172);
lean_ctor_set(x_182, 15, x_173);
lean_ctor_set(x_182, 16, x_174);
lean_ctor_set(x_182, 17, x_175);
lean_ctor_set(x_182, 18, x_176);
lean_ctor_set(x_182, 19, x_179);
lean_ctor_set(x_182, 20, x_180);
lean_ctor_set_uint8(x_182, sizeof(void*)*21, x_181);
x_183 = lean_array_fset(x_155, x_109, x_182);
lean_dec(x_109);
x_129 = x_183;
goto block_149;
}
block_149:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_128, 2);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 3);
lean_inc(x_132);
lean_dec(x_128);
x_133 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_133, 0, x_129);
lean_ctor_set(x_133, 1, x_130);
lean_ctor_set(x_133, 2, x_131);
lean_ctor_set(x_133, 3, x_132);
x_134 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_134, 0, x_126);
lean_ctor_set(x_134, 1, x_127);
lean_ctor_set(x_134, 2, x_133);
x_135 = lean_ctor_get(x_105, 15);
lean_inc(x_135);
lean_dec(x_105);
x_136 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_136, 0, x_110);
lean_ctor_set(x_136, 1, x_111);
lean_ctor_set(x_136, 2, x_112);
lean_ctor_set(x_136, 3, x_113);
lean_ctor_set(x_136, 4, x_114);
lean_ctor_set(x_136, 5, x_115);
lean_ctor_set(x_136, 6, x_116);
lean_ctor_set(x_136, 7, x_117);
lean_ctor_set(x_136, 8, x_119);
lean_ctor_set(x_136, 9, x_120);
lean_ctor_set(x_136, 10, x_121);
lean_ctor_set(x_136, 11, x_122);
lean_ctor_set(x_136, 12, x_123);
lean_ctor_set(x_136, 13, x_124);
lean_ctor_set(x_136, 14, x_134);
lean_ctor_set(x_136, 15, x_135);
lean_ctor_set_uint8(x_136, sizeof(void*)*16, x_118);
x_137 = lean_st_ref_set(x_3, x_136, x_106);
x_138 = lean_ctor_get(x_137, 1);
lean_inc(x_138);
lean_dec(x_137);
lean_inc(x_1);
x_139 = l_Lean_Meta_Grind_Arith_CommRing_setTermRingId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_138);
x_140 = lean_ctor_get(x_139, 1);
lean_inc(x_140);
lean_dec(x_139);
x_141 = l_Lean_Meta_Grind_markAsCommRingTerm(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_140);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_143 = x_141;
} else {
 lean_dec_ref(x_141);
 x_143 = lean_box(0);
}
if (lean_is_scalar(x_143)) {
 x_144 = lean_alloc_ctor(0, 2, 0);
} else {
 x_144 = x_143;
}
lean_ctor_set(x_144, 0, x_108);
lean_ctor_set(x_144, 1, x_142);
return x_144;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_108);
x_145 = lean_ctor_get(x_141, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_147 = x_141;
} else {
 lean_dec_ref(x_141);
 x_147 = lean_box(0);
}
if (lean_is_scalar(x_147)) {
 x_148 = lean_alloc_ctor(1, 2, 0);
} else {
 x_148 = x_147;
}
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
}
else
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_100);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_184 = lean_ctor_get(x_103, 0);
lean_inc(x_184);
lean_dec(x_103);
x_185 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_101);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_186 = !lean_is_exclusive(x_12);
if (x_186 == 0)
{
return x_12;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_12, 0);
x_188 = lean_ctor_get(x_12, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_12);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Var(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Tactic_Grind_Arith_CommRing_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
