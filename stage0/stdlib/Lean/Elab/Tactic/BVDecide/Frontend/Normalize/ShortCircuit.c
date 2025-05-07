// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.ShortCircuit
// Imports: Lean.Elab.Tactic.Simp Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic Lean.Elab.Tactic.BVDecide.Frontend.Attr Std.Tactic.BVDecide.Normalize.BitVec
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Meta_getSimpCongrTheorems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpGoal(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed(lean_object**);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass;
extern lean_object* l_Lean_Meta_simpGlobalConfig;
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___lam__0), 8, 3);
lean_closure_set(x_10, 0, x_2);
lean_closure_set(x_10, 1, x_3);
lean_closure_set(x_10, 2, x_4);
x_11 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_10, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
return x_11;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_11);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21) {
_start:
{
lean_object* x_22; 
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_22 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_1, x_2, x_3, x_4, x_17, x_18, x_19, x_20, x_21);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_mk_string_unchecked("mul_beq_mul_short_circuit_right", 31, 31);
lean_inc(x_25);
x_26 = l_Lean_Name_mkStr1(x_25);
x_27 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*1, x_5);
lean_ctor_set_uint8(x_27, sizeof(void*)*1 + 1, x_6);
x_28 = l_Lean_Name_mkStr6(x_7, x_8, x_9, x_10, x_11, x_25);
x_29 = l_Lean_Expr_const___override(x_28, x_12);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_30 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_23, x_27, x_29, x_4, x_17, x_18, x_19, x_20, x_24);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Meta_getSimpCongrTheorems(x_19, x_20, x_32);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_15, 1);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_box(0);
lean_inc(x_37);
x_40 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*2, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 1, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 2, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 3, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 5, x_5);
x_41 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 6, x_41);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 7, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 8, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 9, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 10, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 11, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 12, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 13, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 14, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 15, x_6);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 16, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 17, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 18, x_5);
lean_ctor_set_uint8(x_40, sizeof(void*)*2 + 19, x_5);
x_42 = l_Lean_Meta_Simp_mkContext(x_40, x_31, x_35, x_17, x_18, x_19, x_20, x_36);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_46 = l_Lean_Meta_getPropHyps(x_17, x_18, x_19, x_20, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; size_t x_55; lean_object* x_56; lean_object* x_57; size_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_mk_empty_array_with_capacity(x_13);
x_50 = lean_box(0);
x_51 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_51);
x_52 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_52, 0, x_51);
lean_inc(x_13);
lean_inc(x_52);
lean_ctor_set(x_42, 1, x_13);
lean_ctor_set(x_42, 0, x_52);
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unsigned_to_nat(5u);
x_55 = lean_usize_of_nat(x_54);
x_56 = lean_usize_to_nat(x_55);
x_57 = lean_nat_pow(x_38, x_56);
lean_dec(x_56);
x_58 = lean_usize_of_nat(x_57);
lean_dec(x_57);
x_59 = lean_usize_to_nat(x_58);
x_60 = lean_mk_empty_array_with_capacity(x_59);
lean_dec(x_59);
lean_inc(x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_13);
x_62 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_60);
lean_ctor_set(x_62, 2, x_13);
lean_ctor_set(x_62, 3, x_13);
lean_ctor_set_usize(x_62, 4, x_55);
lean_inc(x_52);
x_63 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_52);
lean_ctor_set(x_63, 2, x_53);
lean_ctor_set(x_63, 3, x_62);
lean_ctor_set(x_33, 1, x_63);
lean_ctor_set(x_33, 0, x_42);
x_64 = l_Lean_Meta_simpGoal(x_14, x_44, x_49, x_50, x_5, x_47, x_33, x_17, x_18, x_19, x_20, x_48);
lean_dec(x_17);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
lean_dec(x_65);
if (lean_obj_tag(x_66) == 0)
{
uint8_t x_67; 
x_67 = !lean_is_exclusive(x_64);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_64, 0);
lean_dec(x_68);
x_69 = lean_box(0);
lean_ctor_set(x_64, 0, x_69);
return x_64;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_66);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_64);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_66, 0);
x_76 = lean_ctor_get(x_64, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_ctor_set(x_66, 0, x_77);
lean_ctor_set(x_64, 0, x_66);
return x_64;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_ctor_get(x_66, 0);
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
lean_ctor_set(x_66, 0, x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_66);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_66, 0);
lean_inc(x_82);
lean_dec(x_66);
x_83 = lean_ctor_get(x_64, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_64)) {
 lean_ctor_release(x_64, 0);
 lean_ctor_release(x_64, 1);
 x_84 = x_64;
} else {
 lean_dec_ref(x_64);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_82, 1);
lean_inc(x_85);
lean_dec(x_82);
x_86 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_86, 0, x_85);
if (lean_is_scalar(x_84)) {
 x_87 = lean_alloc_ctor(0, 2, 0);
} else {
 x_87 = x_84;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_83);
return x_87;
}
}
}
else
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_64);
if (x_88 == 0)
{
return x_64;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_64, 0);
x_90 = lean_ctor_get(x_64, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_64);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_free_object(x_42);
lean_dec(x_44);
lean_free_object(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_92 = !lean_is_exclusive(x_46);
if (x_92 == 0)
{
return x_46;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_46, 0);
x_94 = lean_ctor_get(x_46, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_46);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_42, 0);
x_97 = lean_ctor_get(x_42, 1);
lean_inc(x_97);
lean_inc(x_96);
lean_dec(x_42);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_98 = l_Lean_Meta_getPropHyps(x_17, x_18, x_19, x_20, x_97);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; size_t x_108; lean_object* x_109; lean_object* x_110; size_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_mk_empty_array_with_capacity(x_13);
x_102 = lean_box(0);
x_103 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_103);
x_104 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_104, 0, x_103);
lean_inc(x_13);
lean_inc(x_104);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_13);
x_106 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_106, 0, x_103);
x_107 = lean_unsigned_to_nat(5u);
x_108 = lean_usize_of_nat(x_107);
x_109 = lean_usize_to_nat(x_108);
x_110 = lean_nat_pow(x_38, x_109);
lean_dec(x_109);
x_111 = lean_usize_of_nat(x_110);
lean_dec(x_110);
x_112 = lean_usize_to_nat(x_111);
x_113 = lean_mk_empty_array_with_capacity(x_112);
lean_dec(x_112);
lean_inc(x_113);
x_114 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_114, 0, x_113);
lean_inc(x_13);
x_115 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_113);
lean_ctor_set(x_115, 2, x_13);
lean_ctor_set(x_115, 3, x_13);
lean_ctor_set_usize(x_115, 4, x_108);
lean_inc(x_104);
x_116 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_116, 0, x_104);
lean_ctor_set(x_116, 1, x_104);
lean_ctor_set(x_116, 2, x_106);
lean_ctor_set(x_116, 3, x_115);
lean_ctor_set(x_33, 1, x_116);
lean_ctor_set(x_33, 0, x_105);
x_117 = l_Lean_Meta_simpGoal(x_14, x_96, x_101, x_102, x_5, x_99, x_33, x_17, x_18, x_19, x_20, x_100);
lean_dec(x_17);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
lean_dec(x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_120 = lean_ctor_get(x_117, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_121 = x_117;
} else {
 lean_dec_ref(x_117);
 x_121 = lean_box(0);
}
x_122 = lean_box(0);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 x_125 = x_119;
} else {
 lean_dec_ref(x_119);
 x_125 = lean_box(0);
}
x_126 = lean_ctor_get(x_117, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_127 = x_117;
} else {
 lean_dec_ref(x_117);
 x_127 = lean_box(0);
}
x_128 = lean_ctor_get(x_124, 1);
lean_inc(x_128);
lean_dec(x_124);
if (lean_is_scalar(x_125)) {
 x_129 = lean_alloc_ctor(1, 1, 0);
} else {
 x_129 = x_125;
}
lean_ctor_set(x_129, 0, x_128);
if (lean_is_scalar(x_127)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_127;
}
lean_ctor_set(x_130, 0, x_129);
lean_ctor_set(x_130, 1, x_126);
return x_130;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_117, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_117, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_117)) {
 lean_ctor_release(x_117, 0);
 lean_ctor_release(x_117, 1);
 x_133 = x_117;
} else {
 lean_dec_ref(x_117);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_96);
lean_free_object(x_33);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_135 = lean_ctor_get(x_98, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_98, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_98)) {
 lean_ctor_release(x_98, 0);
 lean_ctor_release(x_98, 1);
 x_137 = x_98;
} else {
 lean_dec_ref(x_98);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_139 = lean_ctor_get(x_33, 0);
x_140 = lean_ctor_get(x_33, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_33);
x_141 = lean_ctor_get(x_15, 1);
x_142 = lean_unsigned_to_nat(2u);
x_143 = lean_box(0);
lean_inc(x_141);
x_144 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_144, 0, x_141);
lean_ctor_set(x_144, 1, x_142);
lean_ctor_set_uint8(x_144, sizeof(void*)*2, x_6);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 1, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 2, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 3, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 4, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 5, x_5);
x_145 = lean_unbox(x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 6, x_145);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 7, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 8, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 9, x_6);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 10, x_6);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 11, x_6);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 12, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 13, x_6);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 14, x_6);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 15, x_6);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 16, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 17, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 18, x_5);
lean_ctor_set_uint8(x_144, sizeof(void*)*2 + 19, x_5);
x_146 = l_Lean_Meta_Simp_mkContext(x_144, x_31, x_139, x_17, x_18, x_19, x_20, x_140);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_146, 1);
lean_inc(x_148);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_149 = x_146;
} else {
 lean_dec_ref(x_146);
 x_149 = lean_box(0);
}
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
x_150 = l_Lean_Meta_getPropHyps(x_17, x_18, x_19, x_20, x_148);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; size_t x_160; lean_object* x_161; lean_object* x_162; size_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_150, 1);
lean_inc(x_152);
lean_dec(x_150);
x_153 = lean_mk_empty_array_with_capacity(x_13);
x_154 = lean_box(0);
x_155 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_155);
x_156 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_inc(x_13);
lean_inc(x_156);
if (lean_is_scalar(x_149)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_149;
}
lean_ctor_set(x_157, 0, x_156);
lean_ctor_set(x_157, 1, x_13);
x_158 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_158, 0, x_155);
x_159 = lean_unsigned_to_nat(5u);
x_160 = lean_usize_of_nat(x_159);
x_161 = lean_usize_to_nat(x_160);
x_162 = lean_nat_pow(x_142, x_161);
lean_dec(x_161);
x_163 = lean_usize_of_nat(x_162);
lean_dec(x_162);
x_164 = lean_usize_to_nat(x_163);
x_165 = lean_mk_empty_array_with_capacity(x_164);
lean_dec(x_164);
lean_inc(x_165);
x_166 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_166, 0, x_165);
lean_inc(x_13);
x_167 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
lean_ctor_set(x_167, 2, x_13);
lean_ctor_set(x_167, 3, x_13);
lean_ctor_set_usize(x_167, 4, x_160);
lean_inc(x_156);
x_168 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_168, 0, x_156);
lean_ctor_set(x_168, 1, x_156);
lean_ctor_set(x_168, 2, x_158);
lean_ctor_set(x_168, 3, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_157);
lean_ctor_set(x_169, 1, x_168);
x_170 = l_Lean_Meta_simpGoal(x_14, x_147, x_153, x_154, x_5, x_151, x_169, x_17, x_18, x_19, x_20, x_152);
lean_dec(x_17);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_171, 0);
lean_inc(x_172);
lean_dec(x_171);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_174 = x_170;
} else {
 lean_dec_ref(x_170);
 x_174 = lean_box(0);
}
x_175 = lean_box(0);
if (lean_is_scalar(x_174)) {
 x_176 = lean_alloc_ctor(0, 2, 0);
} else {
 x_176 = x_174;
}
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_173);
return x_176;
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; 
x_177 = lean_ctor_get(x_172, 0);
lean_inc(x_177);
if (lean_is_exclusive(x_172)) {
 lean_ctor_release(x_172, 0);
 x_178 = x_172;
} else {
 lean_dec_ref(x_172);
 x_178 = lean_box(0);
}
x_179 = lean_ctor_get(x_170, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_180 = x_170;
} else {
 lean_dec_ref(x_170);
 x_180 = lean_box(0);
}
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
lean_dec(x_177);
if (lean_is_scalar(x_178)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_178;
}
lean_ctor_set(x_182, 0, x_181);
if (lean_is_scalar(x_180)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_180;
}
lean_ctor_set(x_183, 0, x_182);
lean_ctor_set(x_183, 1, x_179);
return x_183;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_184 = lean_ctor_get(x_170, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_170, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_186 = x_170;
} else {
 lean_dec_ref(x_170);
 x_186 = lean_box(0);
}
if (lean_is_scalar(x_186)) {
 x_187 = lean_alloc_ctor(1, 2, 0);
} else {
 x_187 = x_186;
}
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
return x_187;
}
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
lean_dec(x_149);
lean_dec(x_147);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_188 = lean_ctor_get(x_150, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_150, 1);
lean_inc(x_189);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_190 = x_150;
} else {
 lean_dec_ref(x_150);
 x_190 = lean_box(0);
}
if (lean_is_scalar(x_190)) {
 x_191 = lean_alloc_ctor(1, 2, 0);
} else {
 x_191 = x_190;
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_189);
return x_191;
}
}
}
else
{
uint8_t x_192; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
x_192 = !lean_is_exclusive(x_30);
if (x_192 == 0)
{
return x_30;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_30, 0);
x_194 = lean_ctor_get(x_30, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_30);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_196 = !lean_is_exclusive(x_22);
if (x_196 == 0)
{
return x_22;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_22, 0);
x_198 = lean_ctor_get(x_22, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_22);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_mk_string_unchecked("mul_beq_mul_short_circuit_left", 30, 30);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(1);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_15, 0, x_12);
x_16 = lean_unbox(x_13);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 1, x_17);
x_18 = lean_mk_string_unchecked("Std", 3, 3);
x_19 = lean_mk_string_unchecked("Tactic", 6, 6);
x_20 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_21 = lean_mk_string_unchecked("Normalize", 9, 9);
x_22 = lean_mk_string_unchecked("BitVec", 6, 6);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
x_23 = l_Lean_Name_mkStr6(x_18, x_19, x_20, x_21, x_22, x_11);
x_24 = lean_box(0);
x_25 = l_Lean_Expr_const___override(x_23, x_24);
x_26 = l_Lean_Meta_simpGlobalConfig;
lean_inc(x_1);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed), 21, 14);
lean_closure_set(x_27, 0, x_10);
lean_closure_set(x_27, 1, x_15);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_26);
lean_closure_set(x_27, 4, x_13);
lean_closure_set(x_27, 5, x_14);
lean_closure_set(x_27, 6, x_18);
lean_closure_set(x_27, 7, x_19);
lean_closure_set(x_27, 8, x_20);
lean_closure_set(x_27, 9, x_21);
lean_closure_set(x_27, 10, x_22);
lean_closure_set(x_27, 11, x_24);
lean_closure_set(x_27, 12, x_9);
lean_closure_set(x_27, 13, x_1);
x_28 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(x_1, x_27, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_28;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed), 8, 0);
x_2 = lean_mk_string_unchecked("shortCircuitPass", 16, 16);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0___boxed(lean_object** _args) {
lean_object* x_1 = _args[0];
lean_object* x_2 = _args[1];
lean_object* x_3 = _args[2];
lean_object* x_4 = _args[3];
lean_object* x_5 = _args[4];
lean_object* x_6 = _args[5];
lean_object* x_7 = _args[6];
lean_object* x_8 = _args[7];
lean_object* x_9 = _args[8];
lean_object* x_10 = _args[9];
lean_object* x_11 = _args[10];
lean_object* x_12 = _args[11];
lean_object* x_13 = _args[12];
lean_object* x_14 = _args[13];
lean_object* x_15 = _args[14];
lean_object* x_16 = _args[15];
lean_object* x_17 = _args[16];
lean_object* x_18 = _args[17];
lean_object* x_19 = _args[18];
lean_object* x_20 = _args[19];
lean_object* x_21 = _args[20];
_start:
{
uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_22 = lean_unbox(x_5);
lean_dec(x_5);
x_23 = lean_unbox(x_6);
lean_dec(x_6);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__0(x_1, x_2, x_3, x_4, x_22, x_23, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_4);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Lean_Elab_Tactic_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(uint8_t builtin, lean_object*);
lean_object* initialize_Std_Tactic_BVDecide_Normalize_BitVec(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_ShortCircuit(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Tactic_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Attr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Tactic_BVDecide_Normalize_BitVec(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_shortCircuitPass);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
