// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.AndFlatten
// Imports: Std.Tactic.BVDecide.Normalize.Bool Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic Lean.Meta.Tactic.Assert
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint8_t l_Lean_Expr_isApp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
lean_object* l_Lean_Meta_getPropHyps(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_MVarId_tryClearMany(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assertHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = lean_mk_string_unchecked("Eq", 2, 2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_unsigned_to_nat(1u);
x_5 = l_Lean_Level_ofNat(x_4);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = l_Lean_Expr_const___override(x_3, x_7);
x_9 = lean_mk_string_unchecked("Bool", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = l_Lean_Expr_const___override(x_10, x_6);
x_12 = lean_mk_string_unchecked("true", 4, 4);
x_13 = l_Lean_Name_mkStr2(x_9, x_12);
x_14 = l_Lean_Expr_const___override(x_13, x_6);
x_15 = l_Lean_mkApp3(x_8, x_11, x_1, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_8; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_st_ref_get(x_2, x_3);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; size_t x_30; size_t x_31; lean_object* x_32; size_t x_33; size_t x_34; size_t x_35; lean_object* x_36; uint8_t x_37; 
x_16 = lean_ctor_get(x_12, 1);
x_17 = lean_ctor_get(x_12, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
x_20 = lean_array_get_size(x_18);
x_21 = l_Lean_Expr_hash(x_19);
x_22 = lean_unsigned_to_nat(32u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_unsigned_to_nat(16u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_uint64_to_usize(x_29);
x_31 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_sub(x_31, x_33);
x_35 = lean_usize_land(x_30, x_34);
x_36 = lean_array_uget(x_18, x_35);
lean_dec(x_18);
x_37 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_19, x_36);
lean_dec(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_167; size_t x_168; size_t x_169; size_t x_170; lean_object* x_171; uint8_t x_172; 
lean_free_object(x_12);
x_38 = lean_st_ref_take(x_2, x_16);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_38)) {
 lean_ctor_release(x_38, 0);
 lean_ctor_release(x_38, 1);
 x_42 = x_38;
} else {
 lean_dec_ref(x_38);
 x_42 = lean_box(0);
}
x_43 = lean_ctor_get(x_40, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_dec(x_39);
x_167 = lean_array_get_size(x_44);
x_168 = lean_usize_of_nat(x_167);
lean_dec(x_167);
x_169 = lean_usize_sub(x_168, x_33);
x_170 = lean_usize_land(x_30, x_169);
x_171 = lean_array_uget(x_44, x_170);
x_172 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_19, x_171);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = !lean_is_exclusive(x_40);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_174 = lean_ctor_get(x_40, 1);
lean_dec(x_174);
x_175 = lean_ctor_get(x_40, 0);
lean_dec(x_175);
x_176 = lean_box(0);
x_177 = lean_nat_add(x_43, x_32);
lean_dec(x_43);
lean_inc(x_19);
x_178 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_178, 0, x_19);
lean_ctor_set(x_178, 1, x_176);
lean_ctor_set(x_178, 2, x_171);
x_179 = lean_array_uset(x_44, x_170, x_178);
x_180 = lean_unsigned_to_nat(2u);
x_181 = lean_nat_shiftl(x_177, x_180);
x_182 = lean_unsigned_to_nat(3u);
x_183 = lean_nat_div(x_181, x_182);
lean_dec(x_181);
x_184 = lean_array_get_size(x_179);
x_185 = lean_nat_dec_le(x_183, x_184);
lean_dec(x_184);
lean_dec(x_183);
if (x_185 == 0)
{
lean_object* x_186; 
x_186 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_179);
lean_ctor_set(x_40, 1, x_186);
lean_ctor_set(x_40, 0, x_177);
x_47 = x_40;
goto block_166;
}
else
{
lean_ctor_set(x_40, 1, x_179);
lean_ctor_set(x_40, 0, x_177);
x_47 = x_40;
goto block_166;
}
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint8_t x_196; 
lean_dec(x_40);
x_187 = lean_box(0);
x_188 = lean_nat_add(x_43, x_32);
lean_dec(x_43);
lean_inc(x_19);
x_189 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_189, 0, x_19);
lean_ctor_set(x_189, 1, x_187);
lean_ctor_set(x_189, 2, x_171);
x_190 = lean_array_uset(x_44, x_170, x_189);
x_191 = lean_unsigned_to_nat(2u);
x_192 = lean_nat_shiftl(x_188, x_191);
x_193 = lean_unsigned_to_nat(3u);
x_194 = lean_nat_div(x_192, x_193);
lean_dec(x_192);
x_195 = lean_array_get_size(x_190);
x_196 = lean_nat_dec_le(x_194, x_195);
lean_dec(x_195);
lean_dec(x_194);
if (x_196 == 0)
{
lean_object* x_197; lean_object* x_198; 
x_197 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_190);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_188);
lean_ctor_set(x_198, 1, x_197);
x_47 = x_198;
goto block_166;
}
else
{
lean_object* x_199; 
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_188);
lean_ctor_set(x_199, 1, x_190);
x_47 = x_199;
goto block_166;
}
}
}
else
{
lean_dec(x_171);
lean_dec(x_44);
lean_dec(x_43);
x_47 = x_40;
goto block_166;
}
block_166:
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = lean_st_ref_set(x_2, x_48, x_41);
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_49, 1);
x_52 = lean_ctor_get(x_49, 0);
lean_dec(x_52);
x_53 = l_Lean_Expr_cleanupAnnotations(x_19);
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_free_object(x_49);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_51;
goto block_11;
}
else
{
lean_object* x_55; uint8_t x_56; 
lean_inc(x_53);
x_55 = l_Lean_Expr_appFnCleanup___redArg(x_53);
x_56 = l_Lean_Expr_isApp(x_55);
if (x_56 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
lean_free_object(x_49);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_51;
goto block_11;
}
else
{
lean_object* x_57; uint8_t x_58; 
lean_inc(x_55);
x_57 = l_Lean_Expr_appFnCleanup___redArg(x_55);
x_58 = l_Lean_Expr_isApp(x_57);
if (x_58 == 0)
{
lean_dec(x_57);
lean_dec(x_55);
lean_dec(x_53);
lean_free_object(x_49);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_51;
goto block_11;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_60 = lean_mk_string_unchecked("Eq", 2, 2);
x_61 = l_Lean_Name_mkStr1(x_60);
x_62 = l_Lean_Expr_isConstOf(x_59, x_61);
lean_dec(x_61);
lean_dec(x_59);
if (x_62 == 0)
{
lean_dec(x_55);
lean_dec(x_53);
lean_free_object(x_49);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_51;
goto block_11;
}
else
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_63 = lean_ctor_get(x_55, 1);
lean_inc(x_63);
lean_dec(x_55);
x_64 = l_Lean_Expr_cleanupAnnotations(x_63);
x_65 = l_Lean_Expr_isApp(x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_53);
lean_free_object(x_49);
lean_dec(x_42);
lean_dec(x_1);
x_4 = x_51;
goto block_7;
}
else
{
lean_object* x_66; uint8_t x_67; 
lean_inc(x_64);
x_66 = l_Lean_Expr_appFnCleanup___redArg(x_64);
x_67 = l_Lean_Expr_isApp(x_66);
if (x_67 == 0)
{
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_53);
lean_free_object(x_49);
lean_dec(x_42);
lean_dec(x_1);
x_4 = x_51;
goto block_7;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
lean_inc(x_66);
x_68 = l_Lean_Expr_appFnCleanup___redArg(x_66);
x_69 = lean_mk_string_unchecked("Bool", 4, 4);
x_70 = lean_mk_string_unchecked("and", 3, 3);
lean_inc(x_69);
x_71 = l_Lean_Name_mkStr2(x_69, x_70);
x_72 = l_Lean_Expr_isConstOf(x_68, x_71);
lean_dec(x_71);
lean_dec(x_68);
if (x_72 == 0)
{
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_53);
lean_free_object(x_49);
lean_dec(x_42);
lean_dec(x_1);
x_4 = x_51;
goto block_7;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_73 = lean_ctor_get(x_53, 1);
lean_inc(x_73);
lean_dec(x_53);
x_74 = l_Lean_Expr_cleanupAnnotations(x_73);
x_75 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_69);
x_76 = l_Lean_Name_mkStr2(x_69, x_75);
x_77 = l_Lean_Expr_isConstOf(x_74, x_76);
lean_dec(x_76);
lean_dec(x_74);
if (x_77 == 0)
{
lean_object* x_78; 
lean_dec(x_69);
lean_dec(x_66);
lean_dec(x_64);
lean_dec(x_42);
lean_dec(x_1);
x_78 = lean_box(0);
lean_ctor_set(x_49, 0, x_78);
return x_49;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; 
x_79 = lean_ctor_get(x_64, 1);
lean_inc(x_79);
lean_dec(x_64);
x_80 = lean_ctor_get(x_66, 1);
lean_inc(x_80);
lean_dec(x_66);
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_inc(x_80);
x_82 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(x_80);
x_83 = lean_mk_string_unchecked("Std", 3, 3);
x_84 = lean_mk_string_unchecked("Tactic", 6, 6);
x_85 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_86 = lean_mk_string_unchecked("Normalize", 9, 9);
x_87 = lean_mk_string_unchecked("and_left", 8, 8);
lean_inc(x_69);
lean_inc(x_86);
lean_inc(x_85);
lean_inc(x_84);
lean_inc(x_83);
x_88 = l_Lean_Name_mkStr6(x_83, x_84, x_85, x_86, x_69, x_87);
x_89 = lean_box(0);
x_90 = l_Lean_Expr_const___override(x_88, x_89);
x_91 = lean_ctor_get(x_1, 2);
lean_inc(x_91);
lean_dec(x_1);
lean_inc(x_91);
lean_inc(x_79);
lean_inc(x_80);
x_92 = l_Lean_mkApp3(x_90, x_80, x_79, x_91);
x_93 = lean_box(0);
x_94 = lean_box(0);
lean_inc(x_81);
x_95 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_95, 0, x_81);
lean_ctor_set(x_95, 1, x_82);
lean_ctor_set(x_95, 2, x_92);
x_96 = lean_unbox(x_93);
lean_ctor_set_uint8(x_95, sizeof(void*)*3, x_96);
x_97 = lean_unbox(x_94);
lean_ctor_set_uint8(x_95, sizeof(void*)*3 + 1, x_97);
lean_inc(x_79);
x_98 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(x_79);
x_99 = lean_mk_string_unchecked("and_right", 9, 9);
x_100 = l_Lean_Name_mkStr6(x_83, x_84, x_85, x_86, x_69, x_99);
x_101 = l_Lean_Expr_const___override(x_100, x_89);
x_102 = l_Lean_mkApp3(x_101, x_80, x_79, x_91);
x_103 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_103, 0, x_81);
lean_ctor_set(x_103, 1, x_98);
lean_ctor_set(x_103, 2, x_102);
x_104 = lean_unbox(x_93);
lean_ctor_set_uint8(x_103, sizeof(void*)*3, x_104);
x_105 = lean_unbox(x_94);
lean_ctor_set_uint8(x_103, sizeof(void*)*3 + 1, x_105);
if (lean_is_scalar(x_42)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_42;
}
lean_ctor_set(x_106, 0, x_95);
lean_ctor_set(x_106, 1, x_103);
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_49, 0, x_107);
return x_49;
}
}
}
}
}
}
}
}
}
else
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; 
x_108 = lean_ctor_get(x_49, 1);
lean_inc(x_108);
lean_dec(x_49);
x_109 = l_Lean_Expr_cleanupAnnotations(x_19);
x_110 = l_Lean_Expr_isApp(x_109);
if (x_110 == 0)
{
lean_dec(x_109);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_108;
goto block_11;
}
else
{
lean_object* x_111; uint8_t x_112; 
lean_inc(x_109);
x_111 = l_Lean_Expr_appFnCleanup___redArg(x_109);
x_112 = l_Lean_Expr_isApp(x_111);
if (x_112 == 0)
{
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_108;
goto block_11;
}
else
{
lean_object* x_113; uint8_t x_114; 
lean_inc(x_111);
x_113 = l_Lean_Expr_appFnCleanup___redArg(x_111);
x_114 = l_Lean_Expr_isApp(x_113);
if (x_114 == 0)
{
lean_dec(x_113);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_108;
goto block_11;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_115 = l_Lean_Expr_appFnCleanup___redArg(x_113);
x_116 = lean_mk_string_unchecked("Eq", 2, 2);
x_117 = l_Lean_Name_mkStr1(x_116);
x_118 = l_Lean_Expr_isConstOf(x_115, x_117);
lean_dec(x_117);
lean_dec(x_115);
if (x_118 == 0)
{
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_42);
lean_dec(x_1);
x_8 = x_108;
goto block_11;
}
else
{
lean_object* x_119; lean_object* x_120; uint8_t x_121; 
x_119 = lean_ctor_get(x_111, 1);
lean_inc(x_119);
lean_dec(x_111);
x_120 = l_Lean_Expr_cleanupAnnotations(x_119);
x_121 = l_Lean_Expr_isApp(x_120);
if (x_121 == 0)
{
lean_dec(x_120);
lean_dec(x_109);
lean_dec(x_42);
lean_dec(x_1);
x_4 = x_108;
goto block_7;
}
else
{
lean_object* x_122; uint8_t x_123; 
lean_inc(x_120);
x_122 = l_Lean_Expr_appFnCleanup___redArg(x_120);
x_123 = l_Lean_Expr_isApp(x_122);
if (x_123 == 0)
{
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_109);
lean_dec(x_42);
lean_dec(x_1);
x_4 = x_108;
goto block_7;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; uint8_t x_128; 
lean_inc(x_122);
x_124 = l_Lean_Expr_appFnCleanup___redArg(x_122);
x_125 = lean_mk_string_unchecked("Bool", 4, 4);
x_126 = lean_mk_string_unchecked("and", 3, 3);
lean_inc(x_125);
x_127 = l_Lean_Name_mkStr2(x_125, x_126);
x_128 = l_Lean_Expr_isConstOf(x_124, x_127);
lean_dec(x_127);
lean_dec(x_124);
if (x_128 == 0)
{
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_109);
lean_dec(x_42);
lean_dec(x_1);
x_4 = x_108;
goto block_7;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_129 = lean_ctor_get(x_109, 1);
lean_inc(x_129);
lean_dec(x_109);
x_130 = l_Lean_Expr_cleanupAnnotations(x_129);
x_131 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_125);
x_132 = l_Lean_Name_mkStr2(x_125, x_131);
x_133 = l_Lean_Expr_isConstOf(x_130, x_132);
lean_dec(x_132);
lean_dec(x_130);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_125);
lean_dec(x_122);
lean_dec(x_120);
lean_dec(x_42);
lean_dec(x_1);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_108);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_136 = lean_ctor_get(x_120, 1);
lean_inc(x_136);
lean_dec(x_120);
x_137 = lean_ctor_get(x_122, 1);
lean_inc(x_137);
lean_dec(x_122);
x_138 = lean_ctor_get(x_1, 0);
lean_inc(x_138);
lean_inc(x_137);
x_139 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(x_137);
x_140 = lean_mk_string_unchecked("Std", 3, 3);
x_141 = lean_mk_string_unchecked("Tactic", 6, 6);
x_142 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_143 = lean_mk_string_unchecked("Normalize", 9, 9);
x_144 = lean_mk_string_unchecked("and_left", 8, 8);
lean_inc(x_125);
lean_inc(x_143);
lean_inc(x_142);
lean_inc(x_141);
lean_inc(x_140);
x_145 = l_Lean_Name_mkStr6(x_140, x_141, x_142, x_143, x_125, x_144);
x_146 = lean_box(0);
x_147 = l_Lean_Expr_const___override(x_145, x_146);
x_148 = lean_ctor_get(x_1, 2);
lean_inc(x_148);
lean_dec(x_1);
lean_inc(x_148);
lean_inc(x_136);
lean_inc(x_137);
x_149 = l_Lean_mkApp3(x_147, x_137, x_136, x_148);
x_150 = lean_box(0);
x_151 = lean_box(0);
lean_inc(x_138);
x_152 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_152, 0, x_138);
lean_ctor_set(x_152, 1, x_139);
lean_ctor_set(x_152, 2, x_149);
x_153 = lean_unbox(x_150);
lean_ctor_set_uint8(x_152, sizeof(void*)*3, x_153);
x_154 = lean_unbox(x_151);
lean_ctor_set_uint8(x_152, sizeof(void*)*3 + 1, x_154);
lean_inc(x_136);
x_155 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(x_136);
x_156 = lean_mk_string_unchecked("and_right", 9, 9);
x_157 = l_Lean_Name_mkStr6(x_140, x_141, x_142, x_143, x_125, x_156);
x_158 = l_Lean_Expr_const___override(x_157, x_146);
x_159 = l_Lean_mkApp3(x_158, x_137, x_136, x_148);
x_160 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_160, 0, x_138);
lean_ctor_set(x_160, 1, x_155);
lean_ctor_set(x_160, 2, x_159);
x_161 = lean_unbox(x_150);
lean_ctor_set_uint8(x_160, sizeof(void*)*3, x_161);
x_162 = lean_unbox(x_151);
lean_ctor_set_uint8(x_160, sizeof(void*)*3 + 1, x_162);
if (lean_is_scalar(x_42)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_42;
}
lean_ctor_set(x_163, 0, x_152);
lean_ctor_set(x_163, 1, x_160);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_164);
lean_ctor_set(x_165, 1, x_108);
return x_165;
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
}
else
{
lean_object* x_200; 
lean_dec(x_19);
lean_dec(x_1);
x_200 = lean_box(0);
lean_ctor_set(x_12, 0, x_200);
return x_12;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint64_t x_205; lean_object* x_206; uint64_t x_207; uint64_t x_208; uint64_t x_209; lean_object* x_210; uint64_t x_211; uint64_t x_212; uint64_t x_213; size_t x_214; size_t x_215; lean_object* x_216; size_t x_217; size_t x_218; size_t x_219; lean_object* x_220; uint8_t x_221; 
x_201 = lean_ctor_get(x_12, 1);
lean_inc(x_201);
lean_dec(x_12);
x_202 = lean_ctor_get(x_14, 1);
lean_inc(x_202);
lean_dec(x_14);
x_203 = lean_ctor_get(x_1, 1);
lean_inc(x_203);
x_204 = lean_array_get_size(x_202);
x_205 = l_Lean_Expr_hash(x_203);
x_206 = lean_unsigned_to_nat(32u);
x_207 = lean_uint64_of_nat(x_206);
x_208 = lean_uint64_shift_right(x_205, x_207);
x_209 = lean_uint64_xor(x_205, x_208);
x_210 = lean_unsigned_to_nat(16u);
x_211 = lean_uint64_of_nat(x_210);
x_212 = lean_uint64_shift_right(x_209, x_211);
x_213 = lean_uint64_xor(x_209, x_212);
x_214 = lean_uint64_to_usize(x_213);
x_215 = lean_usize_of_nat(x_204);
lean_dec(x_204);
x_216 = lean_unsigned_to_nat(1u);
x_217 = lean_usize_of_nat(x_216);
x_218 = lean_usize_sub(x_215, x_217);
x_219 = lean_usize_land(x_214, x_218);
x_220 = lean_array_uget(x_202, x_219);
lean_dec(x_202);
x_221 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_203, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_294; size_t x_295; size_t x_296; size_t x_297; lean_object* x_298; uint8_t x_299; 
x_222 = lean_st_ref_take(x_2, x_201);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_223, 2);
lean_inc(x_224);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
if (lean_is_exclusive(x_222)) {
 lean_ctor_release(x_222, 0);
 lean_ctor_release(x_222, 1);
 x_226 = x_222;
} else {
 lean_dec_ref(x_222);
 x_226 = lean_box(0);
}
x_227 = lean_ctor_get(x_224, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_224, 1);
lean_inc(x_228);
x_229 = lean_ctor_get(x_223, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_223, 1);
lean_inc(x_230);
lean_dec(x_223);
x_294 = lean_array_get_size(x_228);
x_295 = lean_usize_of_nat(x_294);
lean_dec(x_294);
x_296 = lean_usize_sub(x_295, x_217);
x_297 = lean_usize_land(x_214, x_296);
x_298 = lean_array_uget(x_228, x_297);
x_299 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_203, x_298);
if (x_299 == 0)
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; 
if (lean_is_exclusive(x_224)) {
 lean_ctor_release(x_224, 0);
 lean_ctor_release(x_224, 1);
 x_300 = x_224;
} else {
 lean_dec_ref(x_224);
 x_300 = lean_box(0);
}
x_301 = lean_box(0);
x_302 = lean_nat_add(x_227, x_216);
lean_dec(x_227);
lean_inc(x_203);
x_303 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_303, 0, x_203);
lean_ctor_set(x_303, 1, x_301);
lean_ctor_set(x_303, 2, x_298);
x_304 = lean_array_uset(x_228, x_297, x_303);
x_305 = lean_unsigned_to_nat(2u);
x_306 = lean_nat_shiftl(x_302, x_305);
x_307 = lean_unsigned_to_nat(3u);
x_308 = lean_nat_div(x_306, x_307);
lean_dec(x_306);
x_309 = lean_array_get_size(x_304);
x_310 = lean_nat_dec_le(x_308, x_309);
lean_dec(x_309);
lean_dec(x_308);
if (x_310 == 0)
{
lean_object* x_311; lean_object* x_312; 
x_311 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_304);
if (lean_is_scalar(x_300)) {
 x_312 = lean_alloc_ctor(0, 2, 0);
} else {
 x_312 = x_300;
}
lean_ctor_set(x_312, 0, x_302);
lean_ctor_set(x_312, 1, x_311);
x_231 = x_312;
goto block_293;
}
else
{
lean_object* x_313; 
if (lean_is_scalar(x_300)) {
 x_313 = lean_alloc_ctor(0, 2, 0);
} else {
 x_313 = x_300;
}
lean_ctor_set(x_313, 0, x_302);
lean_ctor_set(x_313, 1, x_304);
x_231 = x_313;
goto block_293;
}
}
else
{
lean_dec(x_298);
lean_dec(x_228);
lean_dec(x_227);
x_231 = x_224;
goto block_293;
}
block_293:
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; 
x_232 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_230);
lean_ctor_set(x_232, 2, x_231);
x_233 = lean_st_ref_set(x_2, x_232, x_225);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_235 = x_233;
} else {
 lean_dec_ref(x_233);
 x_235 = lean_box(0);
}
x_236 = l_Lean_Expr_cleanupAnnotations(x_203);
x_237 = l_Lean_Expr_isApp(x_236);
if (x_237 == 0)
{
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_1);
x_8 = x_234;
goto block_11;
}
else
{
lean_object* x_238; uint8_t x_239; 
lean_inc(x_236);
x_238 = l_Lean_Expr_appFnCleanup___redArg(x_236);
x_239 = l_Lean_Expr_isApp(x_238);
if (x_239 == 0)
{
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_1);
x_8 = x_234;
goto block_11;
}
else
{
lean_object* x_240; uint8_t x_241; 
lean_inc(x_238);
x_240 = l_Lean_Expr_appFnCleanup___redArg(x_238);
x_241 = l_Lean_Expr_isApp(x_240);
if (x_241 == 0)
{
lean_dec(x_240);
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_1);
x_8 = x_234;
goto block_11;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = l_Lean_Expr_appFnCleanup___redArg(x_240);
x_243 = lean_mk_string_unchecked("Eq", 2, 2);
x_244 = l_Lean_Name_mkStr1(x_243);
x_245 = l_Lean_Expr_isConstOf(x_242, x_244);
lean_dec(x_244);
lean_dec(x_242);
if (x_245 == 0)
{
lean_dec(x_238);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_1);
x_8 = x_234;
goto block_11;
}
else
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = lean_ctor_get(x_238, 1);
lean_inc(x_246);
lean_dec(x_238);
x_247 = l_Lean_Expr_cleanupAnnotations(x_246);
x_248 = l_Lean_Expr_isApp(x_247);
if (x_248 == 0)
{
lean_dec(x_247);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_1);
x_4 = x_234;
goto block_7;
}
else
{
lean_object* x_249; uint8_t x_250; 
lean_inc(x_247);
x_249 = l_Lean_Expr_appFnCleanup___redArg(x_247);
x_250 = l_Lean_Expr_isApp(x_249);
if (x_250 == 0)
{
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_1);
x_4 = x_234;
goto block_7;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; 
lean_inc(x_249);
x_251 = l_Lean_Expr_appFnCleanup___redArg(x_249);
x_252 = lean_mk_string_unchecked("Bool", 4, 4);
x_253 = lean_mk_string_unchecked("and", 3, 3);
lean_inc(x_252);
x_254 = l_Lean_Name_mkStr2(x_252, x_253);
x_255 = l_Lean_Expr_isConstOf(x_251, x_254);
lean_dec(x_254);
lean_dec(x_251);
if (x_255 == 0)
{
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_226);
lean_dec(x_1);
x_4 = x_234;
goto block_7;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; 
x_256 = lean_ctor_get(x_236, 1);
lean_inc(x_256);
lean_dec(x_236);
x_257 = l_Lean_Expr_cleanupAnnotations(x_256);
x_258 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_252);
x_259 = l_Lean_Name_mkStr2(x_252, x_258);
x_260 = l_Lean_Expr_isConstOf(x_257, x_259);
lean_dec(x_259);
lean_dec(x_257);
if (x_260 == 0)
{
lean_object* x_261; lean_object* x_262; 
lean_dec(x_252);
lean_dec(x_249);
lean_dec(x_247);
lean_dec(x_226);
lean_dec(x_1);
x_261 = lean_box(0);
if (lean_is_scalar(x_235)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_235;
}
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_234);
return x_262;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; uint8_t x_280; uint8_t x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; uint8_t x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_263 = lean_ctor_get(x_247, 1);
lean_inc(x_263);
lean_dec(x_247);
x_264 = lean_ctor_get(x_249, 1);
lean_inc(x_264);
lean_dec(x_249);
x_265 = lean_ctor_get(x_1, 0);
lean_inc(x_265);
lean_inc(x_264);
x_266 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(x_264);
x_267 = lean_mk_string_unchecked("Std", 3, 3);
x_268 = lean_mk_string_unchecked("Tactic", 6, 6);
x_269 = lean_mk_string_unchecked("BVDecide", 8, 8);
x_270 = lean_mk_string_unchecked("Normalize", 9, 9);
x_271 = lean_mk_string_unchecked("and_left", 8, 8);
lean_inc(x_252);
lean_inc(x_270);
lean_inc(x_269);
lean_inc(x_268);
lean_inc(x_267);
x_272 = l_Lean_Name_mkStr6(x_267, x_268, x_269, x_270, x_252, x_271);
x_273 = lean_box(0);
x_274 = l_Lean_Expr_const___override(x_272, x_273);
x_275 = lean_ctor_get(x_1, 2);
lean_inc(x_275);
lean_dec(x_1);
lean_inc(x_275);
lean_inc(x_263);
lean_inc(x_264);
x_276 = l_Lean_mkApp3(x_274, x_264, x_263, x_275);
x_277 = lean_box(0);
x_278 = lean_box(0);
lean_inc(x_265);
x_279 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_279, 0, x_265);
lean_ctor_set(x_279, 1, x_266);
lean_ctor_set(x_279, 2, x_276);
x_280 = lean_unbox(x_277);
lean_ctor_set_uint8(x_279, sizeof(void*)*3, x_280);
x_281 = lean_unbox(x_278);
lean_ctor_set_uint8(x_279, sizeof(void*)*3 + 1, x_281);
lean_inc(x_263);
x_282 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___lam__0(x_263);
x_283 = lean_mk_string_unchecked("and_right", 9, 9);
x_284 = l_Lean_Name_mkStr6(x_267, x_268, x_269, x_270, x_252, x_283);
x_285 = l_Lean_Expr_const___override(x_284, x_273);
x_286 = l_Lean_mkApp3(x_285, x_264, x_263, x_275);
x_287 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_287, 0, x_265);
lean_ctor_set(x_287, 1, x_282);
lean_ctor_set(x_287, 2, x_286);
x_288 = lean_unbox(x_277);
lean_ctor_set_uint8(x_287, sizeof(void*)*3, x_288);
x_289 = lean_unbox(x_278);
lean_ctor_set_uint8(x_287, sizeof(void*)*3 + 1, x_289);
if (lean_is_scalar(x_226)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_226;
}
lean_ctor_set(x_290, 0, x_279);
lean_ctor_set(x_290, 1, x_287);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
if (lean_is_scalar(x_235)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_235;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_234);
return x_292;
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
else
{
lean_object* x_314; lean_object* x_315; 
lean_dec(x_203);
lean_dec(x_1);
x_314 = lean_box(0);
x_315 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_315, 0, x_314);
lean_ctor_set(x_315, 1, x_201);
return x_315;
}
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
block_11:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_1);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg(x_7, x_2, x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_st_ref_take(x_2, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
x_17 = lean_array_push(x_16, x_7);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
lean_dec(x_13);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_st_ref_set(x_2, x_19, x_14);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_1 = x_8;
x_3 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_dec(x_7);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
lean_dec(x_10);
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = !lean_is_exclusive(x_23);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_23, 1);
lean_ctor_set(x_1, 0, x_26);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_1);
x_1 = x_23;
x_3 = x_24;
goto _start;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_23, 0);
x_29 = lean_ctor_get(x_23, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_23);
lean_ctor_set(x_1, 0, x_29);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_1);
x_1 = x_30;
x_3 = x_24;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_1);
lean_inc(x_32);
x_34 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg(x_32, x_2, x_3);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_take(x_2, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_ctor_get(x_38, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
x_42 = lean_array_push(x_41, x_32);
x_43 = lean_ctor_get(x_38, 2);
lean_inc(x_43);
lean_dec(x_38);
x_44 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_42);
lean_ctor_set(x_44, 2, x_43);
x_45 = lean_st_ref_set(x_2, x_44, x_39);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_1 = x_33;
x_3 = x_46;
goto _start;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_32);
x_48 = lean_ctor_get(x_35, 0);
lean_inc(x_48);
lean_dec(x_35);
x_49 = lean_ctor_get(x_34, 1);
lean_inc(x_49);
lean_dec(x_34);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_33);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_52;
 lean_ctor_set_tag(x_54, 1);
}
lean_ctor_set(x_54, 0, x_50);
lean_ctor_set(x_54, 1, x_53);
x_1 = x_54;
x_3 = x_49;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_3);
lean_inc(x_1);
x_7 = l_Lean_FVarId_getType___redArg(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 2);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_array_get_size(x_14);
x_16 = l_Lean_Expr_hash(x_8);
x_17 = lean_unsigned_to_nat(32u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_shift_right(x_16, x_18);
x_20 = lean_uint64_xor(x_16, x_19);
x_21 = lean_unsigned_to_nat(16u);
x_22 = lean_uint64_of_nat(x_21);
x_23 = lean_uint64_shift_right(x_20, x_22);
x_24 = lean_uint64_xor(x_20, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_sub(x_26, x_28);
x_30 = lean_usize_land(x_25, x_29);
x_31 = lean_array_uget(x_14, x_30);
lean_dec(x_14);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_8, x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_inc(x_1);
x_33 = l_Lean_FVarId_getDecl___redArg(x_1, x_3, x_4, x_5, x_13);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_89; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_89 = lean_ctor_get(x_34, 2);
lean_inc(x_89);
lean_dec(x_34);
x_36 = x_89;
goto block_88;
block_88:
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; 
lean_inc(x_1);
x_37 = l_Lean_Expr_fvar___override(x_1);
x_38 = lean_box(0);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_8);
lean_ctor_set(x_40, 2, x_37);
x_41 = lean_unbox(x_38);
lean_ctor_set_uint8(x_40, sizeof(void*)*3, x_41);
x_42 = lean_unbox(x_39);
lean_ctor_set_uint8(x_40, sizeof(void*)*3 + 1, x_42);
x_43 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_trySplit___redArg(x_40, x_2, x_35);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
if (lean_obj_tag(x_44) == 0)
{
uint8_t x_45; 
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = lean_box(0);
lean_ctor_set(x_43, 0, x_47);
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_43, 1);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_48);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_51 = lean_ctor_get(x_44, 0);
lean_inc(x_51);
lean_dec(x_44);
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_ctor_get(x_51, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_55 = lean_st_ref_take(x_2, x_52);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_array_push(x_59, x_1);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 2);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = lean_st_ref_set(x_2, x_63, x_58);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_66 = lean_ctor_get(x_64, 1);
x_67 = lean_ctor_get(x_64, 0);
lean_dec(x_67);
x_68 = lean_box(0);
lean_ctor_set_tag(x_64, 1);
lean_ctor_set(x_64, 1, x_68);
lean_ctor_set(x_64, 0, x_54);
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 1, x_64);
lean_ctor_set(x_55, 0, x_53);
x_69 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg(x_55, x_2, x_66);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_64, 1);
lean_inc(x_70);
lean_dec(x_64);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_54);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set_tag(x_55, 1);
lean_ctor_set(x_55, 1, x_72);
lean_ctor_set(x_55, 0, x_53);
x_73 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg(x_55, x_2, x_70);
return x_73;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_74 = lean_ctor_get(x_55, 0);
x_75 = lean_ctor_get(x_55, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_55);
x_76 = lean_ctor_get(x_74, 0);
lean_inc(x_76);
x_77 = lean_array_push(x_76, x_1);
x_78 = lean_ctor_get(x_74, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_74, 2);
lean_inc(x_79);
lean_dec(x_74);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
lean_ctor_set(x_80, 2, x_79);
x_81 = lean_st_ref_set(x_2, x_80, x_75);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_83 = x_81;
} else {
 lean_dec_ref(x_81);
 x_83 = lean_box(0);
}
x_84 = lean_box(0);
if (lean_is_scalar(x_83)) {
 x_85 = lean_alloc_ctor(1, 2, 0);
} else {
 x_85 = x_83;
 lean_ctor_set_tag(x_85, 1);
}
lean_ctor_set(x_85, 0, x_54);
lean_ctor_set(x_85, 1, x_84);
x_86 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_86, 0, x_53);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_splitAnds___redArg(x_86, x_2, x_82);
return x_87;
}
}
}
}
else
{
uint8_t x_90; 
lean_dec(x_8);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_33);
if (x_90 == 0)
{
return x_33;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_33, 0);
x_92 = lean_ctor_get(x_33, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_33);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_8);
lean_dec(x_3);
x_94 = lean_st_ref_take(x_2, x_13);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
x_98 = lean_array_push(x_97, x_1);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_95, 2);
lean_inc(x_100);
lean_dec(x_95);
x_101 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
lean_ctor_set(x_101, 2, x_100);
x_102 = lean_st_ref_set(x_2, x_101, x_96);
x_103 = !lean_is_exclusive(x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_102, 0);
lean_dec(x_104);
x_105 = lean_box(0);
lean_ctor_set(x_102, 0, x_105);
return x_102;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_3);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_7);
if (x_109 == 0)
{
return x_7;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_7, 0);
x_111 = lean_ctor_get(x_7, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_7);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___redArg(x_1, x_2, x_3, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_6);
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processFVar___redArg(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_2, x_16);
x_2 = x_17;
x_4 = x_13;
x_9 = x_14;
goto _start;
}
else
{
lean_dec(x_6);
return x_12;
}
}
else
{
lean_object* x_19; 
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg___lam__0), 7, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
return x_10;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_7 = l_Lean_Meta_getPropHyps(x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_9);
x_13 = lean_box(0);
x_14 = lean_nat_dec_lt(x_11, x_12);
if (x_14 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_12, x_12);
if (x_15 == 0)
{
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_ctor_set(x_7, 0, x_13);
return x_7;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
lean_free_object(x_7);
x_16 = lean_usize_of_nat(x_11);
x_17 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg(x_9, x_16, x_17, x_13, x_1, x_2, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_9);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = lean_ctor_get(x_7, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_7);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_19);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_20);
return x_25;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_22, x_22);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_20);
return x_27;
}
else
{
size_t x_28; size_t x_29; lean_object* x_30; 
x_28 = lean_usize_of_nat(x_21);
x_29 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_30 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg(x_19, x_28, x_29, x_23, x_1, x_2, x_4, x_5, x_20);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_19);
return x_30;
}
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_7);
if (x_31 == 0)
{
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_7, 0);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_7);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___lam__0___boxed), 6, 0);
x_9 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_unsigned_to_nat(8u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_11, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_10);
x_20 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_10);
lean_ctor_set(x_20, 2, x_19);
x_21 = lean_st_mk_ref(x_20, x_8);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_22);
lean_inc(x_1);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass_processGoal(x_1, x_22, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_st_ref_get(x_22, x_25);
lean_dec(x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
x_32 = l_Array_isEmpty___redArg(x_31);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_33 = l_Lean_MVarId_assertHypotheses(x_1, x_31, x_4, x_5, x_6, x_7, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_MVarId_tryClearMany(x_36, x_30, x_4, x_5, x_6, x_7, x_35);
lean_dec(x_30);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_37, 0);
x_42 = lean_ctor_get(x_37, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_37);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_41);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = !lean_is_exclusive(x_37);
if (x_45 == 0)
{
return x_37;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_37, 0);
x_47 = lean_ctor_get(x_37, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_37);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_49 = !lean_is_exclusive(x_33);
if (x_49 == 0)
{
return x_33;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_33, 0);
x_51 = lean_ctor_get(x_33, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_33);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_26, 0, x_53);
return x_26;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_ctor_get(x_26, 0);
x_55 = lean_ctor_get(x_26, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_26);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = l_Array_isEmpty___redArg(x_57);
if (x_58 == 0)
{
lean_object* x_59; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_59 = l_Lean_MVarId_assertHypotheses(x_1, x_57, x_4, x_5, x_6, x_7, x_55);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = l_Lean_MVarId_tryClearMany(x_62, x_56, x_4, x_5, x_6, x_7, x_61);
lean_dec(x_56);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_73 = lean_ctor_get(x_59, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_59, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_75 = x_59;
} else {
 lean_dec_ref(x_59);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(1, 2, 0);
} else {
 x_76 = x_75;
}
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_74);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; 
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_1);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_55);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_22);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_24);
if (x_79 == 0)
{
return x_24;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_24, 0);
x_81 = lean_ctor_get(x_24, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_24);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass___lam__0___boxed), 8, 0);
x_2 = lean_mk_string_unchecked("andFlattening", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
lean_object* initialize_Std_Tactic_BVDecide_Normalize_Bool(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_AndFlatten(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Tactic_BVDecide_Normalize_Bool(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_andFlatteningPass);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
