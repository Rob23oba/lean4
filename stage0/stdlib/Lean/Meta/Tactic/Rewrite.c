// Lean compiler output
// Module: Lean.Meta.Tactic.Rewrite
// Imports: Lean.Meta.AppBuilder Lean.Meta.MatchUtil Lean.Meta.KAbstract Lean.Meta.Check Lean.Meta.Tactic.Util Lean.Meta.Tactic.Apply Lean.Meta.BinderNameHint
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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_MVarId_checkNotAssigned(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_resolveBinderNameHint(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
lean_object* l_Lean_Meta_postprocessAppMVars(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
uint8_t l_Array_contains___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_mkApp6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasBinderNameHint(lean_object*);
lean_object* l_Lean_Meta_kabstract(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isMVar(lean_object*);
lean_object* l_Lean_Meta_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
extern lean_object* l_Lean_Meta_tactic_skipAssignedInstances;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_getMVarsNoDelayed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l_Lean_Meta_matchEq_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Expr_mvarId_x21(x_5);
lean_dec(x_5);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = l_Array_contains___at___Lean_Elab_Term_logUnassignedUsingErrorInfos_spec__0(x_1, x_13);
if (x_14 == 0)
{
lean_object* x_15; 
x_15 = lean_array_push(x_5, x_13);
x_6 = x_15;
goto block_11;
}
else
{
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_2, x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_18 = lean_array_uget(x_1, x_2);
x_22 = l_Lean_MVarId_isAssigned___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__0(x_18, x_5, x_6, x_7, x_8, x_9);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
lean_dec(x_22);
x_19 = x_25;
goto block_21;
}
else
{
lean_object* x_26; 
lean_dec(x_18);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_10 = x_4;
x_11 = x_26;
goto block_16;
}
block_21:
{
lean_object* x_20; 
x_20 = lean_array_push(x_4, x_18);
x_10 = x_20;
x_11 = x_19;
goto block_16;
}
}
else
{
lean_object* x_27; 
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_4);
lean_ctor_set(x_27, 1, x_9);
return x_27;
}
block_16:
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_2, x_13);
x_2 = x_14;
x_4 = x_10;
x_9 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_expr_instantiate1(x_1, x_3);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_10 = lean_infer_type(x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_Meta_isExprDefEq(x_11, x_2, x_4, x_5, x_6, x_7, x_12);
lean_dec(x_4);
return x_13;
}
else
{
uint8_t x_14; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_14 = !lean_is_exclusive(x_10);
if (x_14 == 0)
{
return x_10;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_10, 0);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_10);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; 
lean_inc(x_2);
lean_inc(x_1);
x_42 = l_Lean_MVarId_checkNotAssigned(x_1, x_2, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
x_44 = lean_infer_type(x_3, x_7, x_8, x_9, x_10, x_43);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_45, x_8, x_46);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 lean_ctor_release(x_47, 1);
 x_50 = x_47;
} else {
 lean_dec_ref(x_47);
 x_50 = lean_box(0);
}
x_51 = lean_box(0);
x_52 = lean_box(0);
x_53 = lean_unbox(x_52);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_54 = l_Lean_Meta_forallMetaTelescopeReducing(x_48, x_51, x_53, x_7, x_8, x_9, x_10, x_49);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; uint8_t x_471; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_56, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_56, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_56)) {
 lean_ctor_release(x_56, 0);
 lean_ctor_release(x_56, 1);
 x_62 = x_56;
} else {
 lean_dec_ref(x_56);
 x_62 = lean_box(0);
}
lean_inc(x_3);
x_467 = l_Lean_mkAppN(x_3, x_58);
x_468 = lean_mk_string_unchecked("Iff", 3, 3);
x_469 = l_Lean_Name_mkStr1(x_468);
x_470 = lean_unsigned_to_nat(2u);
x_471 = l_Lean_Expr_isAppOfArity(x_61, x_469, x_470);
lean_dec(x_469);
if (x_471 == 0)
{
x_419 = x_467;
x_420 = x_61;
x_421 = x_7;
x_422 = x_8;
x_423 = x_9;
x_424 = x_10;
x_425 = x_57;
goto block_466;
}
else
{
lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; 
x_472 = l_Lean_Expr_appFn_x21(x_61);
x_473 = l_Lean_Expr_appArg_x21(x_472);
lean_dec(x_472);
x_474 = l_Lean_Expr_appArg_x21(x_61);
lean_dec(x_61);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_474);
lean_inc(x_473);
x_475 = l_Lean_Meta_mkEq(x_473, x_474, x_7, x_8, x_9, x_10, x_57);
if (lean_obj_tag(x_475) == 0)
{
lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_ctor_get(x_475, 1);
lean_inc(x_477);
lean_dec(x_475);
x_478 = lean_mk_string_unchecked("propext", 7, 7);
x_479 = l_Lean_Name_mkStr1(x_478);
x_480 = lean_box(0);
x_481 = l_Lean_Expr_const___override(x_479, x_480);
x_482 = l_Lean_mkApp3(x_481, x_473, x_474, x_467);
x_419 = x_482;
x_420 = x_476;
x_421 = x_7;
x_422 = x_8;
x_423 = x_9;
x_424 = x_10;
x_425 = x_477;
goto block_466;
}
else
{
uint8_t x_483; 
lean_dec(x_474);
lean_dec(x_473);
lean_dec(x_467);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_483 = !lean_is_exclusive(x_475);
if (x_483 == 0)
{
return x_475;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; 
x_484 = lean_ctor_get(x_475, 0);
x_485 = lean_ctor_get(x_475, 1);
lean_inc(x_485);
lean_inc(x_484);
lean_dec(x_475);
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
return x_486;
}
}
}
block_91:
{
lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_71 = lean_box(0);
x_72 = lean_unbox(x_71);
lean_inc(x_63);
lean_inc(x_65);
lean_inc(x_66);
lean_inc(x_64);
x_73 = l_Lean_Meta_postprocessAppMVars(x_2, x_1, x_58, x_60, x_70, x_72, x_64, x_66, x_65, x_63, x_68);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; size_t x_75; lean_object* x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_array_size(x_58);
x_76 = lean_unsigned_to_nat(0u);
x_77 = lean_usize_of_nat(x_76);
x_78 = l_Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__0(x_75, x_77, x_58);
x_79 = lean_array_get_size(x_78);
x_80 = lean_mk_empty_array_with_capacity(x_76);
x_81 = lean_nat_dec_lt(x_76, x_79);
if (x_81 == 0)
{
lean_dec(x_79);
lean_dec(x_78);
x_22 = x_63;
x_23 = x_64;
x_24 = x_77;
x_25 = x_65;
x_26 = x_66;
x_27 = x_67;
x_28 = x_69;
x_29 = x_76;
x_30 = x_80;
x_31 = x_74;
goto block_41;
}
else
{
uint8_t x_82; 
x_82 = lean_nat_dec_le(x_79, x_79);
if (x_82 == 0)
{
lean_dec(x_79);
lean_dec(x_78);
x_22 = x_63;
x_23 = x_64;
x_24 = x_77;
x_25 = x_65;
x_26 = x_66;
x_27 = x_67;
x_28 = x_69;
x_29 = x_76;
x_30 = x_80;
x_31 = x_74;
goto block_41;
}
else
{
size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_84 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(x_78, x_77, x_83, x_80, x_64, x_66, x_65, x_63, x_74);
lean_dec(x_78);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_22 = x_63;
x_23 = x_64;
x_24 = x_77;
x_25 = x_65;
x_26 = x_66;
x_27 = x_67;
x_28 = x_69;
x_29 = x_76;
x_30 = x_85;
x_31 = x_86;
goto block_41;
}
}
}
else
{
uint8_t x_87; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_58);
lean_dec(x_3);
x_87 = !lean_is_exclusive(x_73);
if (x_87 == 0)
{
return x_73;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_73, 0);
x_89 = lean_ctor_get(x_73, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_73);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_161:
{
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_105, 1);
lean_inc(x_106);
lean_dec(x_105);
lean_inc(x_95);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_99);
x_107 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_box(0), x_102, x_99, x_94, x_92, x_96, x_97, x_95, x_106);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; uint8_t x_109; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_unbox(x_108);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; uint8_t x_121; 
lean_dec(x_108);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_93);
lean_dec(x_60);
lean_dec(x_58);
lean_dec(x_3);
x_110 = lean_ctor_get(x_107, 1);
lean_inc(x_110);
lean_dec(x_107);
x_111 = lean_mk_string_unchecked("motive is dependent", 19, 19);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
x_113 = l_Lean_MessageData_ofExpr(x_104);
x_114 = l_Lean_indentD(x_113);
if (lean_is_scalar(x_62)) {
 x_115 = lean_alloc_ctor(7, 2, 0);
} else {
 x_115 = x_62;
 lean_ctor_set_tag(x_115, 7);
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("", 0, 0);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
if (lean_is_scalar(x_59)) {
 x_118 = lean_alloc_ctor(7, 2, 0);
} else {
 x_118 = x_59;
 lean_ctor_set_tag(x_118, 7);
}
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_119, x_92, x_96, x_97, x_95, x_110);
lean_dec(x_95);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_92);
x_121 = !lean_is_exclusive(x_120);
if (x_121 == 0)
{
return x_120;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_120, 0);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_120);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_107, 1);
lean_inc(x_125);
lean_dec(x_107);
lean_inc(x_95);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_99);
x_126 = l_Lean_Meta_getLevel(x_99, x_92, x_96, x_97, x_95, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_95);
lean_inc(x_97);
lean_inc(x_96);
lean_inc(x_92);
lean_inc(x_100);
x_129 = l_Lean_Meta_getLevel(x_100, x_92, x_96, x_97, x_95, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; uint8_t x_141; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_mk_string_unchecked("congrArg", 8, 8);
x_133 = l_Lean_Name_mkStr1(x_132);
x_134 = lean_box(0);
if (lean_is_scalar(x_62)) {
 x_135 = lean_alloc_ctor(1, 2, 0);
} else {
 x_135 = x_62;
 lean_ctor_set_tag(x_135, 1);
}
lean_ctor_set(x_135, 0, x_130);
lean_ctor_set(x_135, 1, x_134);
if (lean_is_scalar(x_59)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_59;
 lean_ctor_set_tag(x_136, 1);
}
lean_ctor_set(x_136, 0, x_127);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Expr_const___override(x_133, x_136);
x_138 = l_Lean_mkApp6(x_137, x_99, x_100, x_98, x_101, x_104, x_103);
x_139 = lean_ctor_get(x_97, 2);
lean_inc(x_139);
x_140 = l_Lean_Meta_tactic_skipAssignedInstances;
x_141 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_139, x_140);
lean_dec(x_139);
if (x_141 == 0)
{
uint8_t x_142; 
x_142 = lean_unbox(x_108);
lean_dec(x_108);
x_63 = x_95;
x_64 = x_92;
x_65 = x_97;
x_66 = x_96;
x_67 = x_138;
x_68 = x_131;
x_69 = x_93;
x_70 = x_142;
goto block_91;
}
else
{
lean_object* x_143; uint8_t x_144; 
lean_dec(x_108);
x_143 = lean_box(0);
x_144 = lean_unbox(x_143);
x_63 = x_95;
x_64 = x_92;
x_65 = x_97;
x_66 = x_96;
x_67 = x_138;
x_68 = x_131;
x_69 = x_93;
x_70 = x_144;
goto block_91;
}
}
else
{
uint8_t x_145; 
lean_dec(x_127);
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = !lean_is_exclusive(x_129);
if (x_145 == 0)
{
return x_129;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_129, 0);
x_147 = lean_ctor_get(x_129, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_129);
x_148 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_148, 0, x_146);
lean_ctor_set(x_148, 1, x_147);
return x_148;
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_108);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_126);
if (x_149 == 0)
{
return x_126;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_126, 0);
x_151 = lean_ctor_get(x_126, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_126);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_107);
if (x_153 == 0)
{
return x_107;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_107, 0);
x_155 = lean_ctor_get(x_107, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_107);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_157 = !lean_is_exclusive(x_105);
if (x_157 == 0)
{
return x_105;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_105, 0);
x_159 = lean_ctor_get(x_105, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_105);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
block_216:
{
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_164);
x_179 = lean_mk_string_unchecked("motive is not type correct:", 27, 27);
x_180 = l_Lean_stringToMessageData(x_179);
lean_dec(x_179);
lean_inc(x_177);
x_181 = l_Lean_MessageData_ofExpr(x_177);
x_182 = l_Lean_indentD(x_181);
if (lean_is_scalar(x_50)) {
 x_183 = lean_alloc_ctor(7, 2, 0);
} else {
 x_183 = x_50;
 lean_ctor_set_tag(x_183, 7);
}
lean_ctor_set(x_183, 0, x_180);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_mk_string_unchecked("\nError: ", 8, 8);
x_185 = l_Lean_stringToMessageData(x_184);
lean_dec(x_184);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_185);
x_187 = l_Lean_Exception_toMessageData(x_171);
x_188 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
x_189 = lean_mk_string_unchecked("\n\nExplanation: The rewrite tactic rewrites an expression 'e' using an equality 'a = b' by the following process. First, it looks for all 'a' in 'e'. Second, it tries to abstract these occurrences of 'a' to create a function 'm := fun _a => ...', called the *motive*, with the property that 'm a' is definitionally equal to 'e'. Third, we observe that '", 352, 352);
x_190 = l_Lean_stringToMessageData(x_189);
lean_dec(x_189);
x_191 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_mk_string_unchecked("congrArg", 8, 8);
x_193 = l_Lean_Name_mkStr1(x_192);
x_194 = l_Lean_MessageData_ofConstName(x_193, x_178);
x_195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_195, 0, x_191);
lean_ctor_set(x_195, 1, x_194);
x_196 = lean_mk_string_unchecked("' implies that 'm a = m b', which can be used with lemmas such as '", 67, 67);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_195);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_mk_string_unchecked("Eq", 2, 2);
x_200 = lean_mk_string_unchecked("mpr", 3, 3);
x_201 = l_Lean_Name_mkStr2(x_199, x_200);
x_202 = l_Lean_MessageData_ofConstName(x_201, x_178);
x_203 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_203, 0, x_198);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_mk_string_unchecked("' to change the goal. However, if 'e' depends on specific properties of 'a', then the motive 'm' might not typecheck.\n\nPossible solutions: use rewrite's 'occs' configuration option to limit which occurrences are rewritten, or use 'simp' or 'conv' mode, which have strategies for certain kinds of dependencies (these tactics can handle proofs and '", 347, 347);
x_205 = l_Lean_stringToMessageData(x_204);
lean_dec(x_204);
x_206 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_206, 0, x_203);
lean_ctor_set(x_206, 1, x_205);
x_207 = lean_mk_string_unchecked("Decidable", 9, 9);
x_208 = l_Lean_Name_mkStr1(x_207);
x_209 = l_Lean_MessageData_ofConstName(x_208, x_178);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_206);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("' instances whose types depend on the rewritten term, and 'simp' can apply user-defined '@[congr]' theorems as well).", 117, 117);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_213);
lean_inc(x_1);
lean_inc(x_2);
x_215 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_214, x_162, x_168, x_169, x_166, x_163);
x_92 = x_162;
x_93 = x_165;
x_94 = x_167;
x_95 = x_166;
x_96 = x_168;
x_97 = x_169;
x_98 = x_170;
x_99 = x_172;
x_100 = x_173;
x_101 = x_174;
x_102 = x_176;
x_103 = x_175;
x_104 = x_177;
x_105 = x_215;
goto block_161;
}
else
{
lean_dec(x_171);
lean_dec(x_163);
lean_dec(x_50);
x_92 = x_162;
x_93 = x_165;
x_94 = x_167;
x_95 = x_166;
x_96 = x_168;
x_97 = x_169;
x_98 = x_170;
x_99 = x_172;
x_100 = x_173;
x_101 = x_174;
x_102 = x_176;
x_103 = x_175;
x_104 = x_177;
x_105 = x_164;
goto block_161;
}
}
block_248:
{
lean_object* x_230; 
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
x_230 = lean_infer_type(x_221, x_225, x_226, x_227, x_228, x_229);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; uint8_t x_237; lean_object* x_238; lean_object* x_239; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
lean_inc(x_231);
x_233 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__0___boxed), 8, 2);
lean_closure_set(x_233, 0, x_217);
lean_closure_set(x_233, 1, x_231);
x_234 = lean_mk_string_unchecked("_a", 2, 2);
x_235 = l_Lean_Name_mkStr1(x_234);
x_236 = lean_box(0);
x_237 = lean_unbox(x_236);
lean_inc(x_220);
lean_inc(x_235);
x_238 = l_Lean_Expr_lam___override(x_235, x_220, x_219, x_237);
lean_inc(x_228);
lean_inc(x_227);
lean_inc(x_226);
lean_inc(x_225);
lean_inc(x_238);
x_239 = l_Lean_Meta_check(x_238, x_225, x_226, x_227, x_228, x_232);
if (lean_obj_tag(x_239) == 0)
{
lean_dec(x_50);
x_92 = x_225;
x_93 = x_224;
x_94 = x_233;
x_95 = x_228;
x_96 = x_226;
x_97 = x_227;
x_98 = x_218;
x_99 = x_220;
x_100 = x_231;
x_101 = x_222;
x_102 = x_235;
x_103 = x_223;
x_104 = x_238;
x_105 = x_239;
goto block_161;
}
else
{
lean_object* x_240; lean_object* x_241; uint8_t x_242; 
x_240 = lean_ctor_get(x_239, 0);
lean_inc(x_240);
x_241 = lean_ctor_get(x_239, 1);
lean_inc(x_241);
x_242 = l_Lean_Exception_isInterrupt(x_240);
if (x_242 == 0)
{
uint8_t x_243; 
x_243 = l_Lean_Exception_isRuntime(x_240);
x_162 = x_225;
x_163 = x_241;
x_164 = x_239;
x_165 = x_224;
x_166 = x_228;
x_167 = x_233;
x_168 = x_226;
x_169 = x_227;
x_170 = x_218;
x_171 = x_240;
x_172 = x_220;
x_173 = x_231;
x_174 = x_222;
x_175 = x_223;
x_176 = x_235;
x_177 = x_238;
x_178 = x_243;
goto block_216;
}
else
{
x_162 = x_225;
x_163 = x_241;
x_164 = x_239;
x_165 = x_224;
x_166 = x_228;
x_167 = x_233;
x_168 = x_226;
x_169 = x_227;
x_170 = x_218;
x_171 = x_240;
x_172 = x_220;
x_173 = x_231;
x_174 = x_222;
x_175 = x_223;
x_176 = x_235;
x_177 = x_238;
x_178 = x_242;
goto block_216;
}
}
}
else
{
uint8_t x_244; 
lean_dec(x_228);
lean_dec(x_227);
lean_dec(x_226);
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_223);
lean_dec(x_222);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_244 = !lean_is_exclusive(x_230);
if (x_244 == 0)
{
return x_230;
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_230, 0);
x_246 = lean_ctor_get(x_230, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_230);
x_247 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_247, 0, x_245);
lean_ctor_set(x_247, 1, x_246);
return x_247;
}
}
}
block_418:
{
lean_object* x_259; uint8_t x_260; 
x_259 = l_Lean_Expr_getAppFn(x_252);
x_260 = l_Lean_Expr_isMVar(x_259);
lean_dec(x_259);
if (x_260 == 0)
{
lean_object* x_261; uint8_t x_262; 
lean_dec(x_251);
x_261 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_4, x_255, x_258);
x_262 = !lean_is_exclusive(x_261);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; uint8_t x_267; uint8_t x_268; uint8_t x_269; uint8_t x_270; uint8_t x_271; uint8_t x_272; uint8_t x_273; uint8_t x_274; uint8_t x_275; uint8_t x_276; uint8_t x_277; uint8_t x_278; uint8_t x_279; uint8_t x_280; uint8_t x_281; uint8_t x_282; uint8_t x_283; uint8_t x_284; lean_object* x_285; uint64_t x_286; uint8_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint8_t x_294; uint8_t x_295; lean_object* x_296; lean_object* x_297; 
x_263 = lean_ctor_get(x_261, 0);
x_264 = lean_ctor_get(x_261, 1);
x_265 = lean_ctor_get(x_5, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_254, 0);
lean_inc(x_266);
x_267 = lean_ctor_get_uint8(x_266, 0);
x_268 = lean_ctor_get_uint8(x_266, 1);
x_269 = lean_ctor_get_uint8(x_266, 2);
x_270 = lean_ctor_get_uint8(x_266, 3);
x_271 = lean_ctor_get_uint8(x_266, 4);
x_272 = lean_ctor_get_uint8(x_266, 5);
x_273 = lean_ctor_get_uint8(x_266, 6);
x_274 = lean_ctor_get_uint8(x_266, 7);
x_275 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_276 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_277 = lean_ctor_get_uint8(x_266, 10);
x_278 = lean_ctor_get_uint8(x_266, 11);
x_279 = lean_ctor_get_uint8(x_266, 12);
x_280 = lean_ctor_get_uint8(x_266, 13);
x_281 = lean_ctor_get_uint8(x_266, 14);
x_282 = lean_ctor_get_uint8(x_266, 15);
x_283 = lean_ctor_get_uint8(x_266, 16);
x_284 = lean_ctor_get_uint8(x_266, 17);
lean_dec(x_266);
x_285 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_285, 0, x_267);
lean_ctor_set_uint8(x_285, 1, x_268);
lean_ctor_set_uint8(x_285, 2, x_269);
lean_ctor_set_uint8(x_285, 3, x_270);
lean_ctor_set_uint8(x_285, 4, x_271);
lean_ctor_set_uint8(x_285, 5, x_272);
lean_ctor_set_uint8(x_285, 6, x_273);
lean_ctor_set_uint8(x_285, 7, x_274);
lean_ctor_set_uint8(x_285, 8, x_275);
lean_ctor_set_uint8(x_285, 9, x_276);
lean_ctor_set_uint8(x_285, 10, x_277);
lean_ctor_set_uint8(x_285, 11, x_278);
lean_ctor_set_uint8(x_285, 12, x_279);
lean_ctor_set_uint8(x_285, 13, x_280);
lean_ctor_set_uint8(x_285, 14, x_281);
lean_ctor_set_uint8(x_285, 15, x_282);
lean_ctor_set_uint8(x_285, 16, x_283);
lean_ctor_set_uint8(x_285, 17, x_284);
x_286 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_285);
x_287 = lean_ctor_get_uint8(x_254, sizeof(void*)*7 + 8);
x_288 = lean_ctor_get(x_254, 1);
lean_inc(x_288);
x_289 = lean_ctor_get(x_254, 2);
lean_inc(x_289);
x_290 = lean_ctor_get(x_254, 3);
lean_inc(x_290);
x_291 = lean_ctor_get(x_254, 4);
lean_inc(x_291);
x_292 = lean_ctor_get(x_254, 5);
lean_inc(x_292);
x_293 = lean_ctor_get(x_254, 6);
lean_inc(x_293);
x_294 = lean_ctor_get_uint8(x_254, sizeof(void*)*7 + 9);
x_295 = lean_ctor_get_uint8(x_254, sizeof(void*)*7 + 10);
x_296 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_296, 0, x_285);
lean_ctor_set(x_296, 1, x_288);
lean_ctor_set(x_296, 2, x_289);
lean_ctor_set(x_296, 3, x_290);
lean_ctor_set(x_296, 4, x_291);
lean_ctor_set(x_296, 5, x_292);
lean_ctor_set(x_296, 6, x_293);
lean_ctor_set_uint64(x_296, sizeof(void*)*7, x_286);
lean_ctor_set_uint8(x_296, sizeof(void*)*7 + 8, x_287);
lean_ctor_set_uint8(x_296, sizeof(void*)*7 + 9, x_294);
lean_ctor_set_uint8(x_296, sizeof(void*)*7 + 10, x_295);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_252);
lean_inc(x_263);
x_297 = l_Lean_Meta_kabstract(x_263, x_252, x_265, x_296, x_255, x_256, x_257, x_264);
lean_dec(x_296);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; uint8_t x_300; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = l_Lean_Expr_hasLooseBVars(x_298);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; 
lean_dec(x_298);
lean_dec(x_263);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
x_301 = lean_mk_string_unchecked("did not find instance of the pattern in the target expression", 61, 61);
x_302 = l_Lean_stringToMessageData(x_301);
lean_dec(x_301);
x_303 = l_Lean_indentExpr(x_252);
lean_ctor_set_tag(x_261, 7);
lean_ctor_set(x_261, 1, x_303);
lean_ctor_set(x_261, 0, x_302);
x_304 = lean_mk_string_unchecked("", 0, 0);
x_305 = l_Lean_stringToMessageData(x_304);
lean_dec(x_304);
x_306 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_306, 0, x_261);
lean_ctor_set(x_306, 1, x_305);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_307, x_254, x_255, x_256, x_257, x_299);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
x_309 = !lean_is_exclusive(x_308);
if (x_309 == 0)
{
return x_308;
}
else
{
lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_310 = lean_ctor_get(x_308, 0);
x_311 = lean_ctor_get(x_308, 1);
lean_inc(x_311);
lean_inc(x_310);
lean_dec(x_308);
x_312 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_312, 0, x_310);
lean_ctor_set(x_312, 1, x_311);
return x_312;
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; 
lean_free_object(x_261);
x_313 = lean_expr_instantiate1(x_298, x_253);
x_314 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_313, x_255, x_299);
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
x_317 = l_Lean_Expr_hasBinderNameHint(x_253);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; 
lean_dec(x_316);
lean_dec(x_315);
x_318 = lean_ctor_get(x_314, 0);
lean_inc(x_318);
x_319 = lean_ctor_get(x_314, 1);
lean_inc(x_319);
lean_dec(x_314);
lean_inc(x_298);
x_217 = x_298;
x_218 = x_252;
x_219 = x_298;
x_220 = x_249;
x_221 = x_263;
x_222 = x_253;
x_223 = x_250;
x_224 = x_318;
x_225 = x_254;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_319;
goto block_248;
}
else
{
lean_object* x_320; 
lean_dec(x_314);
lean_inc(x_257);
lean_inc(x_256);
x_320 = l_Lean_Expr_resolveBinderNameHint(x_315, x_256, x_257, x_316);
if (lean_obj_tag(x_320) == 0)
{
lean_object* x_321; lean_object* x_322; 
x_321 = lean_ctor_get(x_320, 0);
lean_inc(x_321);
x_322 = lean_ctor_get(x_320, 1);
lean_inc(x_322);
lean_dec(x_320);
lean_inc(x_298);
x_217 = x_298;
x_218 = x_252;
x_219 = x_298;
x_220 = x_249;
x_221 = x_263;
x_222 = x_253;
x_223 = x_250;
x_224 = x_321;
x_225 = x_254;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_322;
goto block_248;
}
else
{
uint8_t x_323; 
lean_dec(x_298);
lean_dec(x_263);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_323 = !lean_is_exclusive(x_320);
if (x_323 == 0)
{
return x_320;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_320, 0);
x_325 = lean_ctor_get(x_320, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_320);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
}
}
}
else
{
uint8_t x_327; 
lean_free_object(x_261);
lean_dec(x_263);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_327 = !lean_is_exclusive(x_297);
if (x_327 == 0)
{
return x_297;
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; 
x_328 = lean_ctor_get(x_297, 0);
x_329 = lean_ctor_get(x_297, 1);
lean_inc(x_329);
lean_inc(x_328);
lean_dec(x_297);
x_330 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_330, 0, x_328);
lean_ctor_set(x_330, 1, x_329);
return x_330;
}
}
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; uint8_t x_336; uint8_t x_337; uint8_t x_338; uint8_t x_339; uint8_t x_340; uint8_t x_341; uint8_t x_342; uint8_t x_343; uint8_t x_344; uint8_t x_345; uint8_t x_346; uint8_t x_347; uint8_t x_348; uint8_t x_349; uint8_t x_350; uint8_t x_351; uint8_t x_352; lean_object* x_353; uint64_t x_354; uint8_t x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; uint8_t x_363; lean_object* x_364; lean_object* x_365; 
x_331 = lean_ctor_get(x_261, 0);
x_332 = lean_ctor_get(x_261, 1);
lean_inc(x_332);
lean_inc(x_331);
lean_dec(x_261);
x_333 = lean_ctor_get(x_5, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_254, 0);
lean_inc(x_334);
x_335 = lean_ctor_get_uint8(x_334, 0);
x_336 = lean_ctor_get_uint8(x_334, 1);
x_337 = lean_ctor_get_uint8(x_334, 2);
x_338 = lean_ctor_get_uint8(x_334, 3);
x_339 = lean_ctor_get_uint8(x_334, 4);
x_340 = lean_ctor_get_uint8(x_334, 5);
x_341 = lean_ctor_get_uint8(x_334, 6);
x_342 = lean_ctor_get_uint8(x_334, 7);
x_343 = lean_ctor_get_uint8(x_5, sizeof(void*)*1 + 1);
x_344 = lean_ctor_get_uint8(x_5, sizeof(void*)*1);
lean_dec(x_5);
x_345 = lean_ctor_get_uint8(x_334, 10);
x_346 = lean_ctor_get_uint8(x_334, 11);
x_347 = lean_ctor_get_uint8(x_334, 12);
x_348 = lean_ctor_get_uint8(x_334, 13);
x_349 = lean_ctor_get_uint8(x_334, 14);
x_350 = lean_ctor_get_uint8(x_334, 15);
x_351 = lean_ctor_get_uint8(x_334, 16);
x_352 = lean_ctor_get_uint8(x_334, 17);
lean_dec(x_334);
x_353 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_353, 0, x_335);
lean_ctor_set_uint8(x_353, 1, x_336);
lean_ctor_set_uint8(x_353, 2, x_337);
lean_ctor_set_uint8(x_353, 3, x_338);
lean_ctor_set_uint8(x_353, 4, x_339);
lean_ctor_set_uint8(x_353, 5, x_340);
lean_ctor_set_uint8(x_353, 6, x_341);
lean_ctor_set_uint8(x_353, 7, x_342);
lean_ctor_set_uint8(x_353, 8, x_343);
lean_ctor_set_uint8(x_353, 9, x_344);
lean_ctor_set_uint8(x_353, 10, x_345);
lean_ctor_set_uint8(x_353, 11, x_346);
lean_ctor_set_uint8(x_353, 12, x_347);
lean_ctor_set_uint8(x_353, 13, x_348);
lean_ctor_set_uint8(x_353, 14, x_349);
lean_ctor_set_uint8(x_353, 15, x_350);
lean_ctor_set_uint8(x_353, 16, x_351);
lean_ctor_set_uint8(x_353, 17, x_352);
x_354 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_353);
x_355 = lean_ctor_get_uint8(x_254, sizeof(void*)*7 + 8);
x_356 = lean_ctor_get(x_254, 1);
lean_inc(x_356);
x_357 = lean_ctor_get(x_254, 2);
lean_inc(x_357);
x_358 = lean_ctor_get(x_254, 3);
lean_inc(x_358);
x_359 = lean_ctor_get(x_254, 4);
lean_inc(x_359);
x_360 = lean_ctor_get(x_254, 5);
lean_inc(x_360);
x_361 = lean_ctor_get(x_254, 6);
lean_inc(x_361);
x_362 = lean_ctor_get_uint8(x_254, sizeof(void*)*7 + 9);
x_363 = lean_ctor_get_uint8(x_254, sizeof(void*)*7 + 10);
x_364 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_364, 0, x_353);
lean_ctor_set(x_364, 1, x_356);
lean_ctor_set(x_364, 2, x_357);
lean_ctor_set(x_364, 3, x_358);
lean_ctor_set(x_364, 4, x_359);
lean_ctor_set(x_364, 5, x_360);
lean_ctor_set(x_364, 6, x_361);
lean_ctor_set_uint64(x_364, sizeof(void*)*7, x_354);
lean_ctor_set_uint8(x_364, sizeof(void*)*7 + 8, x_355);
lean_ctor_set_uint8(x_364, sizeof(void*)*7 + 9, x_362);
lean_ctor_set_uint8(x_364, sizeof(void*)*7 + 10, x_363);
lean_inc(x_257);
lean_inc(x_256);
lean_inc(x_255);
lean_inc(x_252);
lean_inc(x_331);
x_365 = l_Lean_Meta_kabstract(x_331, x_252, x_333, x_364, x_255, x_256, x_257, x_332);
lean_dec(x_364);
if (lean_obj_tag(x_365) == 0)
{
lean_object* x_366; lean_object* x_367; uint8_t x_368; 
x_366 = lean_ctor_get(x_365, 0);
lean_inc(x_366);
x_367 = lean_ctor_get(x_365, 1);
lean_inc(x_367);
lean_dec(x_365);
x_368 = l_Lean_Expr_hasLooseBVars(x_366);
if (x_368 == 0)
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_366);
lean_dec(x_331);
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
x_369 = lean_mk_string_unchecked("did not find instance of the pattern in the target expression", 61, 61);
x_370 = l_Lean_stringToMessageData(x_369);
lean_dec(x_369);
x_371 = l_Lean_indentExpr(x_252);
x_372 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_mk_string_unchecked("", 0, 0);
x_374 = l_Lean_stringToMessageData(x_373);
lean_dec(x_373);
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
x_377 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_376, x_254, x_255, x_256, x_257, x_367);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
x_378 = lean_ctor_get(x_377, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_377, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_377)) {
 lean_ctor_release(x_377, 0);
 lean_ctor_release(x_377, 1);
 x_380 = x_377;
} else {
 lean_dec_ref(x_377);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; uint8_t x_386; 
x_382 = lean_expr_instantiate1(x_366, x_253);
x_383 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_382, x_255, x_367);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_ctor_get(x_383, 1);
lean_inc(x_385);
x_386 = l_Lean_Expr_hasBinderNameHint(x_253);
if (x_386 == 0)
{
lean_object* x_387; lean_object* x_388; 
lean_dec(x_385);
lean_dec(x_384);
x_387 = lean_ctor_get(x_383, 0);
lean_inc(x_387);
x_388 = lean_ctor_get(x_383, 1);
lean_inc(x_388);
lean_dec(x_383);
lean_inc(x_366);
x_217 = x_366;
x_218 = x_252;
x_219 = x_366;
x_220 = x_249;
x_221 = x_331;
x_222 = x_253;
x_223 = x_250;
x_224 = x_387;
x_225 = x_254;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_388;
goto block_248;
}
else
{
lean_object* x_389; 
lean_dec(x_383);
lean_inc(x_257);
lean_inc(x_256);
x_389 = l_Lean_Expr_resolveBinderNameHint(x_384, x_256, x_257, x_385);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; lean_object* x_391; 
x_390 = lean_ctor_get(x_389, 0);
lean_inc(x_390);
x_391 = lean_ctor_get(x_389, 1);
lean_inc(x_391);
lean_dec(x_389);
lean_inc(x_366);
x_217 = x_366;
x_218 = x_252;
x_219 = x_366;
x_220 = x_249;
x_221 = x_331;
x_222 = x_253;
x_223 = x_250;
x_224 = x_390;
x_225 = x_254;
x_226 = x_255;
x_227 = x_256;
x_228 = x_257;
x_229 = x_391;
goto block_248;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_366);
lean_dec(x_331);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_392 = lean_ctor_get(x_389, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_389, 1);
lean_inc(x_393);
if (lean_is_exclusive(x_389)) {
 lean_ctor_release(x_389, 0);
 lean_ctor_release(x_389, 1);
 x_394 = x_389;
} else {
 lean_dec_ref(x_389);
 x_394 = lean_box(0);
}
if (lean_is_scalar(x_394)) {
 x_395 = lean_alloc_ctor(1, 2, 0);
} else {
 x_395 = x_394;
}
lean_ctor_set(x_395, 0, x_392);
lean_ctor_set(x_395, 1, x_393);
return x_395;
}
}
}
}
else
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_331);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_396 = lean_ctor_get(x_365, 0);
lean_inc(x_396);
x_397 = lean_ctor_get(x_365, 1);
lean_inc(x_397);
if (lean_is_exclusive(x_365)) {
 lean_ctor_release(x_365, 0);
 lean_ctor_release(x_365, 1);
 x_398 = x_365;
} else {
 lean_dec_ref(x_365);
 x_398 = lean_box(0);
}
if (lean_is_scalar(x_398)) {
 x_399 = lean_alloc_ctor(1, 2, 0);
} else {
 x_399 = x_398;
}
lean_ctor_set(x_399, 0, x_396);
lean_ctor_set(x_399, 1, x_397);
return x_399;
}
}
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; uint8_t x_414; 
lean_dec(x_253);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_400 = lean_mk_string_unchecked("pattern is a metavariable", 25, 25);
x_401 = l_Lean_stringToMessageData(x_400);
lean_dec(x_400);
x_402 = l_Lean_indentExpr(x_252);
x_403 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_403, 0, x_401);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_mk_string_unchecked("\nfrom equation", 14, 14);
x_405 = l_Lean_stringToMessageData(x_404);
lean_dec(x_404);
x_406 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_406, 0, x_403);
lean_ctor_set(x_406, 1, x_405);
x_407 = l_Lean_indentExpr(x_251);
x_408 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_408, 0, x_406);
lean_ctor_set(x_408, 1, x_407);
x_409 = lean_mk_string_unchecked("", 0, 0);
x_410 = l_Lean_stringToMessageData(x_409);
lean_dec(x_409);
x_411 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_411, 0, x_408);
lean_ctor_set(x_411, 1, x_410);
x_412 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_412, 0, x_411);
x_413 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_412, x_254, x_255, x_256, x_257, x_258);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_255);
lean_dec(x_254);
x_414 = !lean_is_exclusive(x_413);
if (x_414 == 0)
{
return x_413;
}
else
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_415 = lean_ctor_get(x_413, 0);
x_416 = lean_ctor_get(x_413, 1);
lean_inc(x_416);
lean_inc(x_415);
lean_dec(x_413);
x_417 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_417, 0, x_415);
lean_ctor_set(x_417, 1, x_416);
return x_417;
}
}
}
block_466:
{
lean_object* x_426; 
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_420);
x_426 = l_Lean_Meta_matchEq_x3f(x_420, x_421, x_422, x_423, x_424, x_425);
if (lean_obj_tag(x_426) == 0)
{
lean_object* x_427; 
x_427 = lean_ctor_get(x_426, 0);
lean_inc(x_427);
if (lean_obj_tag(x_427) == 0)
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_419);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_428 = lean_ctor_get(x_426, 1);
lean_inc(x_428);
lean_dec(x_426);
x_429 = lean_mk_string_unchecked("equality or iff proof expected", 30, 30);
x_430 = l_Lean_stringToMessageData(x_429);
lean_dec(x_429);
x_431 = l_Lean_indentExpr(x_420);
x_432 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_432, 0, x_430);
lean_ctor_set(x_432, 1, x_431);
x_433 = lean_mk_string_unchecked("", 0, 0);
x_434 = l_Lean_stringToMessageData(x_433);
lean_dec(x_433);
x_435 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_435, 0, x_432);
lean_ctor_set(x_435, 1, x_434);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
x_437 = l_Lean_Meta_throwTacticEx___redArg(x_2, x_1, x_436, x_421, x_422, x_423, x_424, x_428);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
return x_437;
}
else
{
lean_object* x_438; lean_object* x_439; 
x_438 = lean_ctor_get(x_427, 0);
lean_inc(x_438);
lean_dec(x_427);
x_439 = lean_ctor_get(x_438, 1);
lean_inc(x_439);
if (x_6 == 0)
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; 
x_440 = lean_ctor_get(x_426, 1);
lean_inc(x_440);
lean_dec(x_426);
x_441 = lean_ctor_get(x_438, 0);
lean_inc(x_441);
lean_dec(x_438);
x_442 = lean_ctor_get(x_439, 0);
lean_inc(x_442);
x_443 = lean_ctor_get(x_439, 1);
lean_inc(x_443);
lean_dec(x_439);
x_249 = x_441;
x_250 = x_419;
x_251 = x_420;
x_252 = x_442;
x_253 = x_443;
x_254 = x_421;
x_255 = x_422;
x_256 = x_423;
x_257 = x_424;
x_258 = x_440;
goto block_418;
}
else
{
lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; 
lean_dec(x_420);
x_444 = lean_ctor_get(x_426, 1);
lean_inc(x_444);
lean_dec(x_426);
x_445 = lean_ctor_get(x_438, 0);
lean_inc(x_445);
lean_dec(x_438);
x_446 = lean_ctor_get(x_439, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_439, 1);
lean_inc(x_447);
lean_dec(x_439);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_inc(x_421);
x_448 = l_Lean_Meta_mkEqSymm(x_419, x_421, x_422, x_423, x_424, x_444);
if (lean_obj_tag(x_448) == 0)
{
lean_object* x_449; lean_object* x_450; lean_object* x_451; 
x_449 = lean_ctor_get(x_448, 0);
lean_inc(x_449);
x_450 = lean_ctor_get(x_448, 1);
lean_inc(x_450);
lean_dec(x_448);
lean_inc(x_424);
lean_inc(x_423);
lean_inc(x_422);
lean_inc(x_421);
lean_inc(x_446);
lean_inc(x_447);
x_451 = l_Lean_Meta_mkEq(x_447, x_446, x_421, x_422, x_423, x_424, x_450);
if (lean_obj_tag(x_451) == 0)
{
lean_object* x_452; lean_object* x_453; 
x_452 = lean_ctor_get(x_451, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_451, 1);
lean_inc(x_453);
lean_dec(x_451);
x_249 = x_445;
x_250 = x_449;
x_251 = x_452;
x_252 = x_447;
x_253 = x_446;
x_254 = x_421;
x_255 = x_422;
x_256 = x_423;
x_257 = x_424;
x_258 = x_453;
goto block_418;
}
else
{
uint8_t x_454; 
lean_dec(x_449);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_454 = !lean_is_exclusive(x_451);
if (x_454 == 0)
{
return x_451;
}
else
{
lean_object* x_455; lean_object* x_456; lean_object* x_457; 
x_455 = lean_ctor_get(x_451, 0);
x_456 = lean_ctor_get(x_451, 1);
lean_inc(x_456);
lean_inc(x_455);
lean_dec(x_451);
x_457 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_457, 0, x_455);
lean_ctor_set(x_457, 1, x_456);
return x_457;
}
}
}
else
{
uint8_t x_458; 
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_458 = !lean_is_exclusive(x_448);
if (x_458 == 0)
{
return x_448;
}
else
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; 
x_459 = lean_ctor_get(x_448, 0);
x_460 = lean_ctor_get(x_448, 1);
lean_inc(x_460);
lean_inc(x_459);
lean_dec(x_448);
x_461 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_461, 0, x_459);
lean_ctor_set(x_461, 1, x_460);
return x_461;
}
}
}
}
}
else
{
uint8_t x_462; 
lean_dec(x_424);
lean_dec(x_423);
lean_dec(x_422);
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_419);
lean_dec(x_62);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_50);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_462 = !lean_is_exclusive(x_426);
if (x_462 == 0)
{
return x_426;
}
else
{
lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_463 = lean_ctor_get(x_426, 0);
x_464 = lean_ctor_get(x_426, 1);
lean_inc(x_464);
lean_inc(x_463);
lean_dec(x_426);
x_465 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_465, 0, x_463);
lean_ctor_set(x_465, 1, x_464);
return x_465;
}
}
}
}
else
{
uint8_t x_487; 
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_487 = !lean_is_exclusive(x_54);
if (x_487 == 0)
{
return x_54;
}
else
{
lean_object* x_488; lean_object* x_489; lean_object* x_490; 
x_488 = lean_ctor_get(x_54, 0);
x_489 = lean_ctor_get(x_54, 1);
lean_inc(x_489);
lean_inc(x_488);
lean_dec(x_54);
x_490 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_490, 0, x_488);
lean_ctor_set(x_490, 1, x_489);
return x_490;
}
}
}
else
{
uint8_t x_491; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_491 = !lean_is_exclusive(x_44);
if (x_491 == 0)
{
return x_44;
}
else
{
lean_object* x_492; lean_object* x_493; lean_object* x_494; 
x_492 = lean_ctor_get(x_44, 0);
x_493 = lean_ctor_get(x_44, 1);
lean_inc(x_493);
lean_inc(x_492);
lean_dec(x_44);
x_494 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_494, 0, x_492);
lean_ctor_set(x_494, 1, x_493);
return x_494;
}
}
}
else
{
uint8_t x_495; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_495 = !lean_is_exclusive(x_42);
if (x_495 == 0)
{
return x_42;
}
else
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; 
x_496 = lean_ctor_get(x_42, 0);
x_497 = lean_ctor_get(x_42, 1);
lean_inc(x_497);
lean_inc(x_496);
lean_dec(x_42);
x_498 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_498, 0, x_496);
lean_ctor_set(x_498, 1, x_497);
return x_498;
}
}
block_21:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = l_Array_append(lean_box(0), x_14, x_16);
lean_dec(x_16);
x_18 = lean_array_to_list(x_17);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_12);
return x_20;
}
block_41:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = l_Lean_Meta_getMVarsNoDelayed(x_3, x_23, x_26, x_25, x_22, x_31);
lean_dec(x_22);
lean_dec(x_25);
lean_dec(x_26);
lean_dec(x_23);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_array_get_size(x_33);
x_36 = lean_mk_empty_array_with_capacity(x_29);
x_37 = lean_nat_dec_lt(x_29, x_35);
if (x_37 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_27;
x_14 = x_30;
x_15 = x_28;
x_16 = x_36;
goto block_21;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_35, x_35);
if (x_38 == 0)
{
lean_dec(x_35);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_27;
x_14 = x_30;
x_15 = x_28;
x_16 = x_36;
goto block_21;
}
else
{
size_t x_39; lean_object* x_40; 
x_39 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_40 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__1(x_30, x_33, x_24, x_39, x_36);
lean_dec(x_33);
x_12 = x_34;
x_13 = x_27;
x_14 = x_30;
x_15 = x_28;
x_16 = x_40;
goto block_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_mk_string_unchecked("rewrite", 7, 7);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_box(x_4);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Lean_MVarId_rewrite___lam__1___boxed), 11, 6);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_12);
lean_closure_set(x_14, 2, x_3);
lean_closure_set(x_14, 3, x_2);
lean_closure_set(x_14, 4, x_5);
lean_closure_set(x_14, 5, x_13);
x_15 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_14, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_MVarId_rewrite_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__1(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_MVarId_rewrite_spec__2(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_MVarId_rewrite___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_MVarId_rewrite___lam__1(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_rewrite___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l_Lean_MVarId_rewrite(x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_12;
}
}
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_MatchUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_KAbstract(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_BinderNameHint(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Rewrite(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_MatchUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_KAbstract(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_BinderNameHint(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
