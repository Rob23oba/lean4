// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Main
// Imports: Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.TerminationMeasure Lean.Elab.PreDefinition.Mutual Lean.Elab.PreDefinition.WF.PackMutual Lean.Elab.PreDefinition.WF.FloatRecApp Lean.Elab.PreDefinition.WF.Rel Lean.Elab.PreDefinition.WF.Fix Lean.Elab.PreDefinition.WF.Unfold Lean.Elab.PreDefinition.WF.Preprocess Lean.Elab.PreDefinition.WF.GuessLex
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
lean_object* l_Lean_Elab_Mutual_cleanPreDef(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefAttributes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Elab_eraseRecAppSyntaxExpr(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAndCompilePartialRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__5___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_unfoldDeclsFrom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_1698_(lean_object*);
lean_object* l_Lean_Elab_WF_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_floatRecApp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_WF_guessLex_spec__2(size_t, size_t, lean_object*);
uint8_t l_Lean_Elab_DefKind_isTheorem(uint8_t);
lean_object* l_Lean_Elab_WF_mkFix(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_varyingVarNames(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_whnfForall(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_enableRealizationsForConst(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Mutual_addPreDefsFromUnary(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_WF_guessLex_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8(lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_guessLex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getFixedParamPerms(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_elabWFRel___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_addAsAxiom(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___redArg(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_WF_packMutual(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__5(size_t, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8_spec__8(lean_object*, size_t, size_t);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Elab_WF_preDefsFromUnaryNonRec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_Mutual_addPreDefAttributes_spec__2(lean_object*, size_t, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_2, x_1);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_5);
lean_dec(x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_array_uget(x_3, x_2);
x_10 = lean_ctor_get(x_9, 5);
lean_inc(x_10);
lean_inc(x_5);
lean_inc(x_4);
x_11 = l_Lean_Elab_WF_floatRecApp(x_10, x_4, x_5, x_6);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_array_uset(x_3, x_2, x_14);
x_16 = lean_ctor_get(x_9, 0);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*7);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_9, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_9, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 6);
lean_inc(x_22);
lean_dec(x_9);
x_23 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_23, 0, x_16);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_19);
lean_ctor_set(x_23, 3, x_20);
lean_ctor_set(x_23, 4, x_21);
lean_ctor_set(x_23, 5, x_12);
lean_ctor_set(x_23, 6, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*7, x_17);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_add(x_2, x_25);
x_27 = lean_array_uset(x_15, x_2, x_23);
x_2 = x_26;
x_3 = x_27;
x_6 = x_13;
goto _start;
}
else
{
uint8_t x_29; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_29 = !lean_is_exclusive(x_11);
if (x_29 == 0)
{
return x_11;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___redArg(x_1, x_2, x_3, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_12 = lean_array_uget(x_1, x_3);
lean_inc(x_8);
x_13 = l_Lean_Elab_addAsAxiom(x_12, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_15;
x_9 = x_14;
goto _start;
}
else
{
lean_dec(x_8);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___redArg(x_1, x_2, x_3, x_4, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_3, x_11);
if (x_12 == 1)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_fget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
lean_inc(x_1);
x_15 = l_Lean_Elab_WF_varyingVarNames(x_1, x_4, x_14, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_3, x_18);
lean_dec(x_3);
x_20 = lean_nat_add(x_4, x_18);
lean_dec(x_4);
x_21 = lean_array_push(x_5, x_16);
x_3 = x_19;
x_4 = x_20;
x_5 = x_21;
x_10 = x_17;
goto _start;
}
else
{
uint8_t x_23; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_15, 0);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_15);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___redArg(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_3, x_2);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 2);
lean_inc(x_22);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_array_uget(x_1, x_3);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_21, x_27);
lean_inc(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_22);
x_30 = l_Array_isEmpty___redArg(x_25);
lean_dec(x_25);
if (x_30 == 0)
{
lean_dec(x_26);
lean_dec(x_21);
x_12 = x_29;
x_13 = x_11;
goto block_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_29);
x_31 = lean_array_fget(x_26, x_21);
lean_dec(x_21);
lean_dec(x_26);
x_32 = lean_mk_string_unchecked("well-founded recursion cannot be used, '", 40, 40);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_ctor_get(x_31, 3);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_MessageData_ofName(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("' does not take any (non-fixed) arguments", 41, 41);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_3 = x_16;
x_4 = x_12;
x_11 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_3, x_2);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 2);
lean_inc(x_22);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_5);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_4);
lean_ctor_set(x_24, 1, x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_array_uget(x_1, x_3);
x_26 = lean_ctor_get(x_4, 0);
lean_inc(x_26);
lean_dec(x_4);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_21, x_27);
lean_inc(x_26);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_22);
x_30 = l_Array_isEmpty___redArg(x_25);
lean_dec(x_25);
if (x_30 == 0)
{
lean_dec(x_26);
lean_dec(x_21);
x_12 = x_29;
x_13 = x_11;
goto block_18;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
lean_dec(x_29);
x_31 = lean_array_fget(x_26, x_21);
lean_dec(x_21);
lean_dec(x_26);
x_32 = lean_mk_string_unchecked("well-founded recursion cannot be used, '", 40, 40);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_ctor_get(x_31, 3);
lean_inc(x_34);
lean_dec(x_31);
x_35 = l_Lean_MessageData_ofName(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("' does not take any (non-fixed) arguments", 41, 41);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_39, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
return x_40;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_40);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_3, x_15);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3_spec__3(x_1, x_2, x_16, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__5(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_array_uget(x_3, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_box(0);
x_10 = lean_array_uset(x_3, x_2, x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_14 = lean_array_uset(x_10, x_2, x_8);
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___redArg(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_2, x_1);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_array_uget(x_3, x_2);
x_13 = lean_unbox(x_11);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_14 = l_Lean_Elab_Mutual_cleanPreDef(x_12, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_18, x_2, x_15);
x_2 = x_21;
x_3 = x_22;
x_8 = x_16;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = !lean_is_exclusive(x_14);
if (x_24 == 0)
{
return x_14;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_14, 0);
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_14);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___redArg(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___redArg(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_4, x_3);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_5);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
lean_dec(x_5);
x_20 = lean_box(0);
x_21 = lean_array_uget(x_2, x_4);
x_22 = lean_ctor_get(x_21, 3);
lean_inc(x_22);
x_23 = lean_name_eq(x_22, x_1);
lean_dec(x_22);
if (x_23 == 0)
{
uint8_t x_24; uint8_t x_25; 
x_24 = lean_ctor_get_uint8(x_21, sizeof(void*)*7);
x_25 = l_Lean_Elab_DefKind_isTheorem(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_21, 4);
lean_inc(x_26);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = l_Lean_Meta_isProp(x_26, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
lean_dec(x_27);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_31 = l_Lean_Elab_WF_mkBinaryUnfoldEq(x_21, x_1, x_6, x_7, x_8, x_9, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_11 = x_20;
x_12 = x_32;
goto block_17;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_31;
}
}
else
{
lean_object* x_33; 
lean_dec(x_21);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_11 = x_20;
x_12 = x_33;
goto block_17;
}
}
else
{
uint8_t x_34; 
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_27);
if (x_34 == 0)
{
return x_27;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_27, 0);
x_36 = lean_ctor_get(x_27, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_27);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_dec(x_21);
x_11 = x_20;
x_12 = x_10;
goto block_17;
}
}
else
{
lean_dec(x_21);
x_11 = x_20;
x_12 = x_10;
goto block_17;
}
}
block_17:
{
lean_object* x_13; size_t x_14; size_t x_15; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_4, x_14);
x_4 = x_15;
x_5 = x_11;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8_spec__8(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_box(1);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
x_6 = x_4;
goto block_12;
}
else
{
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
x_6 = x_4;
goto block_12;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_usize_of_nat(x_16);
x_20 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_21 = l_Array_anyMUnsafe_any___at___Lean_Elab_Mutual_addPreDefAttributes_spec__2(x_15, x_19, x_20);
lean_dec(x_15);
x_6 = x_21;
goto block_12;
}
}
block_12:
{
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
goto _start;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_5);
return x_11;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8(lean_object* x_1, size_t x_2, size_t x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_eq(x_2, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_5 = lean_box(1);
x_13 = lean_array_uget(x_1, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_15);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
x_6 = x_4;
goto block_12;
}
else
{
if (x_18 == 0)
{
lean_dec(x_17);
lean_dec(x_15);
x_6 = x_4;
goto block_12;
}
else
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_usize_of_nat(x_16);
x_20 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_21 = l_Array_anyMUnsafe_any___at___Lean_Elab_Mutual_addPreDefAttributes_spec__2(x_15, x_19, x_20);
lean_dec(x_15);
x_6 = x_21;
goto block_12;
}
}
block_12:
{
if (x_6 == 0)
{
lean_object* x_7; size_t x_8; size_t x_9; uint8_t x_10; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_2, x_8);
x_10 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8_spec__8(x_1, x_9, x_3);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_unbox(x_5);
return x_11;
}
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_box(0);
x_23 = lean_unbox(x_22);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_1);
x_15 = l_Lean_Elab_getFixedParamPerms(x_1, x_8, x_9, x_10, x_11, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_array_get_size(x_1);
x_19 = lean_mk_empty_array_with_capacity(x_18);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_18);
lean_inc(x_16);
x_20 = l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___redArg(x_16, x_1, x_18, x_5, x_19, x_8, x_9, x_10, x_11, x_17);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = l_Array_toSubarray___redArg(x_1, x_5, x_18);
x_24 = lean_array_size(x_21);
x_25 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3(x_21, x_24, x_3, x_23, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_21);
lean_inc(x_16);
x_27 = l_Lean_Elab_WF_packMutual(x_16, x_21, x_1, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_21);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_16);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_27, 0);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_27);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_21);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_16);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_21);
lean_dec(x_16);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
return x_27;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_27, 0);
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_27);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
else
{
uint8_t x_41; 
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_25);
if (x_41 == 0)
{
return x_25;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_25, 0);
x_43 = lean_ctor_get(x_25, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_25);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_20);
if (x_45 == 0)
{
return x_20;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_20, 0);
x_47 = lean_ctor_get(x_20, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_20);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_15);
if (x_49 == 0)
{
return x_15;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_15, 0);
x_51 = lean_ctor_get(x_15, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_15);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_53 = !lean_is_exclusive(x_13);
if (x_53 == 0)
{
return x_13;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_13, 0);
x_55 = lean_ctor_get(x_13, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_13);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
x_9 = l_Lean_Elab_addAsAxiom(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
x_12 = l_Lean_Elab_WF_preprocess(x_11, x_4, x_5, x_6, x_7, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 4);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 6);
lean_inc(x_22);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_18);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_20);
lean_ctor_set(x_23, 5, x_21);
lean_ctor_set(x_23, 6, x_22);
lean_ctor_set_uint8(x_23, sizeof(void*)*7, x_16);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_12, 0, x_24);
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*7);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 2);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 3);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_25, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 6);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_29);
lean_ctor_set(x_35, 2, x_30);
lean_ctor_set(x_35, 3, x_31);
lean_ctor_set(x_35, 4, x_32);
lean_ctor_set(x_35, 5, x_33);
lean_ctor_set(x_35, 6, x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*7, x_28);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_25);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_26);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_12);
if (x_38 == 0)
{
return x_12;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_12, 0);
x_40 = lean_ctor_get(x_12, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_12);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_9);
if (x_42 == 0)
{
return x_9;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_9, 0);
x_44 = lean_ctor_get(x_9, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_9);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, uint8_t x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18) {
_start:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_inc(x_1);
x_93 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_1, x_16, x_18);
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_unbox(x_94);
lean_dec(x_94);
if (x_95 == 0)
{
lean_object* x_96; 
lean_dec(x_1);
x_96 = lean_ctor_get(x_93, 1);
lean_inc(x_96);
lean_dec(x_93);
x_72 = x_12;
x_73 = x_13;
x_74 = x_14;
x_75 = x_15;
x_76 = x_16;
x_77 = x_17;
x_78 = x_96;
goto block_92;
}
else
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_93);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_98 = lean_ctor_get(x_93, 1);
x_99 = lean_ctor_get(x_93, 0);
lean_dec(x_99);
x_100 = lean_mk_string_unchecked("wfRel: ", 7, 7);
x_101 = l_Lean_stringToMessageData(x_100);
lean_dec(x_100);
lean_inc(x_11);
x_102 = l_Lean_MessageData_ofExpr(x_11);
lean_ctor_set_tag(x_93, 7);
lean_ctor_set(x_93, 1, x_102);
lean_ctor_set(x_93, 0, x_101);
x_103 = lean_mk_string_unchecked("", 0, 0);
x_104 = l_Lean_stringToMessageData(x_103);
lean_dec(x_103);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_93);
lean_ctor_set(x_105, 1, x_104);
x_106 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_1, x_105, x_14, x_15, x_16, x_17, x_98);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_72 = x_12;
x_73 = x_13;
x_74 = x_14;
x_75 = x_15;
x_76 = x_16;
x_77 = x_17;
x_78 = x_107;
goto block_92;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_108 = lean_ctor_get(x_93, 1);
lean_inc(x_108);
lean_dec(x_93);
x_109 = lean_mk_string_unchecked("wfRel: ", 7, 7);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
lean_inc(x_11);
x_111 = l_Lean_MessageData_ofExpr(x_11);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_mk_string_unchecked("", 0, 0);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_1, x_115, x_14, x_15, x_16, x_17, x_108);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
x_72 = x_12;
x_73 = x_13;
x_74 = x_14;
x_75 = x_15;
x_76 = x_16;
x_77 = x_17;
x_78 = x_117;
goto block_92;
}
}
block_29:
{
lean_object* x_24; uint8_t x_25; 
x_24 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0_spec__0___redArg(x_19, x_21, x_20, x_23);
lean_dec(x_20);
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
lean_ctor_set_tag(x_24, 1);
lean_ctor_set(x_24, 0, x_22);
return x_24;
}
else
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_22);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
block_71:
{
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_31, x_36);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_setEnv___at___Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0_spec__0___redArg(x_30, x_32, x_31, x_39);
lean_dec(x_32);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_38, 0);
lean_inc(x_42);
lean_dec(x_38);
x_43 = l_Lean_Meta_unfoldDeclsFrom(x_42, x_35, x_33, x_31, x_41);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_48 = lean_ctor_get(x_2, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 6);
lean_inc(x_52);
lean_dec(x_2);
x_53 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_49);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_51);
lean_ctor_set(x_53, 5, x_45);
lean_ctor_set(x_53, 6, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*7, x_47);
lean_ctor_set(x_43, 0, x_53);
return x_43;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
x_57 = lean_ctor_get_uint8(x_2, sizeof(void*)*7);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_2, 3);
lean_inc(x_60);
x_61 = lean_ctor_get(x_2, 4);
lean_inc(x_61);
x_62 = lean_ctor_get(x_2, 6);
lean_inc(x_62);
lean_dec(x_2);
x_63 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_63, 0, x_56);
lean_ctor_set(x_63, 1, x_58);
lean_ctor_set(x_63, 2, x_59);
lean_ctor_set(x_63, 3, x_60);
lean_ctor_set(x_63, 4, x_61);
lean_ctor_set(x_63, 5, x_54);
lean_ctor_set(x_63, 6, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*7, x_57);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_55);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_2);
x_65 = !lean_is_exclusive(x_43);
if (x_65 == 0)
{
return x_43;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_43, 0);
x_67 = lean_ctor_get(x_43, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_43);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; 
lean_dec(x_33);
lean_dec(x_2);
x_69 = lean_ctor_get(x_34, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_34, 1);
lean_inc(x_70);
lean_dec(x_34);
x_19 = x_30;
x_20 = x_31;
x_21 = x_32;
x_22 = x_69;
x_23 = x_70;
goto block_29;
}
}
block_92:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_79 = lean_st_ref_get(x_77, x_78);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_ctor_get(x_80, 0);
lean_inc(x_82);
lean_dec(x_80);
lean_inc(x_77);
x_83 = l_Lean_Elab_addAsAxiom(x_3, x_74, x_75, x_76, x_77, x_81);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_85 = l_Array_mapMUnsafe_map___at___Lean_Elab_WF_guessLex_spec__3(x_4, x_5, x_6);
lean_inc(x_77);
lean_inc(x_76);
lean_inc(x_75);
lean_inc(x_2);
x_86 = l_Lean_Elab_WF_mkFix(x_2, x_7, x_8, x_11, x_9, x_85, x_10, x_72, x_73, x_74, x_75, x_76, x_77, x_84);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
lean_inc(x_77);
lean_inc(x_76);
x_89 = l_Lean_Elab_eraseRecAppSyntaxExpr(x_87, x_76, x_77, x_88);
x_30 = x_82;
x_31 = x_77;
x_32 = x_75;
x_33 = x_76;
x_34 = x_89;
goto block_71;
}
else
{
x_30 = x_82;
x_31 = x_77;
x_32 = x_75;
x_33 = x_76;
x_34 = x_86;
goto block_71;
}
}
else
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_76);
lean_dec(x_74);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
x_90 = lean_ctor_get(x_83, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_83, 1);
lean_inc(x_91);
lean_dec(x_83);
x_19 = x_82;
x_20 = x_77;
x_21 = x_75;
x_22 = x_90;
x_23 = x_91;
goto block_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19) {
_start:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
x_20 = l_Lean_Meta_whnfForall(x_12, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_isForall(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_24 = lean_mk_string_unchecked("wfRecursion: expected unary function type: ", 43, 43);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = l_Lean_MessageData_ofExpr(x_21);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_mk_string_unchecked("", 0, 0);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_27);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_throwError___at___Lean_Elab_Term_throwErrorIfErrors_spec__0___redArg(x_30, x_13, x_14, x_15, x_16, x_17, x_18, x_22);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
return x_31;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_31);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_36 = l_Lean_Expr_bindingDomain_x21(x_21);
lean_dec(x_21);
lean_inc(x_3);
x_37 = l_Array_mapMUnsafe_map___at___Lean_Elab_WF_guessLex_spec__2(x_1, x_2, x_3);
x_38 = lean_box_usize(x_1);
x_39 = lean_box_usize(x_2);
x_40 = lean_box(x_8);
lean_inc(x_37);
lean_inc(x_7);
lean_inc(x_11);
lean_inc(x_6);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__2___boxed), 18, 10);
lean_closure_set(x_41, 0, x_4);
lean_closure_set(x_41, 1, x_5);
lean_closure_set(x_41, 2, x_6);
lean_closure_set(x_41, 3, x_38);
lean_closure_set(x_41, 4, x_39);
lean_closure_set(x_41, 5, x_3);
lean_closure_set(x_41, 6, x_11);
lean_closure_set(x_41, 7, x_7);
lean_closure_set(x_41, 8, x_37);
lean_closure_set(x_41, 9, x_40);
x_42 = lean_ctor_get(x_6, 3);
lean_inc(x_42);
lean_dec(x_6);
x_43 = l_Lean_Elab_WF_elabWFRel___redArg(x_37, x_42, x_9, x_11, x_7, x_36, x_10, x_41, x_13, x_14, x_15, x_16, x_17, x_18, x_22);
lean_dec(x_13);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_44 = !lean_is_exclusive(x_20);
if (x_44 == 0)
{
return x_20;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_20, 0);
x_46 = lean_ctor_get(x_20, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_20);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; 
x_10 = lean_array_size(x_1);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___redArg(x_10, x_12, x_1, x_7, x_8, x_9);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_8, x_15);
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
x_20 = lean_box(0);
x_37 = lean_array_size(x_14);
x_38 = lean_box_usize(x_37);
x_39 = lean_box_usize(x_12);
lean_inc(x_14);
x_40 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__0___boxed), 12, 5);
lean_closure_set(x_40, 0, x_14);
lean_closure_set(x_40, 1, x_38);
lean_closure_set(x_40, 2, x_39);
lean_closure_set(x_40, 3, x_20);
lean_closure_set(x_40, 4, x_11);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
x_42 = l_Lean_Environment_unlockAsync(x_41);
lean_dec(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_43 = l_Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0(lean_box(0), x_42, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; uint8_t x_117; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_207; uint8_t x_208; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_48 = x_44;
} else {
 lean_dec_ref(x_44);
 x_48 = lean_box(0);
}
x_49 = lean_ctor_get(x_45, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 1);
lean_inc(x_50);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_51 = x_45;
} else {
 lean_dec_ref(x_45);
 x_51 = lean_box(0);
}
x_103 = lean_mk_string_unchecked("Elab", 4, 4);
x_104 = lean_mk_string_unchecked("definition", 10, 10);
x_105 = lean_mk_string_unchecked("wf", 2, 2);
x_106 = l_Lean_Name_mkStr3(x_103, x_104, x_105);
lean_inc(x_106);
x_207 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_106, x_7, x_46);
x_208 = !lean_is_exclusive(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; size_t x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; uint8_t x_302; 
x_209 = lean_ctor_get(x_207, 0);
x_210 = lean_ctor_get(x_207, 1);
lean_inc(x_50);
x_211 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(x_211, 0, x_50);
x_212 = lean_array_size(x_2);
x_213 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__5(x_212, x_12, x_2);
x_302 = lean_unbox(x_209);
lean_dec(x_209);
if (x_302 == 0)
{
lean_free_object(x_207);
x_233 = x_3;
x_234 = x_4;
x_235 = x_5;
x_236 = x_6;
x_237 = x_7;
x_238 = x_8;
x_239 = x_210;
goto block_301;
}
else
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; 
x_303 = lean_mk_string_unchecked("unaryPreDef:", 12, 12);
x_304 = l_Lean_stringToMessageData(x_303);
lean_dec(x_303);
x_305 = lean_ctor_get(x_50, 5);
lean_inc(x_305);
x_306 = l_Lean_MessageData_ofExpr(x_305);
x_307 = l_Lean_indentD(x_306);
lean_ctor_set_tag(x_207, 7);
lean_ctor_set(x_207, 1, x_307);
lean_ctor_set(x_207, 0, x_304);
x_308 = lean_mk_string_unchecked("", 0, 0);
x_309 = l_Lean_stringToMessageData(x_308);
lean_dec(x_308);
x_310 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_310, 0, x_207);
lean_ctor_set(x_310, 1, x_309);
lean_inc(x_106);
x_311 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_310, x_5, x_6, x_7, x_8, x_210);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
x_233 = x_3;
x_234 = x_4;
x_235 = x_5;
x_236 = x_6;
x_237 = x_7;
x_238 = x_8;
x_239 = x_312;
goto block_301;
}
block_232:
{
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_224; 
lean_inc(x_222);
lean_inc(x_221);
lean_inc(x_220);
lean_inc(x_219);
lean_inc(x_49);
lean_inc(x_47);
lean_inc(x_14);
x_224 = l_Lean_Elab_WF_guessLex(x_14, x_215, x_47, x_49, x_219, x_220, x_221, x_222, x_223);
if (lean_obj_tag(x_224) == 0)
{
lean_object* x_225; lean_object* x_226; 
x_225 = lean_ctor_get(x_224, 0);
lean_inc(x_225);
x_226 = lean_ctor_get(x_224, 1);
lean_inc(x_226);
lean_dec(x_224);
x_190 = x_214;
x_191 = x_216;
x_192 = x_225;
x_193 = x_217;
x_194 = x_218;
x_195 = x_219;
x_196 = x_220;
x_197 = x_221;
x_198 = x_222;
x_199 = x_226;
goto block_206;
}
else
{
uint8_t x_227; 
lean_dec(x_222);
lean_dec(x_221);
lean_dec(x_220);
lean_dec(x_219);
lean_dec(x_218);
lean_dec(x_217);
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_106);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_19);
lean_dec(x_14);
x_227 = !lean_is_exclusive(x_224);
if (x_227 == 0)
{
return x_224;
}
else
{
lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_228 = lean_ctor_get(x_224, 0);
x_229 = lean_ctor_get(x_224, 1);
lean_inc(x_229);
lean_inc(x_228);
lean_dec(x_224);
x_230 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_230, 0, x_228);
lean_ctor_set(x_230, 1, x_229);
return x_230;
}
}
}
else
{
lean_object* x_231; 
lean_dec(x_215);
x_231 = lean_ctor_get(x_213, 0);
lean_inc(x_231);
lean_dec(x_213);
x_190 = x_214;
x_191 = x_216;
x_192 = x_231;
x_193 = x_217;
x_194 = x_218;
x_195 = x_219;
x_196 = x_220;
x_197 = x_221;
x_198 = x_222;
x_199 = x_223;
goto block_206;
}
}
block_301:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_240 = lean_st_ref_get(x_238, x_239);
x_241 = lean_ctor_get(x_240, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_240, 1);
lean_inc(x_242);
lean_dec(x_240);
x_243 = lean_ctor_get(x_241, 0);
lean_inc(x_243);
lean_dec(x_241);
x_244 = l_Lean_Environment_unlockAsync(x_243);
lean_dec(x_243);
lean_inc(x_238);
lean_inc(x_237);
lean_inc(x_236);
lean_inc(x_235);
lean_inc(x_234);
lean_inc(x_233);
x_245 = l_Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0(lean_box(0), x_244, x_211, x_233, x_234, x_235, x_236, x_237, x_238, x_242);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_246; lean_object* x_247; uint8_t x_248; 
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_245, 1);
lean_inc(x_247);
lean_dec(x_245);
x_248 = !lean_is_exclusive(x_246);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; uint8_t x_253; 
x_249 = lean_ctor_get(x_246, 0);
x_250 = lean_ctor_get(x_246, 1);
lean_inc(x_106);
x_251 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_106, x_237, x_247);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_unbox(x_252);
lean_dec(x_252);
if (x_253 == 0)
{
lean_object* x_254; 
lean_free_object(x_246);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
lean_dec(x_251);
lean_inc(x_249);
x_214 = x_249;
x_215 = x_249;
x_216 = x_250;
x_217 = x_233;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_237;
x_222 = x_238;
x_223 = x_254;
goto block_232;
}
else
{
uint8_t x_255; 
x_255 = !lean_is_exclusive(x_251);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_256 = lean_ctor_get(x_251, 1);
x_257 = lean_ctor_get(x_251, 0);
lean_dec(x_257);
x_258 = lean_mk_string_unchecked("unaryPreDefProcessed:", 21, 21);
x_259 = l_Lean_stringToMessageData(x_258);
lean_dec(x_258);
x_260 = lean_ctor_get(x_50, 5);
lean_inc(x_260);
x_261 = l_Lean_MessageData_ofExpr(x_260);
x_262 = l_Lean_indentD(x_261);
lean_ctor_set_tag(x_251, 7);
lean_ctor_set(x_251, 1, x_262);
lean_ctor_set(x_251, 0, x_259);
x_263 = lean_mk_string_unchecked("", 0, 0);
x_264 = l_Lean_stringToMessageData(x_263);
lean_dec(x_263);
lean_ctor_set_tag(x_246, 7);
lean_ctor_set(x_246, 1, x_264);
lean_ctor_set(x_246, 0, x_251);
lean_inc(x_106);
x_265 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_246, x_235, x_236, x_237, x_238, x_256);
x_266 = lean_ctor_get(x_265, 1);
lean_inc(x_266);
lean_dec(x_265);
lean_inc(x_249);
x_214 = x_249;
x_215 = x_249;
x_216 = x_250;
x_217 = x_233;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_237;
x_222 = x_238;
x_223 = x_266;
goto block_232;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_267 = lean_ctor_get(x_251, 1);
lean_inc(x_267);
lean_dec(x_251);
x_268 = lean_mk_string_unchecked("unaryPreDefProcessed:", 21, 21);
x_269 = l_Lean_stringToMessageData(x_268);
lean_dec(x_268);
x_270 = lean_ctor_get(x_50, 5);
lean_inc(x_270);
x_271 = l_Lean_MessageData_ofExpr(x_270);
x_272 = l_Lean_indentD(x_271);
x_273 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_273, 0, x_269);
lean_ctor_set(x_273, 1, x_272);
x_274 = lean_mk_string_unchecked("", 0, 0);
x_275 = l_Lean_stringToMessageData(x_274);
lean_dec(x_274);
lean_ctor_set_tag(x_246, 7);
lean_ctor_set(x_246, 1, x_275);
lean_ctor_set(x_246, 0, x_273);
lean_inc(x_106);
x_276 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_246, x_235, x_236, x_237, x_238, x_267);
x_277 = lean_ctor_get(x_276, 1);
lean_inc(x_277);
lean_dec(x_276);
lean_inc(x_249);
x_214 = x_249;
x_215 = x_249;
x_216 = x_250;
x_217 = x_233;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_237;
x_222 = x_238;
x_223 = x_277;
goto block_232;
}
}
}
else
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_278 = lean_ctor_get(x_246, 0);
x_279 = lean_ctor_get(x_246, 1);
lean_inc(x_279);
lean_inc(x_278);
lean_dec(x_246);
lean_inc(x_106);
x_280 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_106, x_237, x_247);
x_281 = lean_ctor_get(x_280, 0);
lean_inc(x_281);
x_282 = lean_unbox(x_281);
lean_dec(x_281);
if (x_282 == 0)
{
lean_object* x_283; 
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
lean_inc(x_278);
x_214 = x_278;
x_215 = x_278;
x_216 = x_279;
x_217 = x_233;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_237;
x_222 = x_238;
x_223 = x_283;
goto block_232;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_284 = lean_ctor_get(x_280, 1);
lean_inc(x_284);
if (lean_is_exclusive(x_280)) {
 lean_ctor_release(x_280, 0);
 lean_ctor_release(x_280, 1);
 x_285 = x_280;
} else {
 lean_dec_ref(x_280);
 x_285 = lean_box(0);
}
x_286 = lean_mk_string_unchecked("unaryPreDefProcessed:", 21, 21);
x_287 = l_Lean_stringToMessageData(x_286);
lean_dec(x_286);
x_288 = lean_ctor_get(x_50, 5);
lean_inc(x_288);
x_289 = l_Lean_MessageData_ofExpr(x_288);
x_290 = l_Lean_indentD(x_289);
if (lean_is_scalar(x_285)) {
 x_291 = lean_alloc_ctor(7, 2, 0);
} else {
 x_291 = x_285;
 lean_ctor_set_tag(x_291, 7);
}
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_mk_string_unchecked("", 0, 0);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_293);
lean_inc(x_106);
x_295 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_294, x_235, x_236, x_237, x_238, x_284);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
lean_inc(x_278);
x_214 = x_278;
x_215 = x_278;
x_216 = x_279;
x_217 = x_233;
x_218 = x_234;
x_219 = x_235;
x_220 = x_236;
x_221 = x_237;
x_222 = x_238;
x_223 = x_296;
goto block_232;
}
}
}
else
{
uint8_t x_297; 
lean_dec(x_238);
lean_dec(x_237);
lean_dec(x_236);
lean_dec(x_235);
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_213);
lean_dec(x_106);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_19);
lean_dec(x_14);
x_297 = !lean_is_exclusive(x_245);
if (x_297 == 0)
{
return x_245;
}
else
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; 
x_298 = lean_ctor_get(x_245, 0);
x_299 = lean_ctor_get(x_245, 1);
lean_inc(x_299);
lean_inc(x_298);
lean_dec(x_245);
x_300 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_300, 0, x_298);
lean_ctor_set(x_300, 1, x_299);
return x_300;
}
}
}
}
else
{
lean_object* x_313; lean_object* x_314; lean_object* x_315; size_t x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; uint8_t x_377; 
x_313 = lean_ctor_get(x_207, 0);
x_314 = lean_ctor_get(x_207, 1);
lean_inc(x_314);
lean_inc(x_313);
lean_dec(x_207);
lean_inc(x_50);
x_315 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__1___boxed), 8, 1);
lean_closure_set(x_315, 0, x_50);
x_316 = lean_array_size(x_2);
x_317 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__5(x_316, x_12, x_2);
x_377 = lean_unbox(x_313);
lean_dec(x_313);
if (x_377 == 0)
{
x_337 = x_3;
x_338 = x_4;
x_339 = x_5;
x_340 = x_6;
x_341 = x_7;
x_342 = x_8;
x_343 = x_314;
goto block_376;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
x_378 = lean_mk_string_unchecked("unaryPreDef:", 12, 12);
x_379 = l_Lean_stringToMessageData(x_378);
lean_dec(x_378);
x_380 = lean_ctor_get(x_50, 5);
lean_inc(x_380);
x_381 = l_Lean_MessageData_ofExpr(x_380);
x_382 = l_Lean_indentD(x_381);
x_383 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_383, 0, x_379);
lean_ctor_set(x_383, 1, x_382);
x_384 = lean_mk_string_unchecked("", 0, 0);
x_385 = l_Lean_stringToMessageData(x_384);
lean_dec(x_384);
x_386 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_386, 0, x_383);
lean_ctor_set(x_386, 1, x_385);
lean_inc(x_106);
x_387 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_386, x_5, x_6, x_7, x_8, x_314);
x_388 = lean_ctor_get(x_387, 1);
lean_inc(x_388);
lean_dec(x_387);
x_337 = x_3;
x_338 = x_4;
x_339 = x_5;
x_340 = x_6;
x_341 = x_7;
x_342 = x_8;
x_343 = x_388;
goto block_376;
}
block_336:
{
if (lean_obj_tag(x_317) == 0)
{
lean_object* x_328; 
lean_inc(x_326);
lean_inc(x_325);
lean_inc(x_324);
lean_inc(x_323);
lean_inc(x_49);
lean_inc(x_47);
lean_inc(x_14);
x_328 = l_Lean_Elab_WF_guessLex(x_14, x_319, x_47, x_49, x_323, x_324, x_325, x_326, x_327);
if (lean_obj_tag(x_328) == 0)
{
lean_object* x_329; lean_object* x_330; 
x_329 = lean_ctor_get(x_328, 0);
lean_inc(x_329);
x_330 = lean_ctor_get(x_328, 1);
lean_inc(x_330);
lean_dec(x_328);
x_190 = x_318;
x_191 = x_320;
x_192 = x_329;
x_193 = x_321;
x_194 = x_322;
x_195 = x_323;
x_196 = x_324;
x_197 = x_325;
x_198 = x_326;
x_199 = x_330;
goto block_206;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_326);
lean_dec(x_325);
lean_dec(x_324);
lean_dec(x_323);
lean_dec(x_322);
lean_dec(x_321);
lean_dec(x_320);
lean_dec(x_318);
lean_dec(x_106);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_19);
lean_dec(x_14);
x_331 = lean_ctor_get(x_328, 0);
lean_inc(x_331);
x_332 = lean_ctor_get(x_328, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_328)) {
 lean_ctor_release(x_328, 0);
 lean_ctor_release(x_328, 1);
 x_333 = x_328;
} else {
 lean_dec_ref(x_328);
 x_333 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_334 = lean_alloc_ctor(1, 2, 0);
} else {
 x_334 = x_333;
}
lean_ctor_set(x_334, 0, x_331);
lean_ctor_set(x_334, 1, x_332);
return x_334;
}
}
else
{
lean_object* x_335; 
lean_dec(x_319);
x_335 = lean_ctor_get(x_317, 0);
lean_inc(x_335);
lean_dec(x_317);
x_190 = x_318;
x_191 = x_320;
x_192 = x_335;
x_193 = x_321;
x_194 = x_322;
x_195 = x_323;
x_196 = x_324;
x_197 = x_325;
x_198 = x_326;
x_199 = x_327;
goto block_206;
}
}
block_376:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_344 = lean_st_ref_get(x_342, x_343);
x_345 = lean_ctor_get(x_344, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_344, 1);
lean_inc(x_346);
lean_dec(x_344);
x_347 = lean_ctor_get(x_345, 0);
lean_inc(x_347);
lean_dec(x_345);
x_348 = l_Lean_Environment_unlockAsync(x_347);
lean_dec(x_347);
lean_inc(x_342);
lean_inc(x_341);
lean_inc(x_340);
lean_inc(x_339);
lean_inc(x_338);
lean_inc(x_337);
x_349 = l_Lean_withEnv___at___Lean_Elab_Term_evalTerm_spec__0(lean_box(0), x_348, x_315, x_337, x_338, x_339, x_340, x_341, x_342, x_346);
if (lean_obj_tag(x_349) == 0)
{
lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_350 = lean_ctor_get(x_349, 0);
lean_inc(x_350);
x_351 = lean_ctor_get(x_349, 1);
lean_inc(x_351);
lean_dec(x_349);
x_352 = lean_ctor_get(x_350, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_350, 1);
lean_inc(x_353);
if (lean_is_exclusive(x_350)) {
 lean_ctor_release(x_350, 0);
 lean_ctor_release(x_350, 1);
 x_354 = x_350;
} else {
 lean_dec_ref(x_350);
 x_354 = lean_box(0);
}
lean_inc(x_106);
x_355 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_106, x_341, x_351);
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_unbox(x_356);
lean_dec(x_356);
if (x_357 == 0)
{
lean_object* x_358; 
lean_dec(x_354);
x_358 = lean_ctor_get(x_355, 1);
lean_inc(x_358);
lean_dec(x_355);
lean_inc(x_352);
x_318 = x_352;
x_319 = x_352;
x_320 = x_353;
x_321 = x_337;
x_322 = x_338;
x_323 = x_339;
x_324 = x_340;
x_325 = x_341;
x_326 = x_342;
x_327 = x_358;
goto block_336;
}
else
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_359 = lean_ctor_get(x_355, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_360 = x_355;
} else {
 lean_dec_ref(x_355);
 x_360 = lean_box(0);
}
x_361 = lean_mk_string_unchecked("unaryPreDefProcessed:", 21, 21);
x_362 = l_Lean_stringToMessageData(x_361);
lean_dec(x_361);
x_363 = lean_ctor_get(x_50, 5);
lean_inc(x_363);
x_364 = l_Lean_MessageData_ofExpr(x_363);
x_365 = l_Lean_indentD(x_364);
if (lean_is_scalar(x_360)) {
 x_366 = lean_alloc_ctor(7, 2, 0);
} else {
 x_366 = x_360;
 lean_ctor_set_tag(x_366, 7);
}
lean_ctor_set(x_366, 0, x_362);
lean_ctor_set(x_366, 1, x_365);
x_367 = lean_mk_string_unchecked("", 0, 0);
x_368 = l_Lean_stringToMessageData(x_367);
lean_dec(x_367);
if (lean_is_scalar(x_354)) {
 x_369 = lean_alloc_ctor(7, 2, 0);
} else {
 x_369 = x_354;
 lean_ctor_set_tag(x_369, 7);
}
lean_ctor_set(x_369, 0, x_366);
lean_ctor_set(x_369, 1, x_368);
lean_inc(x_106);
x_370 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_369, x_339, x_340, x_341, x_342, x_359);
x_371 = lean_ctor_get(x_370, 1);
lean_inc(x_371);
lean_dec(x_370);
lean_inc(x_352);
x_318 = x_352;
x_319 = x_352;
x_320 = x_353;
x_321 = x_337;
x_322 = x_338;
x_323 = x_339;
x_324 = x_340;
x_325 = x_341;
x_326 = x_342;
x_327 = x_371;
goto block_336;
}
}
else
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_340);
lean_dec(x_339);
lean_dec(x_338);
lean_dec(x_337);
lean_dec(x_317);
lean_dec(x_106);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_19);
lean_dec(x_14);
x_372 = lean_ctor_get(x_349, 0);
lean_inc(x_372);
x_373 = lean_ctor_get(x_349, 1);
lean_inc(x_373);
if (lean_is_exclusive(x_349)) {
 lean_ctor_release(x_349, 0);
 lean_ctor_release(x_349, 1);
 x_374 = x_349;
} else {
 lean_dec_ref(x_349);
 x_374 = lean_box(0);
}
if (lean_is_scalar(x_374)) {
 x_375 = lean_alloc_ctor(1, 2, 0);
} else {
 x_375 = x_374;
}
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
}
block_102:
{
lean_object* x_62; 
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_54);
lean_inc(x_14);
lean_inc(x_49);
lean_inc(x_47);
x_62 = l_Lean_Elab_WF_preDefsFromUnaryNonRec(x_47, x_49, x_14, x_54, x_57, x_58, x_59, x_60, x_61);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_14);
x_65 = l_Lean_Elab_Mutual_addPreDefsFromUnary(x_14, x_63, x_54, x_52, x_55, x_56, x_57, x_58, x_59, x_60, x_64);
lean_dec(x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_14);
x_67 = l_Lean_Elab_addAndCompilePartialRec(x_14, x_55, x_56, x_57, x_58, x_59, x_60, x_66);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
x_69 = l_Lean_Elab_Mutual_cleanPreDef(x_50, x_52, x_57, x_58, x_59, x_60, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
x_72 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___redArg(x_37, x_12, x_14, x_57, x_58, x_59, x_60, x_71);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_54, 3);
lean_inc(x_75);
lean_dec(x_54);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_75);
lean_inc(x_73);
x_76 = l_Lean_Elab_WF_registerEqnsInfo(x_73, x_75, x_47, x_49, x_57, x_58, x_59, x_60, x_74);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
lean_dec(x_76);
x_78 = lean_ctor_get(x_70, 4);
lean_inc(x_78);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
x_79 = l_Lean_Meta_isProp(x_78, x_57, x_58, x_59, x_60, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
lean_inc(x_60);
lean_inc(x_59);
lean_inc(x_58);
lean_inc(x_57);
lean_inc(x_75);
x_83 = l_Lean_Elab_WF_mkUnfoldEq(x_70, x_75, x_53, x_57, x_58, x_59, x_60, x_82);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; 
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_21 = x_75;
x_22 = x_73;
x_23 = x_55;
x_24 = x_56;
x_25 = x_57;
x_26 = x_58;
x_27 = x_59;
x_28 = x_60;
x_29 = x_84;
goto block_36;
}
else
{
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
return x_83;
}
}
else
{
lean_object* x_85; 
lean_dec(x_70);
lean_dec(x_53);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
lean_dec(x_79);
x_21 = x_75;
x_22 = x_73;
x_23 = x_55;
x_24 = x_56;
x_25 = x_57;
x_26 = x_58;
x_27 = x_59;
x_28 = x_60;
x_29 = x_85;
goto block_36;
}
}
else
{
uint8_t x_86; 
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
x_86 = !lean_is_exclusive(x_79);
if (x_86 == 0)
{
return x_79;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_79, 0);
x_88 = lean_ctor_get(x_79, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_79);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_53);
return x_76;
}
}
else
{
uint8_t x_90; 
lean_dec(x_70);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_47);
x_90 = !lean_is_exclusive(x_72);
if (x_90 == 0)
{
return x_72;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_72, 0);
x_92 = lean_ctor_get(x_72, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_72);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_14);
x_94 = !lean_is_exclusive(x_69);
if (x_94 == 0)
{
return x_69;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_69, 0);
x_96 = lean_ctor_get(x_69, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_69);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_14);
return x_67;
}
}
else
{
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_14);
return x_65;
}
}
else
{
uint8_t x_98; 
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_55);
lean_dec(x_54);
lean_dec(x_53);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_47);
lean_dec(x_14);
x_98 = !lean_is_exclusive(x_62);
if (x_98 == 0)
{
return x_62;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_62, 0);
x_100 = lean_ctor_get(x_62, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_62);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
block_176:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; 
x_118 = lean_box_usize(x_37);
x_119 = lean_box_usize(x_12);
x_120 = lean_box(x_117);
lean_inc(x_47);
lean_inc(x_49);
lean_inc(x_50);
lean_inc(x_106);
lean_inc(x_14);
x_121 = lean_alloc_closure((void*)(l_Lean_Elab_wfRecursion___lam__3___boxed), 19, 10);
lean_closure_set(x_121, 0, x_118);
lean_closure_set(x_121, 1, x_119);
lean_closure_set(x_121, 2, x_14);
lean_closure_set(x_121, 3, x_106);
lean_closure_set(x_121, 4, x_107);
lean_closure_set(x_121, 5, x_50);
lean_closure_set(x_121, 6, x_49);
lean_closure_set(x_121, 7, x_120);
lean_closure_set(x_121, 8, x_47);
lean_closure_set(x_121, 9, x_108);
x_122 = lean_ctor_get(x_50, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_47, 0);
lean_inc(x_123);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = lean_box(0);
x_126 = lean_unbox(x_125);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_115);
lean_inc(x_109);
lean_inc(x_116);
lean_inc(x_111);
x_127 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Elab_Term_addAutoBoundImplicits_x27_spec__1___redArg(x_122, x_124, x_121, x_126, x_111, x_116, x_109, x_115, x_113, x_114, x_110);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_106);
x_130 = l_Lean_isTracingEnabledFor___at___Lean_Elab_Term_traceAtCmdPos_spec__0___redArg(x_106, x_113, x_129);
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_unbox(x_131);
lean_dec(x_131);
if (x_132 == 0)
{
lean_object* x_133; uint8_t x_134; 
lean_dec(x_106);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_19);
x_133 = lean_ctor_get(x_130, 1);
lean_inc(x_133);
lean_dec(x_130);
x_134 = lean_unbox(x_125);
x_52 = x_134;
x_53 = x_112;
x_54 = x_128;
x_55 = x_111;
x_56 = x_116;
x_57 = x_109;
x_58 = x_115;
x_59 = x_113;
x_60 = x_114;
x_61 = x_133;
goto block_102;
}
else
{
uint8_t x_135; 
x_135 = !lean_is_exclusive(x_130);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; 
x_136 = lean_ctor_get(x_130, 1);
x_137 = lean_ctor_get(x_130, 0);
lean_dec(x_137);
x_138 = lean_mk_string_unchecked(">> ", 3, 3);
x_139 = l_Lean_stringToMessageData(x_138);
lean_dec(x_138);
x_140 = lean_ctor_get(x_128, 3);
lean_inc(x_140);
x_141 = l_Lean_MessageData_ofName(x_140);
lean_ctor_set_tag(x_130, 7);
lean_ctor_set(x_130, 1, x_141);
lean_ctor_set(x_130, 0, x_139);
x_142 = lean_mk_string_unchecked(" :=\n", 4, 4);
x_143 = l_Lean_stringToMessageData(x_142);
lean_dec(x_142);
if (lean_is_scalar(x_51)) {
 x_144 = lean_alloc_ctor(7, 2, 0);
} else {
 x_144 = x_51;
 lean_ctor_set_tag(x_144, 7);
}
lean_ctor_set(x_144, 0, x_130);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_ctor_get(x_128, 5);
lean_inc(x_145);
x_146 = l_Lean_MessageData_ofExpr(x_145);
if (lean_is_scalar(x_48)) {
 x_147 = lean_alloc_ctor(7, 2, 0);
} else {
 x_147 = x_48;
 lean_ctor_set_tag(x_147, 7);
}
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_mk_string_unchecked("", 0, 0);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
if (lean_is_scalar(x_19)) {
 x_150 = lean_alloc_ctor(7, 2, 0);
} else {
 x_150 = x_19;
 lean_ctor_set_tag(x_150, 7);
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_150, x_109, x_115, x_113, x_114, x_136);
x_152 = lean_ctor_get(x_151, 1);
lean_inc(x_152);
lean_dec(x_151);
x_153 = lean_unbox(x_125);
x_52 = x_153;
x_53 = x_112;
x_54 = x_128;
x_55 = x_111;
x_56 = x_116;
x_57 = x_109;
x_58 = x_115;
x_59 = x_113;
x_60 = x_114;
x_61 = x_152;
goto block_102;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_154 = lean_ctor_get(x_130, 1);
lean_inc(x_154);
lean_dec(x_130);
x_155 = lean_mk_string_unchecked(">> ", 3, 3);
x_156 = l_Lean_stringToMessageData(x_155);
lean_dec(x_155);
x_157 = lean_ctor_get(x_128, 3);
lean_inc(x_157);
x_158 = l_Lean_MessageData_ofName(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_mk_string_unchecked(" :=\n", 4, 4);
x_161 = l_Lean_stringToMessageData(x_160);
lean_dec(x_160);
if (lean_is_scalar(x_51)) {
 x_162 = lean_alloc_ctor(7, 2, 0);
} else {
 x_162 = x_51;
 lean_ctor_set_tag(x_162, 7);
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_ctor_get(x_128, 5);
lean_inc(x_163);
x_164 = l_Lean_MessageData_ofExpr(x_163);
if (lean_is_scalar(x_48)) {
 x_165 = lean_alloc_ctor(7, 2, 0);
} else {
 x_165 = x_48;
 lean_ctor_set_tag(x_165, 7);
}
lean_ctor_set(x_165, 0, x_162);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_mk_string_unchecked("", 0, 0);
x_167 = l_Lean_stringToMessageData(x_166);
lean_dec(x_166);
if (lean_is_scalar(x_19)) {
 x_168 = lean_alloc_ctor(7, 2, 0);
} else {
 x_168 = x_19;
 lean_ctor_set_tag(x_168, 7);
}
lean_ctor_set(x_168, 0, x_165);
lean_ctor_set(x_168, 1, x_167);
x_169 = l_Lean_addTrace___at___Lean_Elab_Term_traceAtCmdPos_spec__1___redArg(x_106, x_168, x_109, x_115, x_113, x_114, x_154);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = lean_unbox(x_125);
x_52 = x_171;
x_53 = x_112;
x_54 = x_128;
x_55 = x_111;
x_56 = x_116;
x_57 = x_109;
x_58 = x_115;
x_59 = x_113;
x_60 = x_114;
x_61 = x_170;
goto block_102;
}
}
}
else
{
uint8_t x_172; 
lean_dec(x_116);
lean_dec(x_115);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_109);
lean_dec(x_106);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_19);
lean_dec(x_14);
x_172 = !lean_is_exclusive(x_127);
if (x_172 == 0)
{
return x_127;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = lean_ctor_get(x_127, 0);
x_174 = lean_ctor_get(x_127, 1);
lean_inc(x_174);
lean_inc(x_173);
lean_dec(x_127);
x_175 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
return x_175;
}
}
}
block_189:
{
lean_object* x_187; uint8_t x_188; 
x_187 = lean_box(1);
x_188 = lean_unbox(x_187);
x_107 = x_178;
x_108 = x_183;
x_109 = x_177;
x_110 = x_179;
x_111 = x_180;
x_112 = x_182;
x_113 = x_181;
x_114 = x_185;
x_115 = x_184;
x_116 = x_186;
x_117 = x_188;
goto block_176;
}
block_206:
{
lean_object* x_200; uint8_t x_201; 
x_200 = lean_array_get_size(x_14);
x_201 = lean_nat_dec_lt(x_11, x_200);
if (x_201 == 0)
{
lean_dec(x_200);
x_177 = x_195;
x_178 = x_190;
x_179 = x_199;
x_180 = x_193;
x_181 = x_197;
x_182 = x_191;
x_183 = x_192;
x_184 = x_196;
x_185 = x_198;
x_186 = x_194;
goto block_189;
}
else
{
if (x_201 == 0)
{
lean_dec(x_200);
x_177 = x_195;
x_178 = x_190;
x_179 = x_199;
x_180 = x_193;
x_181 = x_197;
x_182 = x_191;
x_183 = x_192;
x_184 = x_196;
x_185 = x_198;
x_186 = x_194;
goto block_189;
}
else
{
size_t x_202; uint8_t x_203; 
x_202 = lean_usize_of_nat(x_200);
lean_dec(x_200);
x_203 = l_Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8(x_14, x_12, x_202);
if (x_203 == 0)
{
x_177 = x_195;
x_178 = x_190;
x_179 = x_199;
x_180 = x_193;
x_181 = x_197;
x_182 = x_191;
x_183 = x_192;
x_184 = x_196;
x_185 = x_198;
x_186 = x_194;
goto block_189;
}
else
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_box(0);
x_205 = lean_unbox(x_204);
x_107 = x_190;
x_108 = x_192;
x_109 = x_195;
x_110 = x_199;
x_111 = x_193;
x_112 = x_191;
x_113 = x_197;
x_114 = x_198;
x_115 = x_196;
x_116 = x_194;
x_117 = x_205;
goto block_176;
}
}
}
}
}
else
{
uint8_t x_389; 
lean_dec(x_19);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_389 = !lean_is_exclusive(x_43);
if (x_389 == 0)
{
return x_43;
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; 
x_390 = lean_ctor_get(x_43, 0);
x_391 = lean_ctor_get(x_43, 1);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_43);
x_392 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_392, 0, x_390);
lean_ctor_set(x_392, 1, x_391);
return x_392;
}
}
block_36:
{
size_t x_30; lean_object* x_31; 
x_30 = lean_array_size(x_22);
lean_inc(x_28);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_21);
x_31 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___redArg(x_21, x_22, x_30, x_12, x_20, x_25, x_26, x_27, x_28, x_29);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_27);
x_33 = l_Lean_enableRealizationsForConst(x_21, x_27, x_28, x_32);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_Elab_Mutual_addPreDefAttributes(x_22, x_23, x_24, x_25, x_26, x_27, x_28, x_34);
return x_35;
}
else
{
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
return x_31;
}
}
}
else
{
uint8_t x_393; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_393 = !lean_is_exclusive(x_13);
if (x_393 == 0)
{
return x_13;
}
else
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; 
x_394 = lean_ctor_get(x_13, 0);
x_395 = lean_ctor_get(x_13, 1);
lean_inc(x_395);
lean_inc(x_394);
lean_dec(x_13);
x_396 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_396, 0, x_394);
lean_ctor_set(x_396, 1, x_395);
return x_396;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___redArg(x_7, x_8, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__0(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Array_mapFinIdxM_map___at___Lean_Elab_wfRecursion_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3_spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__5(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___redArg(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Elab_wfRecursion_spec__6(x_11, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___redArg(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Elab_wfRecursion_spec__7(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8_spec__8(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Array_anyMUnsafe_any___at___Lean_Elab_wfRecursion_spec__8(x_1, x_4, x_5);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Lean_Elab_wfRecursion___lam__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_wfRecursion___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__2___boxed(lean_object** _args) {
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
_start:
{
size_t x_19; size_t x_20; uint8_t x_21; lean_object* x_22; 
x_19 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_20 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_21 = lean_unbox(x_10);
lean_dec(x_10);
x_22 = l_Lean_Elab_wfRecursion___lam__2(x_1, x_2, x_3, x_19, x_20, x_6, x_7, x_8, x_9, x_21, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18);
lean_dec(x_3);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_wfRecursion___lam__3___boxed(lean_object** _args) {
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
_start:
{
size_t x_20; size_t x_21; uint8_t x_22; lean_object* x_23; 
x_20 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_21 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_22 = lean_unbox(x_8);
lean_dec(x_8);
x_23 = l_Lean_Elab_wfRecursion___lam__3(x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_22, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
return x_23;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_1698_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("definition", 10, 10);
x_4 = lean_mk_string_unchecked("wf", 2, 2);
lean_inc(x_2);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
lean_inc(x_2);
x_10 = l_Lean_Name_str___override(x_9, x_2);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_8);
x_16 = l_Lean_Name_str___override(x_15, x_2);
x_17 = lean_mk_string_unchecked("PreDefinition", 13, 13);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = lean_mk_string_unchecked("WF", 2, 2);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("Main", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_mk_string_unchecked("_hyg", 4, 4);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_unsigned_to_nat(1698u);
x_26 = l_Lean_Name_num___override(x_24, x_25);
x_27 = lean_unbox(x_6);
x_28 = l_Lean_registerTraceClass(x_5, x_27, x_26, x_1);
return x_28;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_TerminationMeasure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Mutual(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_PackMutual(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Rel(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Fix(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_Preprocess(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_WF_GuessLex(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_TerminationMeasure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Mutual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_PackMutual(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_FloatRecApp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Rel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Fix(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Unfold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_Preprocess(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_WF_GuessLex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_initFn____x40_Lean_Elab_PreDefinition_WF_Main___hyg_1698_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
