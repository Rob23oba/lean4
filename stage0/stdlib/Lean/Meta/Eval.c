// Lean compiler output
// Module: Lean.Meta.Eval
// Imports: Lean.AddDecl Lean.Meta.Check Lean.Util.CollectLevelParams
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
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isImportedConst(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_setEnv___at___Lean_Meta_setInlineAttribute_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_CollectLevelParams_main(lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__2(lean_object*, lean_object*, size_t, size_t);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Environment_unlockAsync(lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_async;
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Environment_importEnv_x3f_unsafe__1(lean_object*);
lean_object* l_Lean_Meta_whnfD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* l_Lean_Meta_mkHasTypeButIsExpectedMsg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_Expr_getUsedConstants(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addAndCompile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_stringToMessageData(x_7);
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_4, 2);
x_12 = lean_eval_const(x_10, x_11, x_1);
lean_dec(x_10);
x_13 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___redArg(x_12, x_2, x_3, x_4, x_5, x_9);
lean_dec(x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__2(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_box(1);
x_7 = lean_array_uget(x_2, x_3);
x_8 = l_Lean_Environment_isImportedConst(x_1, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
uint8_t x_9; 
x_9 = lean_unbox(x_6);
return x_9;
}
else
{
if (x_5 == 0)
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
goto _start;
}
else
{
uint8_t x_14; 
x_14 = lean_unbox(x_6);
return x_14;
}
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_setEnv___at___Lean_Meta_setInlineAttribute_spec__0(x_1, x_3, x_4, x_5, x_6, x_10);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_14 = lean_apply_5(x_2, x_3, x_4, x_5, x_6, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_setEnv___at___Lean_Meta_setInlineAttribute_spec__0(x_11, x_3, x_4, x_5, x_6, x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_15);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_15);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_setEnv___at___Lean_Meta_setInlineAttribute_spec__0(x_11, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
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
}
}
LEAN_EXPORT lean_object* l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; 
x_299 = lean_st_ref_get(x_7, x_8);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_299, 1);
lean_inc(x_301);
lean_dec(x_299);
lean_inc(x_3);
x_309 = l_Lean_Expr_getUsedConstants(x_3);
x_310 = lean_unsigned_to_nat(0u);
x_311 = lean_array_get_size(x_309);
x_312 = lean_nat_dec_lt(x_310, x_311);
if (x_312 == 0)
{
lean_dec(x_311);
lean_dec(x_309);
lean_dec(x_300);
goto block_308;
}
else
{
if (x_312 == 0)
{
lean_dec(x_311);
lean_dec(x_309);
lean_dec(x_300);
goto block_308;
}
else
{
lean_object* x_313; size_t x_314; size_t x_315; uint8_t x_316; 
x_313 = lean_ctor_get(x_300, 0);
lean_inc(x_313);
lean_dec(x_300);
x_314 = lean_usize_of_nat(x_310);
x_315 = lean_usize_of_nat(x_311);
lean_dec(x_311);
x_316 = l_Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__2(x_313, x_309, x_314, x_315);
lean_dec(x_309);
lean_dec(x_313);
if (x_316 == 0)
{
goto block_308;
}
else
{
x_154 = x_4;
x_155 = x_5;
x_156 = x_6;
x_157 = x_7;
x_158 = x_301;
goto block_267;
}
}
}
block_40:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_15, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_15, 3);
lean_inc(x_20);
x_21 = l_Lean_maxRecDepth;
x_22 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_13, x_21);
x_23 = lean_ctor_get(x_15, 5);
lean_inc(x_23);
x_24 = lean_ctor_get(x_15, 6);
lean_inc(x_24);
x_25 = lean_ctor_get(x_15, 7);
lean_inc(x_25);
x_26 = lean_ctor_get(x_15, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_15, 9);
lean_inc(x_27);
x_28 = lean_ctor_get(x_15, 10);
lean_inc(x_28);
x_29 = lean_ctor_get(x_15, 11);
lean_inc(x_29);
x_30 = lean_ctor_get_uint8(x_15, sizeof(void*)*13 + 1);
x_31 = lean_ctor_get(x_15, 12);
lean_inc(x_31);
lean_dec(x_15);
x_32 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_19);
lean_ctor_set(x_32, 2, x_13);
lean_ctor_set(x_32, 3, x_20);
lean_ctor_set(x_32, 4, x_22);
lean_ctor_set(x_32, 5, x_23);
lean_ctor_set(x_32, 6, x_24);
lean_ctor_set(x_32, 7, x_25);
lean_ctor_set(x_32, 8, x_26);
lean_ctor_set(x_32, 9, x_27);
lean_ctor_set(x_32, 10, x_28);
lean_ctor_set(x_32, 11, x_29);
lean_ctor_set(x_32, 12, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*13, x_12);
lean_ctor_set_uint8(x_32, sizeof(void*)*13 + 1, x_30);
lean_inc(x_16);
lean_inc(x_32);
x_33 = l_Lean_addAndCompile(x_11, x_32, x_16, x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg(x_10, x_14, x_9, x_32, x_16, x_34);
lean_dec(x_16);
lean_dec(x_32);
lean_dec(x_9);
lean_dec(x_14);
lean_dec(x_10);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
return x_33;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_33, 0);
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_33);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
block_83:
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_st_ref_take(x_46, x_47);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = l_Lean_Kernel_enableDiag(x_54, x_45);
x_56 = lean_ctor_get(x_52, 1);
lean_inc(x_56);
x_57 = lean_ctor_get(x_52, 2);
lean_inc(x_57);
x_58 = lean_ctor_get(x_52, 3);
lean_inc(x_58);
x_59 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_59);
lean_inc(x_60);
lean_ctor_set(x_50, 1, x_60);
lean_ctor_set(x_50, 0, x_60);
x_61 = lean_ctor_get(x_52, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_52, 6);
lean_inc(x_62);
x_63 = lean_ctor_get(x_52, 7);
lean_inc(x_63);
lean_dec(x_52);
x_64 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_64, 0, x_55);
lean_ctor_set(x_64, 1, x_56);
lean_ctor_set(x_64, 2, x_57);
lean_ctor_set(x_64, 3, x_58);
lean_ctor_set(x_64, 4, x_50);
lean_ctor_set(x_64, 5, x_61);
lean_ctor_set(x_64, 6, x_62);
lean_ctor_set(x_64, 7, x_63);
x_65 = lean_st_ref_set(x_46, x_64, x_53);
x_66 = lean_ctor_get(x_65, 1);
lean_inc(x_66);
lean_dec(x_65);
x_9 = x_42;
x_10 = x_41;
x_11 = x_44;
x_12 = x_45;
x_13 = x_48;
x_14 = x_49;
x_15 = x_43;
x_16 = x_46;
x_17 = x_66;
goto block_40;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_67 = lean_ctor_get(x_50, 0);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_50);
x_69 = lean_ctor_get(x_67, 0);
lean_inc(x_69);
x_70 = l_Lean_Kernel_enableDiag(x_69, x_45);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 3);
lean_inc(x_73);
x_74 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_inc(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_ctor_get(x_67, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_67, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_67, 7);
lean_inc(x_79);
lean_dec(x_67);
x_80 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_72);
lean_ctor_set(x_80, 3, x_73);
lean_ctor_set(x_80, 4, x_76);
lean_ctor_set(x_80, 5, x_77);
lean_ctor_set(x_80, 6, x_78);
lean_ctor_set(x_80, 7, x_79);
x_81 = lean_st_ref_set(x_46, x_80, x_68);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_9 = x_42;
x_10 = x_41;
x_11 = x_44;
x_12 = x_45;
x_13 = x_48;
x_14 = x_49;
x_15 = x_43;
x_16 = x_46;
x_17 = x_82;
goto block_40;
}
}
block_153:
{
lean_object* x_93; 
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_85);
x_93 = lean_infer_type(x_85, x_88, x_89, x_90, x_91, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
lean_inc(x_88);
lean_inc(x_94);
x_96 = lean_apply_6(x_1, x_94, x_88, x_89, x_90, x_91, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_98 = lean_st_ref_get(x_91, x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ctor_get(x_99, 0);
lean_inc(x_101);
lean_dec(x_99);
x_102 = lean_mk_string_unchecked("compiler env", 12, 12);
x_103 = lean_ctor_get(x_101, 2);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_91);
lean_inc(x_90);
x_104 = l_Lean_traceBlock___redArg(x_102, x_103, x_90, x_91, x_100);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
lean_dec(x_104);
x_106 = lean_st_ref_get(x_91, x_105);
x_107 = !lean_is_exclusive(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; uint8_t x_121; lean_object* x_122; uint8_t x_123; 
x_108 = lean_ctor_get(x_106, 0);
x_109 = lean_ctor_get(x_106, 1);
x_110 = lean_array_to_list(x_87);
lean_inc(x_84);
x_111 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_111, 0, x_84);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_94);
x_112 = lean_box(0);
lean_inc(x_84);
lean_ctor_set_tag(x_106, 1);
lean_ctor_set(x_106, 1, x_86);
lean_ctor_set(x_106, 0, x_84);
x_113 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_85);
lean_ctor_set(x_113, 2, x_112);
lean_ctor_set(x_113, 3, x_106);
lean_ctor_set_uint8(x_113, sizeof(void*)*4, x_2);
x_114 = lean_ctor_get(x_90, 2);
lean_inc(x_114);
x_115 = l_Lean_Elab_async;
x_116 = lean_box(0);
x_117 = l_Lean_diagnostics;
x_118 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_118, 0, x_113);
x_119 = lean_unbox(x_116);
x_120 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_114, x_115, x_119);
x_121 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_120, x_117);
x_122 = lean_ctor_get(x_108, 0);
lean_inc(x_122);
lean_dec(x_108);
x_123 = l_Lean_Kernel_isDiagnosticsEnabled(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
if (x_121 == 0)
{
x_9 = x_89;
x_10 = x_84;
x_11 = x_118;
x_12 = x_121;
x_13 = x_120;
x_14 = x_88;
x_15 = x_90;
x_16 = x_91;
x_17 = x_109;
goto block_40;
}
else
{
x_41 = x_84;
x_42 = x_89;
x_43 = x_90;
x_44 = x_118;
x_45 = x_121;
x_46 = x_91;
x_47 = x_109;
x_48 = x_120;
x_49 = x_88;
goto block_83;
}
}
else
{
if (x_121 == 0)
{
x_41 = x_84;
x_42 = x_89;
x_43 = x_90;
x_44 = x_118;
x_45 = x_121;
x_46 = x_91;
x_47 = x_109;
x_48 = x_120;
x_49 = x_88;
goto block_83;
}
else
{
x_9 = x_89;
x_10 = x_84;
x_11 = x_118;
x_12 = x_121;
x_13 = x_120;
x_14 = x_88;
x_15 = x_90;
x_16 = x_91;
x_17 = x_109;
goto block_40;
}
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; uint8_t x_140; 
x_124 = lean_ctor_get(x_106, 0);
x_125 = lean_ctor_get(x_106, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_106);
x_126 = lean_array_to_list(x_87);
lean_inc(x_84);
x_127 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_127, 0, x_84);
lean_ctor_set(x_127, 1, x_126);
lean_ctor_set(x_127, 2, x_94);
x_128 = lean_box(0);
lean_inc(x_84);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_84);
lean_ctor_set(x_129, 1, x_86);
x_130 = lean_alloc_ctor(0, 4, 1);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_85);
lean_ctor_set(x_130, 2, x_128);
lean_ctor_set(x_130, 3, x_129);
lean_ctor_set_uint8(x_130, sizeof(void*)*4, x_2);
x_131 = lean_ctor_get(x_90, 2);
lean_inc(x_131);
x_132 = l_Lean_Elab_async;
x_133 = lean_box(0);
x_134 = l_Lean_diagnostics;
x_135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_135, 0, x_130);
x_136 = lean_unbox(x_133);
x_137 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_131, x_132, x_136);
x_138 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_137, x_134);
x_139 = lean_ctor_get(x_124, 0);
lean_inc(x_139);
lean_dec(x_124);
x_140 = l_Lean_Kernel_isDiagnosticsEnabled(x_139);
lean_dec(x_139);
if (x_140 == 0)
{
if (x_138 == 0)
{
x_9 = x_89;
x_10 = x_84;
x_11 = x_135;
x_12 = x_138;
x_13 = x_137;
x_14 = x_88;
x_15 = x_90;
x_16 = x_91;
x_17 = x_125;
goto block_40;
}
else
{
x_41 = x_84;
x_42 = x_89;
x_43 = x_90;
x_44 = x_135;
x_45 = x_138;
x_46 = x_91;
x_47 = x_125;
x_48 = x_137;
x_49 = x_88;
goto block_83;
}
}
else
{
if (x_138 == 0)
{
x_41 = x_84;
x_42 = x_89;
x_43 = x_90;
x_44 = x_135;
x_45 = x_138;
x_46 = x_91;
x_47 = x_125;
x_48 = x_137;
x_49 = x_88;
goto block_83;
}
else
{
x_9 = x_89;
x_10 = x_84;
x_11 = x_135;
x_12 = x_138;
x_13 = x_137;
x_14 = x_88;
x_15 = x_90;
x_16 = x_91;
x_17 = x_125;
goto block_40;
}
}
}
}
else
{
uint8_t x_141; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
x_141 = !lean_is_exclusive(x_104);
if (x_141 == 0)
{
return x_104;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_104, 0);
x_143 = lean_ctor_get(x_104, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_104);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
else
{
uint8_t x_145; 
lean_dec(x_94);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
x_145 = !lean_is_exclusive(x_96);
if (x_145 == 0)
{
return x_96;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_146 = lean_ctor_get(x_96, 0);
x_147 = lean_ctor_get(x_96, 1);
lean_inc(x_147);
lean_inc(x_146);
lean_dec(x_96);
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
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_93);
if (x_149 == 0)
{
return x_93;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_93, 0);
x_151 = lean_ctor_get(x_93, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_93);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
block_267:
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; 
x_159 = lean_mk_string_unchecked("_tmp", 4, 4);
x_160 = l_Lean_Name_mkStr1(x_159);
x_161 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_160, x_156, x_157, x_158);
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ctor_get(x_161, 1);
x_165 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_3, x_155, x_164);
x_166 = !lean_is_exclusive(x_165);
if (x_166 == 0)
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_167 = lean_ctor_get(x_165, 0);
x_168 = lean_ctor_get(x_165, 1);
x_169 = lean_unsigned_to_nat(8u);
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_unsigned_to_nat(2u);
x_172 = lean_nat_shiftl(x_169, x_171);
x_173 = lean_unsigned_to_nat(3u);
x_174 = lean_nat_div(x_172, x_173);
lean_dec(x_172);
x_175 = l_Nat_nextPowerOfTwo(x_174);
lean_dec(x_174);
x_176 = lean_box(0);
lean_inc(x_175);
x_177 = lean_mk_array(x_175, x_176);
lean_ctor_set(x_165, 1, x_177);
lean_ctor_set(x_165, 0, x_170);
x_178 = lean_box(0);
x_179 = lean_mk_array(x_175, x_178);
lean_ctor_set(x_161, 1, x_179);
lean_ctor_set(x_161, 0, x_170);
x_180 = lean_box(0);
x_181 = lean_mk_empty_array_with_capacity(x_170);
x_182 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_182, 0, x_165);
lean_ctor_set(x_182, 1, x_161);
lean_ctor_set(x_182, 2, x_181);
lean_inc(x_167);
x_183 = l_Lean_CollectLevelParams_main(x_167, x_182);
x_184 = lean_ctor_get(x_183, 2);
lean_inc(x_184);
lean_dec(x_183);
x_185 = l_Lean_Expr_hasMVar(x_167);
if (x_185 == 0)
{
x_84 = x_163;
x_85 = x_167;
x_86 = x_180;
x_87 = x_184;
x_88 = x_154;
x_89 = x_155;
x_90 = x_156;
x_91 = x_157;
x_92 = x_168;
goto block_153;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; uint8_t x_194; 
lean_dec(x_184);
lean_dec(x_163);
lean_dec(x_1);
x_186 = lean_mk_string_unchecked("failed to evaluate expression, it contains metavariables", 56, 56);
x_187 = l_Lean_stringToMessageData(x_186);
lean_dec(x_186);
x_188 = l_Lean_indentExpr(x_167);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_mk_string_unchecked("", 0, 0);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_189);
lean_ctor_set(x_192, 1, x_191);
x_193 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_192, x_154, x_155, x_156, x_157, x_168);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
x_194 = !lean_is_exclusive(x_193);
if (x_194 == 0)
{
return x_193;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_193, 0);
x_196 = lean_ctor_get(x_193, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_193);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
else
{
lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
x_198 = lean_ctor_get(x_165, 0);
x_199 = lean_ctor_get(x_165, 1);
lean_inc(x_199);
lean_inc(x_198);
lean_dec(x_165);
x_200 = lean_unsigned_to_nat(8u);
x_201 = lean_unsigned_to_nat(0u);
x_202 = lean_unsigned_to_nat(2u);
x_203 = lean_nat_shiftl(x_200, x_202);
x_204 = lean_unsigned_to_nat(3u);
x_205 = lean_nat_div(x_203, x_204);
lean_dec(x_203);
x_206 = l_Nat_nextPowerOfTwo(x_205);
lean_dec(x_205);
x_207 = lean_box(0);
lean_inc(x_206);
x_208 = lean_mk_array(x_206, x_207);
x_209 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_209, 0, x_201);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_box(0);
x_211 = lean_mk_array(x_206, x_210);
lean_ctor_set(x_161, 1, x_211);
lean_ctor_set(x_161, 0, x_201);
x_212 = lean_box(0);
x_213 = lean_mk_empty_array_with_capacity(x_201);
x_214 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_214, 0, x_209);
lean_ctor_set(x_214, 1, x_161);
lean_ctor_set(x_214, 2, x_213);
lean_inc(x_198);
x_215 = l_Lean_CollectLevelParams_main(x_198, x_214);
x_216 = lean_ctor_get(x_215, 2);
lean_inc(x_216);
lean_dec(x_215);
x_217 = l_Lean_Expr_hasMVar(x_198);
if (x_217 == 0)
{
x_84 = x_163;
x_85 = x_198;
x_86 = x_212;
x_87 = x_216;
x_88 = x_154;
x_89 = x_155;
x_90 = x_156;
x_91 = x_157;
x_92 = x_199;
goto block_153;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_216);
lean_dec(x_163);
lean_dec(x_1);
x_218 = lean_mk_string_unchecked("failed to evaluate expression, it contains metavariables", 56, 56);
x_219 = l_Lean_stringToMessageData(x_218);
lean_dec(x_218);
x_220 = l_Lean_indentExpr(x_198);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_219);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_mk_string_unchecked("", 0, 0);
x_223 = l_Lean_stringToMessageData(x_222);
lean_dec(x_222);
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_223);
x_225 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_224, x_154, x_155, x_156, x_157, x_199);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 lean_ctor_release(x_225, 1);
 x_228 = x_225;
} else {
 lean_dec_ref(x_225);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; 
x_230 = lean_ctor_get(x_161, 0);
x_231 = lean_ctor_get(x_161, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_161);
x_232 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_3, x_155, x_231);
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = lean_unsigned_to_nat(8u);
x_237 = lean_unsigned_to_nat(0u);
x_238 = lean_unsigned_to_nat(2u);
x_239 = lean_nat_shiftl(x_236, x_238);
x_240 = lean_unsigned_to_nat(3u);
x_241 = lean_nat_div(x_239, x_240);
lean_dec(x_239);
x_242 = l_Nat_nextPowerOfTwo(x_241);
lean_dec(x_241);
x_243 = lean_box(0);
lean_inc(x_242);
x_244 = lean_mk_array(x_242, x_243);
if (lean_is_scalar(x_235)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_235;
}
lean_ctor_set(x_245, 0, x_237);
lean_ctor_set(x_245, 1, x_244);
x_246 = lean_box(0);
x_247 = lean_mk_array(x_242, x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_237);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_box(0);
x_250 = lean_mk_empty_array_with_capacity(x_237);
x_251 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_251, 0, x_245);
lean_ctor_set(x_251, 1, x_248);
lean_ctor_set(x_251, 2, x_250);
lean_inc(x_233);
x_252 = l_Lean_CollectLevelParams_main(x_233, x_251);
x_253 = lean_ctor_get(x_252, 2);
lean_inc(x_253);
lean_dec(x_252);
x_254 = l_Lean_Expr_hasMVar(x_233);
if (x_254 == 0)
{
x_84 = x_230;
x_85 = x_233;
x_86 = x_249;
x_87 = x_253;
x_88 = x_154;
x_89 = x_155;
x_90 = x_156;
x_91 = x_157;
x_92 = x_234;
goto block_153;
}
else
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_dec(x_253);
lean_dec(x_230);
lean_dec(x_1);
x_255 = lean_mk_string_unchecked("failed to evaluate expression, it contains metavariables", 56, 56);
x_256 = l_Lean_stringToMessageData(x_255);
lean_dec(x_255);
x_257 = l_Lean_indentExpr(x_233);
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_mk_string_unchecked("", 0, 0);
x_260 = l_Lean_stringToMessageData(x_259);
lean_dec(x_259);
x_261 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_261, 0, x_258);
lean_ctor_set(x_261, 1, x_260);
x_262 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_261, x_154, x_155, x_156, x_157, x_234);
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_262)) {
 lean_ctor_release(x_262, 0);
 lean_ctor_release(x_262, 1);
 x_265 = x_262;
} else {
 lean_dec_ref(x_262);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(1, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
block_298:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_271 = lean_ctor_get(x_268, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_268, 2);
lean_inc(x_272);
x_273 = lean_ctor_get(x_268, 3);
lean_inc(x_273);
x_274 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_274);
x_275 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_275, 0, x_274);
lean_inc(x_275);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_ctor_get(x_268, 5);
lean_inc(x_277);
x_278 = lean_ctor_get(x_268, 6);
lean_inc(x_278);
x_279 = lean_ctor_get(x_268, 7);
lean_inc(x_279);
lean_dec(x_268);
x_280 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_280, 0, x_270);
lean_ctor_set(x_280, 1, x_271);
lean_ctor_set(x_280, 2, x_272);
lean_ctor_set(x_280, 3, x_273);
lean_ctor_set(x_280, 4, x_276);
lean_ctor_set(x_280, 5, x_277);
lean_ctor_set(x_280, 6, x_278);
lean_ctor_set(x_280, 7, x_279);
x_281 = lean_st_ref_set(x_7, x_280, x_269);
x_282 = lean_ctor_get(x_281, 1);
lean_inc(x_282);
lean_dec(x_281);
x_283 = lean_st_ref_take(x_5, x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_283, 1);
lean_inc(x_285);
lean_dec(x_283);
x_286 = lean_ctor_get(x_284, 0);
lean_inc(x_286);
lean_inc(x_274);
x_287 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_287, 0, x_274);
lean_inc(x_274);
x_288 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_288, 0, x_274);
lean_inc(x_274);
x_289 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_289, 0, x_274);
x_290 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_290, 0, x_274);
lean_inc(x_290);
lean_inc(x_287);
x_291 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_291, 0, x_287);
lean_ctor_set(x_291, 1, x_288);
lean_ctor_set(x_291, 2, x_289);
lean_ctor_set(x_291, 3, x_287);
lean_ctor_set(x_291, 4, x_290);
lean_ctor_set(x_291, 5, x_290);
x_292 = lean_ctor_get(x_284, 2);
lean_inc(x_292);
x_293 = lean_ctor_get(x_284, 3);
lean_inc(x_293);
x_294 = lean_ctor_get(x_284, 4);
lean_inc(x_294);
lean_dec(x_284);
x_295 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_295, 0, x_286);
lean_ctor_set(x_295, 1, x_291);
lean_ctor_set(x_295, 2, x_292);
lean_ctor_set(x_295, 3, x_293);
lean_ctor_set(x_295, 4, x_294);
x_296 = lean_st_ref_set(x_5, x_295, x_285);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_154 = x_4;
x_155 = x_5;
x_156 = x_6;
x_157 = x_7;
x_158 = x_297;
goto block_267;
}
block_308:
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_302 = lean_st_ref_take(x_7, x_301);
x_303 = lean_ctor_get(x_302, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_302, 1);
lean_inc(x_304);
lean_dec(x_302);
x_305 = lean_ctor_get(x_303, 0);
lean_inc(x_305);
lean_inc(x_305);
x_306 = l_Lean_Environment_importEnv_x3f_unsafe__1(x_305);
if (lean_obj_tag(x_306) == 0)
{
x_268 = x_303;
x_269 = x_304;
x_270 = x_305;
goto block_298;
}
else
{
lean_object* x_307; 
lean_dec(x_305);
x_307 = lean_ctor_get(x_306, 0);
lean_inc(x_307);
lean_dec(x_306);
x_268 = x_303;
x_269 = x_304;
x_270 = x_307;
goto block_298;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_box(x_3);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_evalExprCore___redArg___lam__0___boxed), 8, 3);
lean_closure_set(x_13, 0, x_2);
lean_closure_set(x_13, 1, x_12);
lean_closure_set(x_13, 2, x_1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Environment_unlockAsync(x_14);
lean_dec(x_14);
x_16 = l_Lean_withEnv___at___Lean_Meta_evalExprCore_spec__3___redArg(x_15, x_13, x_4, x_5, x_6, x_7, x_11);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_evalExprCore___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_ofExcept___at___Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_evalConst___at___Lean_Meta_evalExprCore_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_evalExprCore_spec__2(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l_Lean_Meta_evalExprCore___redArg___lam__0(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_evalExprCore___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExprCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_evalExprCore(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_8 = l_Lean_Meta_whnfD(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = l_Lean_Expr_isConstOf(x_10, x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_8);
x_13 = lean_mk_string_unchecked("unexpected type at evalExpr", 27, 27);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
x_15 = l_Lean_indentExpr(x_10);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("", 0, 0);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_19, x_3, x_4, x_5, x_6, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_21 = lean_box(0);
lean_ctor_set(x_8, 0, x_21);
return x_8;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_8, 0);
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_8);
x_24 = l_Lean_Expr_isConstOf(x_22, x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_25 = lean_mk_string_unchecked("unexpected type at evalExpr", 27, 27);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_indentExpr(x_22);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_31, x_3, x_4, x_5, x_6, x_23);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_23);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_8);
if (x_35 == 0)
{
return x_8;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_8, 0);
x_37 = lean_ctor_get(x_8, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_8);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed), 7, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_evalExprCore___redArg(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_evalExpr_x27___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_evalExpr_x27___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_evalExpr_x27___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr_x27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_evalExpr_x27(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
lean_inc(x_2);
x_8 = l_Lean_Meta_isExprDefEq(x_2, x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_12 = l_Lean_Meta_mkHasTypeButIsExpectedMsg(x_2, x_1, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("unexpected type at `evalExpr` ", 30, 30);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_20, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_22 = !lean_is_exclusive(x_12);
if (x_22 == 0)
{
return x_12;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_12, 0);
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_12);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_8, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_8, 0, x_28);
return x_8;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
uint8_t x_32; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_8);
if (x_32 == 0)
{
return x_8;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_8, 0);
x_34 = lean_ctor_get(x_8, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_8);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_evalExpr___redArg___lam__0), 7, 1);
lean_closure_set(x_9, 0, x_1);
x_10 = l_Lean_Meta_evalExprCore___redArg(x_2, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_evalExpr___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Lean_Meta_evalExpr___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_evalExpr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_evalExpr(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Lean_AddDecl(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Check(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectLevelParams(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Eval(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_AddDecl(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Check(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectLevelParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
