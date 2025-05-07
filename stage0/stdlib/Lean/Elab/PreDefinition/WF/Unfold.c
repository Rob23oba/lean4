// Lean compiler output
// Module: Lean.Elab.PreDefinition.WF.Unfold
// Imports: Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Eqns Lean.Meta.Tactic.Apply
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentD(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_MVarId_getType_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_maxRecDepth;
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2463_(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__1(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_delta_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mapErrorImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__1(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_Simp_mkCongr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_TransparencyMode_lt(uint8_t, uint8_t);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_MVarId_applyConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(uint8_t, lean_object*);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Meta_subst_substEq_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwTacticEx___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* l_Lean_Meta_applySimpResultToTarget(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; 
x_11 = l_Lean_Expr_appFn_x21(x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_2, x_4, x_12);
x_14 = l_Lean_Expr_app___override(x_11, x_13);
x_15 = lean_box(0);
x_16 = lean_box(1);
x_17 = lean_unbox(x_15);
x_18 = lean_unbox(x_15);
x_19 = lean_unbox(x_16);
x_20 = l_Lean_Meta_mkLambdaFVars(x_4, x_14, x_17, x_3, x_18, x_19, x_6, x_7, x_8, x_9, x_10);
return x_20;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_21; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Lean_MVarId_getType_x27(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_mk_string_unchecked("Eq", 2, 2);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_unsigned_to_nat(3u);
x_27 = l_Lean_Expr_isAppOfArity(x_22, x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_28 = lean_mk_string_unchecked("Lean.Elab.PreDefinition.WF.Unfold", 33, 33);
x_29 = lean_mk_string_unchecked("_private.Lean.Elab.PreDefinition.WF.Unfold.0.Lean.Elab.WF.rwFixEq", 65, 65);
x_30 = lean_unsigned_to_nat(17u);
x_31 = lean_unsigned_to_nat(41u);
x_32 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_33 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_28, x_29, x_30, x_31, x_32);
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_28);
x_34 = l_panic___at___Lean_Meta_subst_substEq_spec__0(x_33, x_3, x_4, x_5, x_6, x_23);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_box(x_27);
x_36 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed), 2, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = l_Lean_Expr_appFn_x21(x_22);
x_38 = l_Lean_Expr_appArg_x21(x_37);
lean_dec(x_37);
lean_inc(x_38);
x_39 = l_Lean_Meta_delta_x3f(x_38, x_36, x_5, x_6, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_mk_string_unchecked("rwFixEq: cannot delta-reduce ", 29, 29);
x_43 = l_Lean_stringToMessageData(x_42);
lean_dec(x_42);
x_44 = l_Lean_MessageData_ofExpr(x_38);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_mk_string_unchecked("", 0, 0);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_48, x_3, x_4, x_5, x_6, x_41);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_49;
}
else
{
lean_object* x_50; uint8_t x_51; 
x_50 = lean_ctor_get(x_39, 1);
lean_inc(x_50);
lean_dec(x_39);
x_51 = !lean_is_exclusive(x_40);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_40, 0);
lean_inc(x_52);
x_53 = l_Lean_Expr_cleanupAnnotations(x_52);
x_54 = l_Lean_Expr_isApp(x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
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
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
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
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = l_Lean_Expr_appFnCleanup___redArg(x_57);
x_60 = l_Lean_Expr_isApp(x_59);
if (x_60 == 0)
{
lean_dec(x_59);
lean_dec(x_55);
lean_dec(x_53);
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_61; uint8_t x_62; 
x_61 = l_Lean_Expr_appFnCleanup___redArg(x_59);
x_62 = l_Lean_Expr_isApp(x_61);
if (x_62 == 0)
{
lean_dec(x_61);
lean_dec(x_55);
lean_dec(x_53);
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = l_Lean_Expr_appFnCleanup___redArg(x_61);
x_64 = l_Lean_Expr_isApp(x_63);
if (x_64 == 0)
{
lean_dec(x_63);
lean_dec(x_55);
lean_dec(x_53);
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_65 = l_Lean_Expr_appFnCleanup___redArg(x_63);
x_66 = lean_mk_string_unchecked("WellFounded", 11, 11);
x_67 = lean_mk_string_unchecked("fix", 3, 3);
lean_inc(x_66);
x_68 = l_Lean_Name_mkStr2(x_66, x_67);
x_69 = l_Lean_Expr_isConstOf(x_65, x_68);
lean_dec(x_68);
lean_dec(x_65);
if (x_69 == 0)
{
lean_dec(x_66);
lean_dec(x_55);
lean_dec(x_53);
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_70 = lean_ctor_get(x_53, 1);
lean_inc(x_70);
lean_dec(x_53);
x_71 = lean_ctor_get(x_55, 1);
lean_inc(x_71);
lean_dec(x_55);
x_72 = lean_mk_string_unchecked("fix_eq", 6, 6);
x_73 = l_Lean_Expr_getAppFn(x_52);
x_74 = lean_box(0);
x_75 = l_Lean_Expr_sort___override(x_74);
x_76 = l_Lean_Expr_getAppNumArgs(x_52);
x_77 = lean_unsigned_to_nat(1u);
lean_inc(x_70);
lean_inc(x_71);
x_78 = l_Lean_Expr_app___override(x_71, x_70);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_79 = lean_infer_type(x_78, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_box(x_69);
x_83 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 10, 3);
lean_closure_set(x_83, 0, x_38);
lean_closure_set(x_83, 1, x_2);
lean_closure_set(x_83, 2, x_82);
x_84 = l_Lean_Expr_bindingDomain_x21(x_80);
lean_dec(x_80);
x_85 = lean_unsigned_to_nat(2u);
lean_ctor_set(x_40, 0, x_85);
x_86 = lean_box(0);
x_87 = lean_unbox(x_86);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_88 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_84, x_40, x_83, x_87, x_3, x_4, x_5, x_6, x_81);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_92 = l_Lean_mkAppB(x_71, x_70, x_89);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_93 = l_Lean_Meta_mkEq(x_92, x_91, x_3, x_4, x_5, x_6, x_90);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_box(0);
lean_inc(x_3);
x_97 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_94, x_96, x_3, x_4, x_5, x_6, x_95);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
x_100 = l_Lean_Name_mkStr2(x_66, x_72);
x_101 = l_Lean_Expr_constLevels_x21(x_73);
lean_dec(x_73);
lean_inc(x_76);
x_102 = lean_mk_array(x_76, x_75);
x_103 = lean_nat_sub(x_76, x_77);
lean_dec(x_76);
x_104 = l_Lean_Expr_const___override(x_100, x_101);
x_105 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_52, x_102, x_103);
x_106 = l_Lean_mkAppN(x_104, x_105);
lean_dec(x_105);
lean_inc(x_4);
lean_inc(x_98);
x_107 = l_Lean_Meta_mkEqTrans(x_106, x_98, x_3, x_4, x_5, x_6, x_99);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
lean_dec(x_107);
x_110 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_108, x_4, x_109);
lean_dec(x_4);
x_111 = !lean_is_exclusive(x_110);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_110, 0);
lean_dec(x_112);
x_113 = l_Lean_Expr_mvarId_x21(x_98);
lean_dec(x_98);
lean_ctor_set(x_110, 0, x_113);
return x_110;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_110, 1);
lean_inc(x_114);
lean_dec(x_110);
x_115 = l_Lean_Expr_mvarId_x21(x_98);
lean_dec(x_98);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
}
else
{
uint8_t x_117; 
lean_dec(x_98);
lean_dec(x_4);
lean_dec(x_1);
x_117 = !lean_is_exclusive(x_107);
if (x_117 == 0)
{
return x_107;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_107, 0);
x_119 = lean_ctor_get(x_107, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_107);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
uint8_t x_121; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_66);
lean_dec(x_52);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_121 = !lean_is_exclusive(x_93);
if (x_121 == 0)
{
return x_93;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_93, 0);
x_123 = lean_ctor_get(x_93, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_93);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_66);
lean_dec(x_52);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_125 = !lean_is_exclusive(x_88);
if (x_125 == 0)
{
return x_88;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_88, 0);
x_127 = lean_ctor_get(x_88, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_88);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
uint8_t x_129; 
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_66);
lean_free_object(x_40);
lean_dec(x_52);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_129 = !lean_is_exclusive(x_79);
if (x_129 == 0)
{
return x_79;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; 
x_130 = lean_ctor_get(x_79, 0);
x_131 = lean_ctor_get(x_79, 1);
lean_inc(x_131);
lean_inc(x_130);
lean_dec(x_79);
x_132 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
return x_132;
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
lean_object* x_133; lean_object* x_134; uint8_t x_135; 
x_133 = lean_ctor_get(x_40, 0);
lean_inc(x_133);
lean_dec(x_40);
lean_inc(x_133);
x_134 = l_Lean_Expr_cleanupAnnotations(x_133);
x_135 = l_Lean_Expr_isApp(x_134);
if (x_135 == 0)
{
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_136; uint8_t x_137; 
lean_inc(x_134);
x_136 = l_Lean_Expr_appFnCleanup___redArg(x_134);
x_137 = l_Lean_Expr_isApp(x_136);
if (x_137 == 0)
{
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_138; uint8_t x_139; 
lean_inc(x_136);
x_138 = l_Lean_Expr_appFnCleanup___redArg(x_136);
x_139 = l_Lean_Expr_isApp(x_138);
if (x_139 == 0)
{
lean_dec(x_138);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_140; uint8_t x_141; 
x_140 = l_Lean_Expr_appFnCleanup___redArg(x_138);
x_141 = l_Lean_Expr_isApp(x_140);
if (x_141 == 0)
{
lean_dec(x_140);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_142; uint8_t x_143; 
x_142 = l_Lean_Expr_appFnCleanup___redArg(x_140);
x_143 = l_Lean_Expr_isApp(x_142);
if (x_143 == 0)
{
lean_dec(x_142);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_144; uint8_t x_145; 
x_144 = l_Lean_Expr_appFnCleanup___redArg(x_142);
x_145 = l_Lean_Expr_isApp(x_144);
if (x_145 == 0)
{
lean_dec(x_144);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; 
x_146 = l_Lean_Expr_appFnCleanup___redArg(x_144);
x_147 = lean_mk_string_unchecked("WellFounded", 11, 11);
x_148 = lean_mk_string_unchecked("fix", 3, 3);
lean_inc(x_147);
x_149 = l_Lean_Name_mkStr2(x_147, x_148);
x_150 = l_Lean_Expr_isConstOf(x_146, x_149);
lean_dec(x_149);
lean_dec(x_146);
if (x_150 == 0)
{
lean_dec(x_147);
lean_dec(x_136);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_2);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_50;
goto block_20;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_151 = lean_ctor_get(x_134, 1);
lean_inc(x_151);
lean_dec(x_134);
x_152 = lean_ctor_get(x_136, 1);
lean_inc(x_152);
lean_dec(x_136);
x_153 = lean_mk_string_unchecked("fix_eq", 6, 6);
x_154 = l_Lean_Expr_getAppFn(x_133);
x_155 = lean_box(0);
x_156 = l_Lean_Expr_sort___override(x_155);
x_157 = l_Lean_Expr_getAppNumArgs(x_133);
x_158 = lean_unsigned_to_nat(1u);
lean_inc(x_151);
lean_inc(x_152);
x_159 = l_Lean_Expr_app___override(x_152, x_151);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_160 = lean_infer_type(x_159, x_3, x_4, x_5, x_6, x_50);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_box(x_150);
x_164 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed), 10, 3);
lean_closure_set(x_164, 0, x_38);
lean_closure_set(x_164, 1, x_2);
lean_closure_set(x_164, 2, x_163);
x_165 = l_Lean_Expr_bindingDomain_x21(x_161);
lean_dec(x_161);
x_166 = lean_unsigned_to_nat(2u);
x_167 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_167, 0, x_166);
x_168 = lean_box(0);
x_169 = lean_unbox(x_168);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_170 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_setMVarUserNamesAt_spec__0___redArg(x_165, x_167, x_164, x_169, x_3, x_4, x_5, x_6, x_162);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_170, 1);
lean_inc(x_172);
lean_dec(x_170);
x_173 = l_Lean_Expr_appArg_x21(x_22);
lean_dec(x_22);
x_174 = l_Lean_mkAppB(x_152, x_151, x_171);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_175 = l_Lean_Meta_mkEq(x_174, x_173, x_3, x_4, x_5, x_6, x_172);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = lean_box(0);
lean_inc(x_3);
x_179 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_176, x_178, x_3, x_4, x_5, x_6, x_177);
x_180 = lean_ctor_get(x_179, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = l_Lean_Name_mkStr2(x_147, x_153);
x_183 = l_Lean_Expr_constLevels_x21(x_154);
lean_dec(x_154);
lean_inc(x_157);
x_184 = lean_mk_array(x_157, x_156);
x_185 = lean_nat_sub(x_157, x_158);
lean_dec(x_157);
x_186 = l_Lean_Expr_const___override(x_182, x_183);
x_187 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_133, x_184, x_185);
x_188 = l_Lean_mkAppN(x_186, x_187);
lean_dec(x_187);
lean_inc(x_4);
lean_inc(x_180);
x_189 = l_Lean_Meta_mkEqTrans(x_188, x_180, x_3, x_4, x_5, x_6, x_181);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
x_190 = lean_ctor_get(x_189, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_189, 1);
lean_inc(x_191);
lean_dec(x_189);
x_192 = l_Lean_MVarId_assign___at___Lean_Meta_getLevel_spec__0___redArg(x_1, x_190, x_4, x_191);
lean_dec(x_4);
x_193 = lean_ctor_get(x_192, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_194 = x_192;
} else {
 lean_dec_ref(x_192);
 x_194 = lean_box(0);
}
x_195 = l_Lean_Expr_mvarId_x21(x_180);
lean_dec(x_180);
if (lean_is_scalar(x_194)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_194;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_193);
return x_196;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_dec(x_180);
lean_dec(x_4);
lean_dec(x_1);
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_189)) {
 lean_ctor_release(x_189, 0);
 lean_ctor_release(x_189, 1);
 x_199 = x_189;
} else {
 lean_dec_ref(x_189);
 x_199 = lean_box(0);
}
if (lean_is_scalar(x_199)) {
 x_200 = lean_alloc_ctor(1, 2, 0);
} else {
 x_200 = x_199;
}
lean_ctor_set(x_200, 0, x_197);
lean_ctor_set(x_200, 1, x_198);
return x_200;
}
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_147);
lean_dec(x_133);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_201 = lean_ctor_get(x_175, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_175, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_203 = x_175;
} else {
 lean_dec_ref(x_175);
 x_203 = lean_box(0);
}
if (lean_is_scalar(x_203)) {
 x_204 = lean_alloc_ctor(1, 2, 0);
} else {
 x_204 = x_203;
}
lean_ctor_set(x_204, 0, x_201);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_133);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_205 = lean_ctor_get(x_170, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_170, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_207 = x_170;
} else {
 lean_dec_ref(x_170);
 x_207 = lean_box(0);
}
if (lean_is_scalar(x_207)) {
 x_208 = lean_alloc_ctor(1, 2, 0);
} else {
 x_208 = x_207;
}
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_157);
lean_dec(x_156);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_152);
lean_dec(x_151);
lean_dec(x_147);
lean_dec(x_133);
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_209 = lean_ctor_get(x_160, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_160, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_211 = x_160;
} else {
 lean_dec_ref(x_160);
 x_211 = lean_box(0);
}
if (lean_is_scalar(x_211)) {
 x_212 = lean_alloc_ctor(1, 2, 0);
} else {
 x_212 = x_211;
}
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_210);
return x_212;
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
uint8_t x_213; 
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_213 = !lean_is_exclusive(x_39);
if (x_213 == 0)
{
return x_39;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_39, 0);
x_215 = lean_ctor_get(x_39, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_39);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
}
else
{
uint8_t x_217; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_217 = !lean_is_exclusive(x_21);
if (x_217 == 0)
{
return x_21;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_21, 0);
x_219 = lean_ctor_get(x_21, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_21);
x_220 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("rwFixEq", 7, 7);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("expected saturated fixed-point application in {lhs'}", 52, 52);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = l_Lean_Meta_throwTacticEx___redArg(x_14, x_1, x_18, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_instInhabitedExpr;
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__2), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_7);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_1, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__0(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___lam__1(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_7 = x_13;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_5 = x_14;
x_10 = x_15;
goto _start;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_13;
}
}
else
{
lean_object* x_20; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_5);
lean_ctor_set(x_20, 1, x_10);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_12; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_501; lean_object* x_502; uint8_t x_503; 
x_33 = lean_mk_string_unchecked("Elab", 4, 4);
x_34 = lean_mk_string_unchecked("definition", 10, 10);
x_35 = lean_mk_string_unchecked("wf", 2, 2);
x_36 = lean_mk_string_unchecked("eqns", 4, 4);
x_37 = l_Lean_Name_mkStr4(x_33, x_34, x_35, x_36);
lean_inc(x_37);
x_501 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_3, x_4, x_5, x_6, x_7);
x_502 = lean_ctor_get(x_501, 0);
lean_inc(x_502);
x_503 = lean_unbox(x_502);
lean_dec(x_502);
if (x_503 == 0)
{
lean_object* x_504; 
x_504 = lean_ctor_get(x_501, 1);
lean_inc(x_504);
lean_dec(x_501);
x_489 = x_3;
x_490 = x_4;
x_491 = x_5;
x_492 = x_6;
x_493 = x_504;
goto block_500;
}
else
{
uint8_t x_505; 
x_505 = !lean_is_exclusive(x_501);
if (x_505 == 0)
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_506 = lean_ctor_get(x_501, 1);
x_507 = lean_ctor_get(x_501, 0);
lean_dec(x_507);
x_508 = lean_mk_string_unchecked("step\n", 5, 5);
x_509 = l_Lean_stringToMessageData(x_508);
lean_dec(x_508);
lean_inc(x_2);
x_510 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_510, 0, x_2);
lean_ctor_set_tag(x_501, 7);
lean_ctor_set(x_501, 1, x_510);
lean_ctor_set(x_501, 0, x_509);
x_511 = lean_mk_string_unchecked("", 0, 0);
x_512 = l_Lean_stringToMessageData(x_511);
lean_dec(x_511);
x_513 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_513, 0, x_501);
lean_ctor_set(x_513, 1, x_512);
lean_inc(x_37);
x_514 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_513, x_3, x_4, x_5, x_6, x_506);
x_515 = lean_ctor_get(x_514, 1);
lean_inc(x_515);
lean_dec(x_514);
x_489 = x_3;
x_490 = x_4;
x_491 = x_5;
x_492 = x_6;
x_493 = x_515;
goto block_500;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; 
x_516 = lean_ctor_get(x_501, 1);
lean_inc(x_516);
lean_dec(x_501);
x_517 = lean_mk_string_unchecked("step\n", 5, 5);
x_518 = l_Lean_stringToMessageData(x_517);
lean_dec(x_517);
lean_inc(x_2);
x_519 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_519, 0, x_2);
x_520 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_520, 0, x_518);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_mk_string_unchecked("", 0, 0);
x_522 = l_Lean_stringToMessageData(x_521);
lean_dec(x_521);
x_523 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_523, 0, x_520);
lean_ctor_set(x_523, 1, x_522);
lean_inc(x_37);
x_524 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_523, x_3, x_4, x_5, x_6, x_516);
x_525 = lean_ctor_get(x_524, 1);
lean_inc(x_525);
lean_dec(x_524);
x_489 = x_3;
x_490 = x_4;
x_491 = x_5;
x_492 = x_6;
x_493 = x_525;
goto block_500;
}
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
block_15:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
block_32:
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_23 = lean_array_get_size(x_16);
x_24 = lean_box(0);
x_25 = lean_nat_dec_lt(x_17, x_23);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_22);
return x_26;
}
else
{
uint8_t x_27; 
x_27 = lean_nat_dec_le(x_23, x_23);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_16);
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_22);
return x_28;
}
else
{
size_t x_29; size_t x_30; lean_object* x_31; 
x_29 = lean_usize_of_nat(x_17);
x_30 = lean_usize_of_nat(x_23);
lean_dec(x_23);
x_31 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__1(x_1, x_16, x_29, x_30, x_24, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_16);
return x_31;
}
}
}
block_488:
{
lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; uint8_t x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; uint8_t x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; uint8_t x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; 
x_44 = lean_ctor_get(x_39, 0);
lean_inc(x_44);
x_45 = lean_ctor_get_uint8(x_44, 0);
x_46 = lean_ctor_get_uint8(x_44, 1);
x_47 = lean_ctor_get_uint8(x_44, 2);
x_48 = lean_ctor_get_uint8(x_44, 3);
x_49 = lean_ctor_get_uint8(x_44, 4);
x_50 = lean_ctor_get_uint8(x_44, 5);
x_51 = lean_ctor_get_uint8(x_44, 6);
x_52 = lean_ctor_get_uint8(x_44, 7);
x_53 = lean_ctor_get_uint8(x_44, 8);
x_54 = lean_ctor_get_uint8(x_44, 10);
x_55 = lean_ctor_get_uint8(x_44, 11);
x_56 = lean_ctor_get_uint8(x_44, 12);
x_57 = lean_ctor_get_uint8(x_44, 13);
x_58 = lean_ctor_get_uint8(x_44, 14);
x_59 = lean_ctor_get_uint8(x_44, 15);
x_60 = lean_ctor_get_uint8(x_44, 16);
x_61 = lean_ctor_get_uint8(x_44, 17);
lean_dec(x_44);
x_62 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_62, 0, x_45);
lean_ctor_set_uint8(x_62, 1, x_46);
lean_ctor_set_uint8(x_62, 2, x_47);
lean_ctor_set_uint8(x_62, 3, x_48);
lean_ctor_set_uint8(x_62, 4, x_49);
lean_ctor_set_uint8(x_62, 5, x_50);
lean_ctor_set_uint8(x_62, 6, x_51);
lean_ctor_set_uint8(x_62, 7, x_52);
lean_ctor_set_uint8(x_62, 8, x_53);
lean_ctor_set_uint8(x_62, 9, x_43);
lean_ctor_set_uint8(x_62, 10, x_54);
lean_ctor_set_uint8(x_62, 11, x_55);
lean_ctor_set_uint8(x_62, 12, x_56);
lean_ctor_set_uint8(x_62, 13, x_57);
lean_ctor_set_uint8(x_62, 14, x_58);
lean_ctor_set_uint8(x_62, 15, x_59);
lean_ctor_set_uint8(x_62, 16, x_60);
lean_ctor_set_uint8(x_62, 17, x_61);
x_63 = lean_ctor_get_uint64(x_39, sizeof(void*)*7);
x_64 = lean_unsigned_to_nat(2u);
x_65 = lean_uint64_of_nat(x_64);
x_66 = lean_uint64_shift_right(x_63, x_65);
x_67 = lean_uint64_shift_left(x_66, x_65);
x_68 = l_Lean_Meta_TransparencyMode_toUInt64(x_43);
x_69 = lean_uint64_lor(x_67, x_68);
x_70 = lean_ctor_get_uint8(x_39, sizeof(void*)*7 + 8);
x_71 = lean_ctor_get(x_39, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_39, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_39, 3);
lean_inc(x_73);
x_74 = lean_ctor_get(x_39, 4);
lean_inc(x_74);
x_75 = lean_ctor_get(x_39, 5);
lean_inc(x_75);
x_76 = lean_ctor_get(x_39, 6);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_39, sizeof(void*)*7 + 9);
x_78 = lean_ctor_get_uint8(x_39, sizeof(void*)*7 + 10);
x_79 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_79, 0, x_62);
lean_ctor_set(x_79, 1, x_71);
lean_ctor_set(x_79, 2, x_72);
lean_ctor_set(x_79, 3, x_73);
lean_ctor_set(x_79, 4, x_74);
lean_ctor_set(x_79, 5, x_75);
lean_ctor_set(x_79, 6, x_76);
lean_ctor_set_uint64(x_79, sizeof(void*)*7, x_69);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 8, x_70);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 9, x_77);
lean_ctor_set_uint8(x_79, sizeof(void*)*7 + 10, x_78);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_2);
x_80 = l_Lean_Elab_Eqns_tryURefl(x_2, x_79, x_40, x_42, x_38, x_41);
lean_dec(x_79);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = lean_ctor_get(x_80, 1);
lean_inc(x_83);
lean_dec(x_80);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_2);
x_84 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_39, x_40, x_42, x_38, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_2);
x_88 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_39, x_40, x_42, x_38, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; 
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_2);
x_91 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_39, x_40, x_42, x_38, x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
if (lean_obj_tag(x_92) == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; uint8_t x_99; uint8_t x_100; uint8_t x_101; uint8_t x_102; uint8_t x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; uint8_t x_111; uint8_t x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; uint8_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; uint8_t x_133; 
x_93 = lean_ctor_get(x_91, 1);
lean_inc(x_93);
lean_dec(x_91);
x_94 = lean_box(1);
x_95 = lean_unsigned_to_nat(100000u);
x_96 = lean_box(2);
x_97 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_64);
x_98 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2, x_98);
x_99 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 1, x_99);
x_100 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 2, x_100);
x_101 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 3, x_101);
x_102 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 4, x_102);
x_103 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 5, x_103);
x_104 = lean_unbox(x_96);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 6, x_104);
x_105 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 7, x_105);
x_106 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 8, x_106);
x_107 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 9, x_107);
x_108 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 10, x_108);
x_109 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 11, x_109);
x_110 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 12, x_110);
x_111 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 13, x_111);
x_112 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 14, x_112);
x_113 = lean_unbox(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 15, x_113);
x_114 = lean_unbox(x_85);
lean_dec(x_85);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 16, x_114);
x_115 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 17, x_115);
x_116 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 18, x_116);
x_117 = lean_unbox(x_94);
lean_ctor_set_uint8(x_97, sizeof(void*)*2 + 19, x_117);
x_118 = l_Array_empty(lean_box(0));
x_119 = lean_unsigned_to_nat(8u);
x_120 = lean_unsigned_to_nat(0u);
x_121 = lean_nat_shiftl(x_119, x_64);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_div(x_121, x_122);
lean_dec(x_121);
x_124 = l_Nat_nextPowerOfTwo(x_123);
lean_dec(x_123);
x_125 = lean_box(0);
x_126 = lean_mk_array(x_124, x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_120);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_128);
x_129 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_unbox(x_94);
lean_ctor_set_uint8(x_130, sizeof(void*)*2, x_131);
lean_inc(x_118);
x_132 = l_Lean_Meta_Simp_mkContext(x_97, x_118, x_130, x_39, x_40, x_42, x_38, x_93);
x_133 = !lean_is_exclusive(x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; size_t x_140; lean_object* x_141; lean_object* x_142; size_t x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_134 = lean_ctor_get(x_132, 0);
x_135 = lean_ctor_get(x_132, 1);
x_136 = lean_box(0);
lean_inc(x_128);
x_137 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_137, 0, x_128);
lean_inc(x_137);
lean_ctor_set(x_132, 1, x_120);
lean_ctor_set(x_132, 0, x_137);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_128);
x_139 = lean_unsigned_to_nat(5u);
x_140 = lean_usize_of_nat(x_139);
x_141 = lean_usize_to_nat(x_140);
x_142 = lean_nat_pow(x_64, x_141);
lean_dec(x_141);
x_143 = lean_usize_of_nat(x_142);
lean_dec(x_142);
x_144 = lean_usize_to_nat(x_143);
x_145 = lean_mk_empty_array_with_capacity(x_144);
lean_dec(x_144);
lean_inc(x_145);
x_146 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_146, 0, x_145);
x_147 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_147, 0, x_146);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_120);
lean_ctor_set(x_147, 3, x_120);
lean_ctor_set_usize(x_147, 4, x_140);
lean_inc(x_137);
x_148 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_148, 0, x_137);
lean_ctor_set(x_148, 1, x_137);
lean_ctor_set(x_148, 2, x_138);
lean_ctor_set(x_148, 3, x_147);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_132);
lean_ctor_set(x_149, 1, x_148);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_2);
x_150 = l_Lean_Meta_simpTargetStar(x_2, x_134, x_118, x_136, x_149, x_39, x_40, x_42, x_38, x_135);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
lean_dec(x_151);
switch (lean_obj_tag(x_152)) {
case 0:
{
uint8_t x_153; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_153 = !lean_is_exclusive(x_150);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_150, 0);
lean_dec(x_154);
x_155 = lean_box(0);
lean_ctor_set(x_150, 0, x_155);
return x_150;
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; 
x_156 = lean_ctor_get(x_150, 1);
lean_inc(x_156);
lean_dec(x_150);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_157);
lean_ctor_set(x_158, 1, x_156);
return x_158;
}
}
case 1:
{
lean_object* x_159; lean_object* x_160; 
x_159 = lean_ctor_get(x_150, 1);
lean_inc(x_159);
lean_dec(x_150);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_2);
x_160 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_39, x_40, x_42, x_38, x_159);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_unbox(x_94);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_2);
x_164 = l_Lean_Meta_splitTarget_x3f(x_2, x_163, x_39, x_40, x_42, x_38, x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
if (lean_obj_tag(x_165) == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_37);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
x_168 = l_Lean_stringToMessageData(x_167);
lean_dec(x_167);
x_169 = l_Lean_MessageData_ofName(x_1);
x_170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
x_171 = lean_mk_string_unchecked("'\n", 2, 2);
x_172 = l_Lean_stringToMessageData(x_171);
lean_dec(x_171);
x_173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_172);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_2);
x_175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_mk_string_unchecked("", 0, 0);
x_177 = l_Lean_stringToMessageData(x_176);
lean_dec(x_176);
x_178 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_177);
x_179 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_178, x_39, x_40, x_42, x_38, x_166);
lean_dec(x_38);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
return x_179;
}
else
{
lean_object* x_180; uint8_t x_181; 
lean_dec(x_2);
x_180 = lean_ctor_get(x_164, 1);
lean_inc(x_180);
lean_dec(x_164);
x_181 = !lean_is_exclusive(x_165);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint8_t x_185; 
x_182 = lean_ctor_get(x_165, 0);
lean_inc(x_37);
x_183 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_180);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_unbox(x_184);
lean_dec(x_184);
if (x_185 == 0)
{
lean_object* x_186; lean_object* x_187; 
lean_free_object(x_165);
lean_dec(x_37);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_186);
lean_dec(x_183);
x_187 = l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_182, x_39, x_40, x_42, x_38, x_186);
return x_187;
}
else
{
uint8_t x_188; 
x_188 = !lean_is_exclusive(x_183);
if (x_188 == 0)
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_189 = lean_ctor_get(x_183, 1);
x_190 = lean_ctor_get(x_183, 0);
lean_dec(x_190);
x_191 = lean_mk_string_unchecked("splitTarget into ", 17, 17);
x_192 = l_Lean_stringToMessageData(x_191);
lean_dec(x_191);
x_193 = l_List_lengthTR(lean_box(0), x_182);
x_194 = l___private_Init_Data_Repr_0__Nat_reprFast(x_193);
lean_ctor_set_tag(x_165, 3);
lean_ctor_set(x_165, 0, x_194);
x_195 = l_Lean_MessageData_ofFormat(x_165);
lean_ctor_set_tag(x_183, 7);
lean_ctor_set(x_183, 1, x_195);
lean_ctor_set(x_183, 0, x_192);
x_196 = lean_mk_string_unchecked(" goals", 6, 6);
x_197 = l_Lean_stringToMessageData(x_196);
lean_dec(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_183);
lean_ctor_set(x_198, 1, x_197);
x_199 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_198, x_39, x_40, x_42, x_38, x_189);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_182, x_39, x_40, x_42, x_38, x_200);
return x_201;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_202 = lean_ctor_get(x_183, 1);
lean_inc(x_202);
lean_dec(x_183);
x_203 = lean_mk_string_unchecked("splitTarget into ", 17, 17);
x_204 = l_Lean_stringToMessageData(x_203);
lean_dec(x_203);
x_205 = l_List_lengthTR(lean_box(0), x_182);
x_206 = l___private_Init_Data_Repr_0__Nat_reprFast(x_205);
lean_ctor_set_tag(x_165, 3);
lean_ctor_set(x_165, 0, x_206);
x_207 = l_Lean_MessageData_ofFormat(x_165);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_204);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_mk_string_unchecked(" goals", 6, 6);
x_210 = l_Lean_stringToMessageData(x_209);
lean_dec(x_209);
x_211 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_210);
x_212 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_211, x_39, x_40, x_42, x_38, x_202);
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_214 = l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_182, x_39, x_40, x_42, x_38, x_213);
return x_214;
}
}
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; uint8_t x_218; 
x_215 = lean_ctor_get(x_165, 0);
lean_inc(x_215);
lean_dec(x_165);
lean_inc(x_37);
x_216 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_180);
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_unbox(x_217);
lean_dec(x_217);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_37);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
x_220 = l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_215, x_39, x_40, x_42, x_38, x_219);
return x_220;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_221 = lean_ctor_get(x_216, 1);
lean_inc(x_221);
if (lean_is_exclusive(x_216)) {
 lean_ctor_release(x_216, 0);
 lean_ctor_release(x_216, 1);
 x_222 = x_216;
} else {
 lean_dec_ref(x_216);
 x_222 = lean_box(0);
}
x_223 = lean_mk_string_unchecked("splitTarget into ", 17, 17);
x_224 = l_Lean_stringToMessageData(x_223);
lean_dec(x_223);
x_225 = l_List_lengthTR(lean_box(0), x_215);
x_226 = l___private_Init_Data_Repr_0__Nat_reprFast(x_225);
x_227 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_227, 0, x_226);
x_228 = l_Lean_MessageData_ofFormat(x_227);
if (lean_is_scalar(x_222)) {
 x_229 = lean_alloc_ctor(7, 2, 0);
} else {
 x_229 = x_222;
 lean_ctor_set_tag(x_229, 7);
}
lean_ctor_set(x_229, 0, x_224);
lean_ctor_set(x_229, 1, x_228);
x_230 = lean_mk_string_unchecked(" goals", 6, 6);
x_231 = l_Lean_stringToMessageData(x_230);
lean_dec(x_230);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_229);
lean_ctor_set(x_232, 1, x_231);
x_233 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_232, x_39, x_40, x_42, x_38, x_221);
x_234 = lean_ctor_get(x_233, 1);
lean_inc(x_234);
lean_dec(x_233);
x_235 = l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_215, x_39, x_40, x_42, x_38, x_234);
return x_235;
}
}
}
}
else
{
uint8_t x_236; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_236 = !lean_is_exclusive(x_164);
if (x_236 == 0)
{
return x_164;
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; 
x_237 = lean_ctor_get(x_164, 0);
x_238 = lean_ctor_get(x_164, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_164);
x_239 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
return x_239;
}
}
}
else
{
lean_object* x_240; uint8_t x_241; 
lean_dec(x_2);
x_240 = lean_ctor_get(x_160, 1);
lean_inc(x_240);
lean_dec(x_160);
x_241 = !lean_is_exclusive(x_161);
if (x_241 == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_242 = lean_ctor_get(x_161, 0);
lean_inc(x_37);
x_243 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_240);
x_244 = lean_ctor_get(x_243, 0);
lean_inc(x_244);
x_245 = lean_unbox(x_244);
lean_dec(x_244);
if (x_245 == 0)
{
lean_object* x_246; 
lean_free_object(x_161);
lean_dec(x_37);
x_246 = lean_ctor_get(x_243, 1);
lean_inc(x_246);
lean_dec(x_243);
x_16 = x_242;
x_17 = x_120;
x_18 = x_39;
x_19 = x_40;
x_20 = x_42;
x_21 = x_38;
x_22 = x_246;
goto block_32;
}
else
{
uint8_t x_247; 
x_247 = !lean_is_exclusive(x_243);
if (x_247 == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_248 = lean_ctor_get(x_243, 1);
x_249 = lean_ctor_get(x_243, 0);
lean_dec(x_249);
x_250 = lean_mk_string_unchecked("case split into ", 16, 16);
x_251 = l_Lean_stringToMessageData(x_250);
lean_dec(x_250);
x_252 = lean_array_get_size(x_242);
x_253 = l___private_Init_Data_Repr_0__Nat_reprFast(x_252);
lean_ctor_set_tag(x_161, 3);
lean_ctor_set(x_161, 0, x_253);
x_254 = l_Lean_MessageData_ofFormat(x_161);
lean_ctor_set_tag(x_243, 7);
lean_ctor_set(x_243, 1, x_254);
lean_ctor_set(x_243, 0, x_251);
x_255 = lean_mk_string_unchecked(" goals", 6, 6);
x_256 = l_Lean_stringToMessageData(x_255);
lean_dec(x_255);
x_257 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_257, 0, x_243);
lean_ctor_set(x_257, 1, x_256);
x_258 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_257, x_39, x_40, x_42, x_38, x_248);
x_259 = lean_ctor_get(x_258, 1);
lean_inc(x_259);
lean_dec(x_258);
x_16 = x_242;
x_17 = x_120;
x_18 = x_39;
x_19 = x_40;
x_20 = x_42;
x_21 = x_38;
x_22 = x_259;
goto block_32;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_260 = lean_ctor_get(x_243, 1);
lean_inc(x_260);
lean_dec(x_243);
x_261 = lean_mk_string_unchecked("case split into ", 16, 16);
x_262 = l_Lean_stringToMessageData(x_261);
lean_dec(x_261);
x_263 = lean_array_get_size(x_242);
x_264 = l___private_Init_Data_Repr_0__Nat_reprFast(x_263);
lean_ctor_set_tag(x_161, 3);
lean_ctor_set(x_161, 0, x_264);
x_265 = l_Lean_MessageData_ofFormat(x_161);
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_262);
lean_ctor_set(x_266, 1, x_265);
x_267 = lean_mk_string_unchecked(" goals", 6, 6);
x_268 = l_Lean_stringToMessageData(x_267);
lean_dec(x_267);
x_269 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_268);
x_270 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_269, x_39, x_40, x_42, x_38, x_260);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
lean_dec(x_270);
x_16 = x_242;
x_17 = x_120;
x_18 = x_39;
x_19 = x_40;
x_20 = x_42;
x_21 = x_38;
x_22 = x_271;
goto block_32;
}
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; uint8_t x_275; 
x_272 = lean_ctor_get(x_161, 0);
lean_inc(x_272);
lean_dec(x_161);
lean_inc(x_37);
x_273 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_240);
x_274 = lean_ctor_get(x_273, 0);
lean_inc(x_274);
x_275 = lean_unbox(x_274);
lean_dec(x_274);
if (x_275 == 0)
{
lean_object* x_276; 
lean_dec(x_37);
x_276 = lean_ctor_get(x_273, 1);
lean_inc(x_276);
lean_dec(x_273);
x_16 = x_272;
x_17 = x_120;
x_18 = x_39;
x_19 = x_40;
x_20 = x_42;
x_21 = x_38;
x_22 = x_276;
goto block_32;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_277 = lean_ctor_get(x_273, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_273)) {
 lean_ctor_release(x_273, 0);
 lean_ctor_release(x_273, 1);
 x_278 = x_273;
} else {
 lean_dec_ref(x_273);
 x_278 = lean_box(0);
}
x_279 = lean_mk_string_unchecked("case split into ", 16, 16);
x_280 = l_Lean_stringToMessageData(x_279);
lean_dec(x_279);
x_281 = lean_array_get_size(x_272);
x_282 = l___private_Init_Data_Repr_0__Nat_reprFast(x_281);
x_283 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_283, 0, x_282);
x_284 = l_Lean_MessageData_ofFormat(x_283);
if (lean_is_scalar(x_278)) {
 x_285 = lean_alloc_ctor(7, 2, 0);
} else {
 x_285 = x_278;
 lean_ctor_set_tag(x_285, 7);
}
lean_ctor_set(x_285, 0, x_280);
lean_ctor_set(x_285, 1, x_284);
x_286 = lean_mk_string_unchecked(" goals", 6, 6);
x_287 = l_Lean_stringToMessageData(x_286);
lean_dec(x_286);
x_288 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_288, 0, x_285);
lean_ctor_set(x_288, 1, x_287);
x_289 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_288, x_39, x_40, x_42, x_38, x_277);
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
x_16 = x_272;
x_17 = x_120;
x_18 = x_39;
x_19 = x_40;
x_20 = x_42;
x_21 = x_38;
x_22 = x_290;
goto block_32;
}
}
}
}
else
{
uint8_t x_291; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_291 = !lean_is_exclusive(x_160);
if (x_291 == 0)
{
return x_160;
}
else
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
x_292 = lean_ctor_get(x_160, 0);
x_293 = lean_ctor_get(x_160, 1);
lean_inc(x_293);
lean_inc(x_292);
lean_dec(x_160);
x_294 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_294, 0, x_292);
lean_ctor_set(x_294, 1, x_293);
return x_294;
}
}
}
default: 
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; uint8_t x_299; 
lean_dec(x_2);
x_295 = lean_ctor_get(x_150, 1);
lean_inc(x_295);
lean_dec(x_150);
x_296 = lean_ctor_get(x_152, 0);
lean_inc(x_296);
lean_dec(x_152);
lean_inc(x_37);
x_297 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_295);
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_unbox(x_298);
lean_dec(x_298);
if (x_299 == 0)
{
lean_object* x_300; 
lean_dec(x_37);
x_300 = lean_ctor_get(x_297, 1);
lean_inc(x_300);
lean_dec(x_297);
x_2 = x_296;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_300;
goto _start;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
x_302 = lean_ctor_get(x_297, 1);
lean_inc(x_302);
lean_dec(x_297);
x_303 = lean_mk_string_unchecked("simp only!", 10, 10);
x_304 = l_Lean_stringToMessageData(x_303);
lean_dec(x_303);
x_305 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_304, x_39, x_40, x_42, x_38, x_302);
x_306 = lean_ctor_get(x_305, 1);
lean_inc(x_306);
lean_dec(x_305);
x_2 = x_296;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_306;
goto _start;
}
}
}
}
else
{
uint8_t x_308; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_308 = !lean_is_exclusive(x_150);
if (x_308 == 0)
{
return x_150;
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; 
x_309 = lean_ctor_get(x_150, 0);
x_310 = lean_ctor_get(x_150, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_150);
x_311 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_311, 0, x_309);
lean_ctor_set(x_311, 1, x_310);
return x_311;
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; size_t x_319; lean_object* x_320; lean_object* x_321; size_t x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_312 = lean_ctor_get(x_132, 0);
x_313 = lean_ctor_get(x_132, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_132);
x_314 = lean_box(0);
lean_inc(x_128);
x_315 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_315, 0, x_128);
lean_inc(x_315);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_120);
x_317 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_317, 0, x_128);
x_318 = lean_unsigned_to_nat(5u);
x_319 = lean_usize_of_nat(x_318);
x_320 = lean_usize_to_nat(x_319);
x_321 = lean_nat_pow(x_64, x_320);
lean_dec(x_320);
x_322 = lean_usize_of_nat(x_321);
lean_dec(x_321);
x_323 = lean_usize_to_nat(x_322);
x_324 = lean_mk_empty_array_with_capacity(x_323);
lean_dec(x_323);
lean_inc(x_324);
x_325 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_325, 0, x_324);
x_326 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_326, 0, x_325);
lean_ctor_set(x_326, 1, x_324);
lean_ctor_set(x_326, 2, x_120);
lean_ctor_set(x_326, 3, x_120);
lean_ctor_set_usize(x_326, 4, x_319);
lean_inc(x_315);
x_327 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_327, 0, x_315);
lean_ctor_set(x_327, 1, x_315);
lean_ctor_set(x_327, 2, x_317);
lean_ctor_set(x_327, 3, x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_316);
lean_ctor_set(x_328, 1, x_327);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_2);
x_329 = l_Lean_Meta_simpTargetStar(x_2, x_312, x_118, x_314, x_328, x_39, x_40, x_42, x_38, x_313);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_330, 0);
lean_inc(x_331);
lean_dec(x_330);
switch (lean_obj_tag(x_331)) {
case 0:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_332 = lean_ctor_get(x_329, 1);
lean_inc(x_332);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_333 = x_329;
} else {
 lean_dec_ref(x_329);
 x_333 = lean_box(0);
}
x_334 = lean_box(0);
if (lean_is_scalar(x_333)) {
 x_335 = lean_alloc_ctor(0, 2, 0);
} else {
 x_335 = x_333;
}
lean_ctor_set(x_335, 0, x_334);
lean_ctor_set(x_335, 1, x_332);
return x_335;
}
case 1:
{
lean_object* x_336; lean_object* x_337; 
x_336 = lean_ctor_get(x_329, 1);
lean_inc(x_336);
lean_dec(x_329);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_2);
x_337 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_39, x_40, x_42, x_38, x_336);
if (lean_obj_tag(x_337) == 0)
{
lean_object* x_338; 
x_338 = lean_ctor_get(x_337, 0);
lean_inc(x_338);
if (lean_obj_tag(x_338) == 0)
{
lean_object* x_339; uint8_t x_340; lean_object* x_341; 
x_339 = lean_ctor_get(x_337, 1);
lean_inc(x_339);
lean_dec(x_337);
x_340 = lean_unbox(x_94);
lean_inc(x_38);
lean_inc(x_42);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_2);
x_341 = l_Lean_Meta_splitTarget_x3f(x_2, x_340, x_39, x_40, x_42, x_38, x_339);
if (lean_obj_tag(x_341) == 0)
{
lean_object* x_342; 
x_342 = lean_ctor_get(x_341, 0);
lean_inc(x_342);
if (lean_obj_tag(x_342) == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; 
lean_dec(x_37);
x_343 = lean_ctor_get(x_341, 1);
lean_inc(x_343);
lean_dec(x_341);
x_344 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
x_345 = l_Lean_stringToMessageData(x_344);
lean_dec(x_344);
x_346 = l_Lean_MessageData_ofName(x_1);
x_347 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_347, 0, x_345);
lean_ctor_set(x_347, 1, x_346);
x_348 = lean_mk_string_unchecked("'\n", 2, 2);
x_349 = l_Lean_stringToMessageData(x_348);
lean_dec(x_348);
x_350 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_350, 0, x_347);
lean_ctor_set(x_350, 1, x_349);
x_351 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_351, 0, x_2);
x_352 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_352, 0, x_350);
lean_ctor_set(x_352, 1, x_351);
x_353 = lean_mk_string_unchecked("", 0, 0);
x_354 = l_Lean_stringToMessageData(x_353);
lean_dec(x_353);
x_355 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_355, 0, x_352);
lean_ctor_set(x_355, 1, x_354);
x_356 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_355, x_39, x_40, x_42, x_38, x_343);
lean_dec(x_38);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
return x_356;
}
else
{
lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; uint8_t x_362; 
lean_dec(x_2);
x_357 = lean_ctor_get(x_341, 1);
lean_inc(x_357);
lean_dec(x_341);
x_358 = lean_ctor_get(x_342, 0);
lean_inc(x_358);
if (lean_is_exclusive(x_342)) {
 lean_ctor_release(x_342, 0);
 x_359 = x_342;
} else {
 lean_dec_ref(x_342);
 x_359 = lean_box(0);
}
lean_inc(x_37);
x_360 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_357);
x_361 = lean_ctor_get(x_360, 0);
lean_inc(x_361);
x_362 = lean_unbox(x_361);
lean_dec(x_361);
if (x_362 == 0)
{
lean_object* x_363; lean_object* x_364; 
lean_dec(x_359);
lean_dec(x_37);
x_363 = lean_ctor_get(x_360, 1);
lean_inc(x_363);
lean_dec(x_360);
x_364 = l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_358, x_39, x_40, x_42, x_38, x_363);
return x_364;
}
else
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_365 = lean_ctor_get(x_360, 1);
lean_inc(x_365);
if (lean_is_exclusive(x_360)) {
 lean_ctor_release(x_360, 0);
 lean_ctor_release(x_360, 1);
 x_366 = x_360;
} else {
 lean_dec_ref(x_360);
 x_366 = lean_box(0);
}
x_367 = lean_mk_string_unchecked("splitTarget into ", 17, 17);
x_368 = l_Lean_stringToMessageData(x_367);
lean_dec(x_367);
x_369 = l_List_lengthTR(lean_box(0), x_358);
x_370 = l___private_Init_Data_Repr_0__Nat_reprFast(x_369);
if (lean_is_scalar(x_359)) {
 x_371 = lean_alloc_ctor(3, 1, 0);
} else {
 x_371 = x_359;
 lean_ctor_set_tag(x_371, 3);
}
lean_ctor_set(x_371, 0, x_370);
x_372 = l_Lean_MessageData_ofFormat(x_371);
if (lean_is_scalar(x_366)) {
 x_373 = lean_alloc_ctor(7, 2, 0);
} else {
 x_373 = x_366;
 lean_ctor_set_tag(x_373, 7);
}
lean_ctor_set(x_373, 0, x_368);
lean_ctor_set(x_373, 1, x_372);
x_374 = lean_mk_string_unchecked(" goals", 6, 6);
x_375 = l_Lean_stringToMessageData(x_374);
lean_dec(x_374);
x_376 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_376, 0, x_373);
lean_ctor_set(x_376, 1, x_375);
x_377 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_376, x_39, x_40, x_42, x_38, x_365);
x_378 = lean_ctor_get(x_377, 1);
lean_inc(x_378);
lean_dec(x_377);
x_379 = l_List_forM___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__0(x_1, x_358, x_39, x_40, x_42, x_38, x_378);
return x_379;
}
}
}
else
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_380 = lean_ctor_get(x_341, 0);
lean_inc(x_380);
x_381 = lean_ctor_get(x_341, 1);
lean_inc(x_381);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_382 = x_341;
} else {
 lean_dec_ref(x_341);
 x_382 = lean_box(0);
}
if (lean_is_scalar(x_382)) {
 x_383 = lean_alloc_ctor(1, 2, 0);
} else {
 x_383 = x_382;
}
lean_ctor_set(x_383, 0, x_380);
lean_ctor_set(x_383, 1, x_381);
return x_383;
}
}
else
{
lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
lean_dec(x_2);
x_384 = lean_ctor_get(x_337, 1);
lean_inc(x_384);
lean_dec(x_337);
x_385 = lean_ctor_get(x_338, 0);
lean_inc(x_385);
if (lean_is_exclusive(x_338)) {
 lean_ctor_release(x_338, 0);
 x_386 = x_338;
} else {
 lean_dec_ref(x_338);
 x_386 = lean_box(0);
}
lean_inc(x_37);
x_387 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_384);
x_388 = lean_ctor_get(x_387, 0);
lean_inc(x_388);
x_389 = lean_unbox(x_388);
lean_dec(x_388);
if (x_389 == 0)
{
lean_object* x_390; 
lean_dec(x_386);
lean_dec(x_37);
x_390 = lean_ctor_get(x_387, 1);
lean_inc(x_390);
lean_dec(x_387);
x_16 = x_385;
x_17 = x_120;
x_18 = x_39;
x_19 = x_40;
x_20 = x_42;
x_21 = x_38;
x_22 = x_390;
goto block_32;
}
else
{
lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_391 = lean_ctor_get(x_387, 1);
lean_inc(x_391);
if (lean_is_exclusive(x_387)) {
 lean_ctor_release(x_387, 0);
 lean_ctor_release(x_387, 1);
 x_392 = x_387;
} else {
 lean_dec_ref(x_387);
 x_392 = lean_box(0);
}
x_393 = lean_mk_string_unchecked("case split into ", 16, 16);
x_394 = l_Lean_stringToMessageData(x_393);
lean_dec(x_393);
x_395 = lean_array_get_size(x_385);
x_396 = l___private_Init_Data_Repr_0__Nat_reprFast(x_395);
if (lean_is_scalar(x_386)) {
 x_397 = lean_alloc_ctor(3, 1, 0);
} else {
 x_397 = x_386;
 lean_ctor_set_tag(x_397, 3);
}
lean_ctor_set(x_397, 0, x_396);
x_398 = l_Lean_MessageData_ofFormat(x_397);
if (lean_is_scalar(x_392)) {
 x_399 = lean_alloc_ctor(7, 2, 0);
} else {
 x_399 = x_392;
 lean_ctor_set_tag(x_399, 7);
}
lean_ctor_set(x_399, 0, x_394);
lean_ctor_set(x_399, 1, x_398);
x_400 = lean_mk_string_unchecked(" goals", 6, 6);
x_401 = l_Lean_stringToMessageData(x_400);
lean_dec(x_400);
x_402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_402, 0, x_399);
lean_ctor_set(x_402, 1, x_401);
x_403 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_402, x_39, x_40, x_42, x_38, x_391);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_16 = x_385;
x_17 = x_120;
x_18 = x_39;
x_19 = x_40;
x_20 = x_42;
x_21 = x_38;
x_22 = x_404;
goto block_32;
}
}
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_405 = lean_ctor_get(x_337, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_337, 1);
lean_inc(x_406);
if (lean_is_exclusive(x_337)) {
 lean_ctor_release(x_337, 0);
 lean_ctor_release(x_337, 1);
 x_407 = x_337;
} else {
 lean_dec_ref(x_337);
 x_407 = lean_box(0);
}
if (lean_is_scalar(x_407)) {
 x_408 = lean_alloc_ctor(1, 2, 0);
} else {
 x_408 = x_407;
}
lean_ctor_set(x_408, 0, x_405);
lean_ctor_set(x_408, 1, x_406);
return x_408;
}
}
default: 
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_413; 
lean_dec(x_2);
x_409 = lean_ctor_get(x_329, 1);
lean_inc(x_409);
lean_dec(x_329);
x_410 = lean_ctor_get(x_331, 0);
lean_inc(x_410);
lean_dec(x_331);
lean_inc(x_37);
x_411 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_409);
x_412 = lean_ctor_get(x_411, 0);
lean_inc(x_412);
x_413 = lean_unbox(x_412);
lean_dec(x_412);
if (x_413 == 0)
{
lean_object* x_414; 
lean_dec(x_37);
x_414 = lean_ctor_get(x_411, 1);
lean_inc(x_414);
lean_dec(x_411);
x_2 = x_410;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_414;
goto _start;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
x_416 = lean_ctor_get(x_411, 1);
lean_inc(x_416);
lean_dec(x_411);
x_417 = lean_mk_string_unchecked("simp only!", 10, 10);
x_418 = l_Lean_stringToMessageData(x_417);
lean_dec(x_417);
x_419 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_418, x_39, x_40, x_42, x_38, x_416);
x_420 = lean_ctor_get(x_419, 1);
lean_inc(x_420);
lean_dec(x_419);
x_2 = x_410;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_420;
goto _start;
}
}
}
}
else
{
lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_422 = lean_ctor_get(x_329, 0);
lean_inc(x_422);
x_423 = lean_ctor_get(x_329, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_424 = x_329;
} else {
 lean_dec_ref(x_329);
 x_424 = lean_box(0);
}
if (lean_is_scalar(x_424)) {
 x_425 = lean_alloc_ctor(1, 2, 0);
} else {
 x_425 = x_424;
}
lean_ctor_set(x_425, 0, x_422);
lean_ctor_set(x_425, 1, x_423);
return x_425;
}
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; uint8_t x_430; 
lean_dec(x_85);
lean_dec(x_2);
x_426 = lean_ctor_get(x_91, 1);
lean_inc(x_426);
lean_dec(x_91);
x_427 = lean_ctor_get(x_92, 0);
lean_inc(x_427);
lean_dec(x_92);
lean_inc(x_37);
x_428 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_426);
x_429 = lean_ctor_get(x_428, 0);
lean_inc(x_429);
x_430 = lean_unbox(x_429);
lean_dec(x_429);
if (x_430 == 0)
{
lean_object* x_431; 
lean_dec(x_37);
x_431 = lean_ctor_get(x_428, 1);
lean_inc(x_431);
lean_dec(x_428);
x_2 = x_427;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_431;
goto _start;
}
else
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_433 = lean_ctor_get(x_428, 1);
lean_inc(x_433);
lean_dec(x_428);
x_434 = lean_mk_string_unchecked("simpIf!", 7, 7);
x_435 = l_Lean_stringToMessageData(x_434);
lean_dec(x_434);
x_436 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_435, x_39, x_40, x_42, x_38, x_433);
x_437 = lean_ctor_get(x_436, 1);
lean_inc(x_437);
lean_dec(x_436);
x_2 = x_427;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_437;
goto _start;
}
}
}
else
{
uint8_t x_439; 
lean_dec(x_85);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_439 = !lean_is_exclusive(x_91);
if (x_439 == 0)
{
return x_91;
}
else
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; 
x_440 = lean_ctor_get(x_91, 0);
x_441 = lean_ctor_get(x_91, 1);
lean_inc(x_441);
lean_inc(x_440);
lean_dec(x_91);
x_442 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_442, 0, x_440);
lean_ctor_set(x_442, 1, x_441);
return x_442;
}
}
}
else
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; uint8_t x_447; 
lean_dec(x_85);
lean_dec(x_2);
x_443 = lean_ctor_get(x_88, 1);
lean_inc(x_443);
lean_dec(x_88);
x_444 = lean_ctor_get(x_89, 0);
lean_inc(x_444);
lean_dec(x_89);
lean_inc(x_37);
x_445 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_443);
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_unbox(x_446);
lean_dec(x_446);
if (x_447 == 0)
{
lean_object* x_448; 
lean_dec(x_37);
x_448 = lean_ctor_get(x_445, 1);
lean_inc(x_448);
lean_dec(x_445);
x_2 = x_444;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_448;
goto _start;
}
else
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; 
x_450 = lean_ctor_get(x_445, 1);
lean_inc(x_450);
lean_dec(x_445);
x_451 = lean_mk_string_unchecked("simpMatch!", 10, 10);
x_452 = l_Lean_stringToMessageData(x_451);
lean_dec(x_451);
x_453 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_452, x_39, x_40, x_42, x_38, x_450);
x_454 = lean_ctor_get(x_453, 1);
lean_inc(x_454);
lean_dec(x_453);
x_2 = x_444;
x_3 = x_39;
x_4 = x_40;
x_5 = x_42;
x_6 = x_38;
x_7 = x_454;
goto _start;
}
}
}
else
{
uint8_t x_456; 
lean_dec(x_85);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_456 = !lean_is_exclusive(x_88);
if (x_456 == 0)
{
return x_88;
}
else
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; 
x_457 = lean_ctor_get(x_88, 0);
x_458 = lean_ctor_get(x_88, 1);
lean_inc(x_458);
lean_inc(x_457);
lean_dec(x_88);
x_459 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_459, 0, x_457);
lean_ctor_set(x_459, 1, x_458);
return x_459;
}
}
}
else
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; uint8_t x_463; 
lean_dec(x_85);
lean_dec(x_2);
lean_dec(x_1);
x_460 = lean_ctor_get(x_84, 1);
lean_inc(x_460);
lean_dec(x_84);
lean_inc(x_37);
x_461 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_460);
x_462 = lean_ctor_get(x_461, 0);
lean_inc(x_462);
x_463 = lean_unbox(x_462);
lean_dec(x_462);
if (x_463 == 0)
{
lean_object* x_464; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_464 = lean_ctor_get(x_461, 1);
lean_inc(x_464);
lean_dec(x_461);
x_12 = x_464;
goto block_15;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
x_465 = lean_ctor_get(x_461, 1);
lean_inc(x_465);
lean_dec(x_461);
x_466 = lean_mk_string_unchecked("contradiction!", 14, 14);
x_467 = l_Lean_stringToMessageData(x_466);
lean_dec(x_466);
x_468 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_467, x_39, x_40, x_42, x_38, x_465);
lean_dec(x_38);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
x_469 = lean_ctor_get(x_468, 1);
lean_inc(x_469);
lean_dec(x_468);
x_12 = x_469;
goto block_15;
}
}
}
else
{
uint8_t x_470; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_470 = !lean_is_exclusive(x_84);
if (x_470 == 0)
{
return x_84;
}
else
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; 
x_471 = lean_ctor_get(x_84, 0);
x_472 = lean_ctor_get(x_84, 1);
lean_inc(x_472);
lean_inc(x_471);
lean_dec(x_84);
x_473 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_473, 0, x_471);
lean_ctor_set(x_473, 1, x_472);
return x_473;
}
}
}
else
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; 
lean_dec(x_2);
lean_dec(x_1);
x_474 = lean_ctor_get(x_80, 1);
lean_inc(x_474);
lean_dec(x_80);
lean_inc(x_37);
x_475 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_37, x_39, x_40, x_42, x_38, x_474);
x_476 = lean_ctor_get(x_475, 0);
lean_inc(x_476);
x_477 = lean_unbox(x_476);
lean_dec(x_476);
if (x_477 == 0)
{
lean_object* x_478; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
x_478 = lean_ctor_get(x_475, 1);
lean_inc(x_478);
lean_dec(x_475);
x_8 = x_478;
goto block_11;
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
x_479 = lean_ctor_get(x_475, 1);
lean_inc(x_479);
lean_dec(x_475);
x_480 = lean_mk_string_unchecked("refl!", 5, 5);
x_481 = l_Lean_stringToMessageData(x_480);
lean_dec(x_480);
x_482 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_37, x_481, x_39, x_40, x_42, x_38, x_479);
lean_dec(x_38);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
x_483 = lean_ctor_get(x_482, 1);
lean_inc(x_483);
lean_dec(x_482);
x_8 = x_483;
goto block_11;
}
}
}
else
{
uint8_t x_484; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_2);
lean_dec(x_1);
x_484 = !lean_is_exclusive(x_80);
if (x_484 == 0)
{
return x_80;
}
else
{
lean_object* x_485; lean_object* x_486; lean_object* x_487; 
x_485 = lean_ctor_get(x_80, 0);
x_486 = lean_ctor_get(x_80, 1);
lean_inc(x_486);
lean_inc(x_485);
lean_dec(x_80);
x_487 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_487, 0, x_485);
lean_ctor_set(x_487, 1, x_486);
return x_487;
}
}
}
block_500:
{
lean_object* x_494; lean_object* x_495; uint8_t x_496; uint8_t x_497; uint8_t x_498; 
x_494 = lean_box(0);
x_495 = lean_ctor_get(x_489, 0);
lean_inc(x_495);
x_496 = lean_ctor_get_uint8(x_495, 9);
lean_dec(x_495);
x_497 = lean_unbox(x_494);
x_498 = l_Lean_Meta_TransparencyMode_lt(x_496, x_497);
if (x_498 == 0)
{
x_38 = x_492;
x_39 = x_489;
x_40 = x_490;
x_41 = x_493;
x_42 = x_491;
x_43 = x_496;
goto block_488;
}
else
{
uint8_t x_499; 
x_499 = lean_unbox(x_494);
x_38 = x_492;
x_39 = x_489;
x_40 = x_490;
x_41 = x_493;
x_42 = x_491;
x_43 = x_499;
goto block_488;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_13, x_14);
lean_inc(x_2);
x_16 = l_Lean_Expr_const___override(x_2, x_15);
x_17 = l_Lean_mkAppN(x_16, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_18 = l_Lean_Meta_mkEq(x_17, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_box(0);
lean_inc(x_8);
lean_inc(x_19);
x_22 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_19, x_21, x_8, x_9, x_10, x_11, x_20);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_25 = l_Lean_Meta_Simp_Result_addExtraArgs(x_3, x_6, x_8, x_9, x_10, x_11, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_236; uint8_t x_237; lean_object* x_238; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Expr_appFn_x21(x_19);
x_29 = lean_box(0);
x_30 = lean_box(1);
x_236 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_236, 0, x_28);
lean_ctor_set(x_236, 1, x_29);
x_237 = lean_unbox(x_30);
lean_ctor_set_uint8(x_236, sizeof(void*)*2, x_237);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_238 = l_Lean_Meta_Simp_mkCongr(x_236, x_26, x_8, x_9, x_10, x_11, x_27);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_239 = lean_ctor_get(x_238, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_238, 1);
lean_inc(x_240);
lean_dec(x_238);
x_241 = l_Lean_Expr_mvarId_x21(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_242 = l_Lean_Meta_applySimpResultToTarget(x_241, x_19, x_239, x_8, x_9, x_10, x_11, x_240);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_243; lean_object* x_244; uint8_t x_245; 
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
x_245 = lean_name_eq(x_2, x_5);
if (x_245 == 0)
{
lean_object* x_246; 
lean_dec(x_242);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_246 = l_Lean_Elab_Eqns_deltaLHS(x_243, x_8, x_9, x_10, x_11, x_244);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_31 = x_247;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_248;
goto block_235;
}
else
{
uint8_t x_249; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_249 = !lean_is_exclusive(x_246);
if (x_249 == 0)
{
return x_246;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_246, 0);
x_251 = lean_ctor_get(x_246, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_246);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
lean_dec(x_244);
lean_dec(x_243);
if (lean_obj_tag(x_242) == 0)
{
lean_object* x_253; lean_object* x_254; 
x_253 = lean_ctor_get(x_242, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_242, 1);
lean_inc(x_254);
lean_dec(x_242);
x_31 = x_253;
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_254;
goto block_235;
}
else
{
uint8_t x_255; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_255 = !lean_is_exclusive(x_242);
if (x_255 == 0)
{
lean_ctor_set_tag(x_242, 1);
return x_242;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_242, 0);
x_257 = lean_ctor_get(x_242, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_242);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
else
{
uint8_t x_259; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_259 = !lean_is_exclusive(x_242);
if (x_259 == 0)
{
return x_242;
}
else
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_242, 0);
x_261 = lean_ctor_get(x_242, 1);
lean_inc(x_261);
lean_inc(x_260);
lean_dec(x_242);
x_262 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
return x_262;
}
}
}
else
{
uint8_t x_263; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_263 = !lean_is_exclusive(x_238);
if (x_263 == 0)
{
return x_238;
}
else
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_238, 0);
x_265 = lean_ctor_get(x_238, 1);
lean_inc(x_265);
lean_inc(x_264);
lean_dec(x_238);
x_266 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
return x_266;
}
}
block_235:
{
lean_object* x_37; 
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
x_37 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_rwFixEq(x_31, x_32, x_33, x_34, x_35, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
lean_inc(x_35);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
x_40 = l___private_Lean_Elab_PreDefinition_WF_Unfold_0__Lean_Elab_WF_mkUnfoldProof(x_2, x_38, x_32, x_33, x_34, x_35, x_39);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_42 = lean_ctor_get(x_40, 1);
x_43 = lean_ctor_get(x_40, 0);
lean_dec(x_43);
x_44 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_23, x_33, x_42);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_44, 0);
x_47 = lean_ctor_get(x_44, 1);
x_48 = lean_box(0);
x_49 = lean_box(1);
x_50 = lean_unbox(x_48);
x_51 = lean_unbox(x_30);
x_52 = lean_unbox(x_49);
x_53 = l_Lean_Meta_mkForallFVars(x_6, x_19, x_50, x_51, x_52, x_32, x_33, x_34, x_35, x_47);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; lean_object* x_60; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_unbox(x_48);
x_57 = lean_unbox(x_30);
x_58 = lean_unbox(x_48);
x_59 = lean_unbox(x_49);
x_60 = l_Lean_Meta_mkLambdaFVars(x_6, x_46, x_56, x_57, x_58, x_59, x_32, x_33, x_34, x_35, x_55);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
lean_inc(x_4);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_4);
lean_ctor_set(x_63, 1, x_13);
lean_ctor_set(x_63, 2, x_54);
x_64 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_44, 1);
lean_ctor_set(x_44, 1, x_64);
lean_ctor_set(x_44, 0, x_4);
x_65 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_61);
lean_ctor_set(x_65, 2, x_44);
x_66 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_66, 0, x_65);
lean_inc(x_35);
lean_inc(x_34);
x_67 = l_Lean_addDecl(x_66, x_34, x_35, x_62);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_69 = lean_ctor_get(x_67, 1);
x_70 = lean_ctor_get(x_67, 0);
lean_dec(x_70);
x_71 = lean_mk_string_unchecked("Elab", 4, 4);
x_72 = lean_mk_string_unchecked("definition", 10, 10);
x_73 = lean_mk_string_unchecked("wf", 2, 2);
x_74 = l_Lean_Name_mkStr3(x_71, x_72, x_73);
lean_inc(x_74);
x_75 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_74, x_32, x_33, x_34, x_35, x_69);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_unbox(x_76);
lean_dec(x_76);
if (x_77 == 0)
{
uint8_t x_78; 
lean_dec(x_74);
lean_free_object(x_67);
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
x_78 = !lean_is_exclusive(x_75);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_75, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set(x_75, 0, x_80);
return x_75;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
lean_dec(x_75);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_84 = lean_ctor_get(x_75, 1);
lean_inc(x_84);
lean_dec(x_75);
x_85 = lean_mk_string_unchecked("mkUnfoldEq defined ", 19, 19);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
x_87 = lean_unbox(x_48);
x_88 = l_Lean_MessageData_ofConstName(x_4, x_87);
lean_ctor_set_tag(x_67, 7);
lean_ctor_set(x_67, 1, x_88);
lean_ctor_set(x_67, 0, x_86);
x_89 = lean_mk_string_unchecked("", 0, 0);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_90);
lean_ctor_set(x_40, 0, x_67);
x_91 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_74, x_40, x_32, x_33, x_34, x_35, x_84);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_92 = lean_ctor_get(x_67, 1);
lean_inc(x_92);
lean_dec(x_67);
x_93 = lean_mk_string_unchecked("Elab", 4, 4);
x_94 = lean_mk_string_unchecked("definition", 10, 10);
x_95 = lean_mk_string_unchecked("wf", 2, 2);
x_96 = l_Lean_Name_mkStr3(x_93, x_94, x_95);
lean_inc(x_96);
x_97 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_96, x_32, x_33, x_34, x_35, x_92);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_96);
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_101 = x_97;
} else {
 lean_dec_ref(x_97);
 x_101 = lean_box(0);
}
x_102 = lean_box(0);
if (lean_is_scalar(x_101)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_101;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_100);
return x_103;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_104 = lean_ctor_get(x_97, 1);
lean_inc(x_104);
lean_dec(x_97);
x_105 = lean_mk_string_unchecked("mkUnfoldEq defined ", 19, 19);
x_106 = l_Lean_stringToMessageData(x_105);
lean_dec(x_105);
x_107 = lean_unbox(x_48);
x_108 = l_Lean_MessageData_ofConstName(x_4, x_107);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_110 = lean_mk_string_unchecked("", 0, 0);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_111);
lean_ctor_set(x_40, 0, x_109);
x_112 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_96, x_40, x_32, x_33, x_34, x_35, x_104);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_112;
}
}
}
else
{
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
return x_67;
}
}
else
{
uint8_t x_113; 
lean_dec(x_54);
lean_free_object(x_44);
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_4);
x_113 = !lean_is_exclusive(x_60);
if (x_113 == 0)
{
return x_60;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_60, 0);
x_115 = lean_ctor_get(x_60, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_60);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
uint8_t x_117; 
lean_free_object(x_44);
lean_dec(x_46);
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_4);
x_117 = !lean_is_exclusive(x_53);
if (x_117 == 0)
{
return x_53;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_118 = lean_ctor_get(x_53, 0);
x_119 = lean_ctor_get(x_53, 1);
lean_inc(x_119);
lean_inc(x_118);
lean_dec(x_53);
x_120 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_120, 0, x_118);
lean_ctor_set(x_120, 1, x_119);
return x_120;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; uint8_t x_126; uint8_t x_127; lean_object* x_128; 
x_121 = lean_ctor_get(x_44, 0);
x_122 = lean_ctor_get(x_44, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_44);
x_123 = lean_box(0);
x_124 = lean_box(1);
x_125 = lean_unbox(x_123);
x_126 = lean_unbox(x_30);
x_127 = lean_unbox(x_124);
x_128 = l_Lean_Meta_mkForallFVars(x_6, x_19, x_125, x_126, x_127, x_32, x_33, x_34, x_35, x_122);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; lean_object* x_130; uint8_t x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_unbox(x_123);
x_132 = lean_unbox(x_30);
x_133 = lean_unbox(x_123);
x_134 = lean_unbox(x_124);
x_135 = l_Lean_Meta_mkLambdaFVars(x_6, x_121, x_131, x_132, x_133, x_134, x_32, x_33, x_34, x_35, x_130);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
lean_inc(x_4);
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_4);
lean_ctor_set(x_138, 1, x_13);
lean_ctor_set(x_138, 2, x_129);
x_139 = lean_box(0);
lean_inc(x_4);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_4);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_136);
lean_ctor_set(x_141, 2, x_140);
x_142 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_142, 0, x_141);
lean_inc(x_35);
lean_inc(x_34);
x_143 = l_Lean_addDecl(x_142, x_34, x_35, x_137);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; 
x_144 = lean_ctor_get(x_143, 1);
lean_inc(x_144);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_145 = x_143;
} else {
 lean_dec_ref(x_143);
 x_145 = lean_box(0);
}
x_146 = lean_mk_string_unchecked("Elab", 4, 4);
x_147 = lean_mk_string_unchecked("definition", 10, 10);
x_148 = lean_mk_string_unchecked("wf", 2, 2);
x_149 = l_Lean_Name_mkStr3(x_146, x_147, x_148);
lean_inc(x_149);
x_150 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_149, x_32, x_33, x_34, x_35, x_144);
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_unbox(x_151);
lean_dec(x_151);
if (x_152 == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_dec(x_149);
lean_dec(x_145);
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_154 = x_150;
} else {
 lean_dec_ref(x_150);
 x_154 = lean_box(0);
}
x_155 = lean_box(0);
if (lean_is_scalar(x_154)) {
 x_156 = lean_alloc_ctor(0, 2, 0);
} else {
 x_156 = x_154;
}
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_156, 1, x_153);
return x_156;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; uint8_t x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
x_157 = lean_ctor_get(x_150, 1);
lean_inc(x_157);
lean_dec(x_150);
x_158 = lean_mk_string_unchecked("mkUnfoldEq defined ", 19, 19);
x_159 = l_Lean_stringToMessageData(x_158);
lean_dec(x_158);
x_160 = lean_unbox(x_123);
x_161 = l_Lean_MessageData_ofConstName(x_4, x_160);
if (lean_is_scalar(x_145)) {
 x_162 = lean_alloc_ctor(7, 2, 0);
} else {
 x_162 = x_145;
 lean_ctor_set_tag(x_162, 7);
}
lean_ctor_set(x_162, 0, x_159);
lean_ctor_set(x_162, 1, x_161);
x_163 = lean_mk_string_unchecked("", 0, 0);
x_164 = l_Lean_stringToMessageData(x_163);
lean_dec(x_163);
lean_ctor_set_tag(x_40, 7);
lean_ctor_set(x_40, 1, x_164);
lean_ctor_set(x_40, 0, x_162);
x_165 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_149, x_40, x_32, x_33, x_34, x_35, x_157);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_165;
}
}
else
{
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
return x_143;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_129);
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_4);
x_166 = lean_ctor_get(x_135, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_135, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_168 = x_135;
} else {
 lean_dec_ref(x_135);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_121);
lean_free_object(x_40);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_4);
x_170 = lean_ctor_get(x_128, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_128, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_172 = x_128;
} else {
 lean_dec_ref(x_128);
 x_172 = lean_box(0);
}
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(1, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_170);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
}
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; uint8_t x_181; uint8_t x_182; uint8_t x_183; lean_object* x_184; 
x_174 = lean_ctor_get(x_40, 1);
lean_inc(x_174);
lean_dec(x_40);
x_175 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_23, x_33, x_174);
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_178 = x_175;
} else {
 lean_dec_ref(x_175);
 x_178 = lean_box(0);
}
x_179 = lean_box(0);
x_180 = lean_box(1);
x_181 = lean_unbox(x_179);
x_182 = lean_unbox(x_30);
x_183 = lean_unbox(x_180);
x_184 = l_Lean_Meta_mkForallFVars(x_6, x_19, x_181, x_182, x_183, x_32, x_33, x_34, x_35, x_177);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; uint8_t x_187; uint8_t x_188; uint8_t x_189; uint8_t x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = lean_unbox(x_179);
x_188 = lean_unbox(x_30);
x_189 = lean_unbox(x_179);
x_190 = lean_unbox(x_180);
x_191 = l_Lean_Meta_mkLambdaFVars(x_6, x_176, x_187, x_188, x_189, x_190, x_32, x_33, x_34, x_35, x_186);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
lean_inc(x_4);
x_194 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_194, 0, x_4);
lean_ctor_set(x_194, 1, x_13);
lean_ctor_set(x_194, 2, x_185);
x_195 = lean_box(0);
lean_inc(x_4);
if (lean_is_scalar(x_178)) {
 x_196 = lean_alloc_ctor(1, 2, 0);
} else {
 x_196 = x_178;
 lean_ctor_set_tag(x_196, 1);
}
lean_ctor_set(x_196, 0, x_4);
lean_ctor_set(x_196, 1, x_195);
x_197 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_192);
lean_ctor_set(x_197, 2, x_196);
x_198 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_198, 0, x_197);
lean_inc(x_35);
lean_inc(x_34);
x_199 = l_Lean_addDecl(x_198, x_34, x_35, x_193);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; uint8_t x_208; 
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_201 = x_199;
} else {
 lean_dec_ref(x_199);
 x_201 = lean_box(0);
}
x_202 = lean_mk_string_unchecked("Elab", 4, 4);
x_203 = lean_mk_string_unchecked("definition", 10, 10);
x_204 = lean_mk_string_unchecked("wf", 2, 2);
x_205 = l_Lean_Name_mkStr3(x_202, x_203, x_204);
lean_inc(x_205);
x_206 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_205, x_32, x_33, x_34, x_35, x_200);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_unbox(x_207);
lean_dec(x_207);
if (x_208 == 0)
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_205);
lean_dec(x_201);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
x_209 = lean_ctor_get(x_206, 1);
lean_inc(x_209);
if (lean_is_exclusive(x_206)) {
 lean_ctor_release(x_206, 0);
 lean_ctor_release(x_206, 1);
 x_210 = x_206;
} else {
 lean_dec_ref(x_206);
 x_210 = lean_box(0);
}
x_211 = lean_box(0);
if (lean_is_scalar(x_210)) {
 x_212 = lean_alloc_ctor(0, 2, 0);
} else {
 x_212 = x_210;
}
lean_ctor_set(x_212, 0, x_211);
lean_ctor_set(x_212, 1, x_209);
return x_212;
}
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_213 = lean_ctor_get(x_206, 1);
lean_inc(x_213);
lean_dec(x_206);
x_214 = lean_mk_string_unchecked("mkUnfoldEq defined ", 19, 19);
x_215 = l_Lean_stringToMessageData(x_214);
lean_dec(x_214);
x_216 = lean_unbox(x_179);
x_217 = l_Lean_MessageData_ofConstName(x_4, x_216);
if (lean_is_scalar(x_201)) {
 x_218 = lean_alloc_ctor(7, 2, 0);
} else {
 x_218 = x_201;
 lean_ctor_set_tag(x_218, 7);
}
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
x_219 = lean_mk_string_unchecked("", 0, 0);
x_220 = l_Lean_stringToMessageData(x_219);
lean_dec(x_219);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
x_222 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_205, x_221, x_32, x_33, x_34, x_35, x_213);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
return x_222;
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_4);
return x_199;
}
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_185);
lean_dec(x_178);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_4);
x_223 = lean_ctor_get(x_191, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_191, 1);
lean_inc(x_224);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_225 = x_191;
} else {
 lean_dec_ref(x_191);
 x_225 = lean_box(0);
}
if (lean_is_scalar(x_225)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_225;
}
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_224);
return x_226;
}
}
else
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
lean_dec(x_178);
lean_dec(x_176);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_13);
lean_dec(x_4);
x_227 = lean_ctor_get(x_184, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_184, 1);
lean_inc(x_228);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_229 = x_184;
} else {
 lean_dec_ref(x_184);
 x_229 = lean_box(0);
}
if (lean_is_scalar(x_229)) {
 x_230 = lean_alloc_ctor(1, 2, 0);
} else {
 x_230 = x_229;
}
lean_ctor_set(x_230, 0, x_227);
lean_ctor_set(x_230, 1, x_228);
return x_230;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_4);
return x_40;
}
}
else
{
uint8_t x_231; 
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_2);
x_231 = !lean_is_exclusive(x_37);
if (x_231 == 0)
{
return x_37;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_232 = lean_ctor_get(x_37, 0);
x_233 = lean_ctor_get(x_37, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_37);
x_234 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
return x_234;
}
}
}
}
else
{
uint8_t x_267; 
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
x_267 = !lean_is_exclusive(x_25);
if (x_267 == 0)
{
return x_25;
}
else
{
lean_object* x_268; lean_object* x_269; lean_object* x_270; 
x_268 = lean_ctor_get(x_25, 0);
x_269 = lean_ctor_get(x_25, 1);
lean_inc(x_269);
lean_inc(x_268);
lean_dec(x_25);
x_270 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_270, 0, x_268);
lean_ctor_set(x_270, 1, x_269);
return x_270;
}
}
}
else
{
uint8_t x_271; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_271 = !lean_is_exclusive(x_18);
if (x_271 == 0)
{
return x_18;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_18, 0);
x_273 = lean_ctor_get(x_18, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_18);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_mk_string_unchecked("Cannot derive ", 14, 14);
x_4 = l_Lean_stringToMessageData(x_3);
lean_dec(x_3);
x_5 = l_Lean_MessageData_ofName(x_1);
x_6 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_mk_string_unchecked("", 0, 0);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
lean_inc(x_8);
x_9 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
x_10 = l_Lean_indentD(x_2);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_71; uint8_t x_72; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = l_Lean_Meta_tactic_hygienic;
x_14 = l_Lean_diagnostics;
x_15 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_12, x_13, x_1);
x_16 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_15, x_14);
x_71 = lean_ctor_get(x_10, 0);
lean_inc(x_71);
lean_dec(x_10);
x_72 = l_Lean_Kernel_isDiagnosticsEnabled(x_71);
lean_dec(x_71);
if (x_72 == 0)
{
if (x_16 == 0)
{
x_17 = x_6;
x_18 = x_7;
x_19 = x_11;
goto block_36;
}
else
{
goto block_70;
}
}
else
{
if (x_16 == 0)
{
goto block_70;
}
else
{
x_17 = x_6;
x_18 = x_7;
x_19 = x_11;
goto block_36;
}
}
block_36:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_20 = lean_ctor_get(x_17, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 3);
lean_inc(x_22);
x_23 = l_Lean_maxRecDepth;
x_24 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_15, x_23);
x_25 = lean_ctor_get(x_17, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_17, 7);
lean_inc(x_27);
x_28 = lean_ctor_get(x_17, 8);
lean_inc(x_28);
x_29 = lean_ctor_get(x_17, 9);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 10);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 11);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_17, sizeof(void*)*13 + 1);
x_33 = lean_ctor_get(x_17, 12);
lean_inc(x_33);
lean_dec(x_17);
x_34 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_34, 0, x_20);
lean_ctor_set(x_34, 1, x_21);
lean_ctor_set(x_34, 2, x_15);
lean_ctor_set(x_34, 3, x_22);
lean_ctor_set(x_34, 4, x_24);
lean_ctor_set(x_34, 5, x_25);
lean_ctor_set(x_34, 6, x_26);
lean_ctor_set(x_34, 7, x_27);
lean_ctor_set(x_34, 8, x_28);
lean_ctor_set(x_34, 9, x_29);
lean_ctor_set(x_34, 10, x_30);
lean_ctor_set(x_34, 11, x_31);
lean_ctor_set(x_34, 12, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*13, x_16);
lean_ctor_set_uint8(x_34, sizeof(void*)*13 + 1, x_32);
x_35 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_2, x_3, x_1, x_4, x_5, x_34, x_18, x_19);
return x_35;
}
block_70:
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_st_ref_take(x_7, x_11);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_37, 0);
x_40 = lean_ctor_get(x_37, 1);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = l_Lean_Kernel_enableDiag(x_41, x_16);
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_39, 2);
lean_inc(x_44);
x_45 = lean_ctor_get(x_39, 3);
lean_inc(x_45);
x_46 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_46);
lean_inc(x_47);
lean_ctor_set(x_37, 1, x_47);
lean_ctor_set(x_37, 0, x_47);
x_48 = lean_ctor_get(x_39, 5);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 6);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 7);
lean_inc(x_50);
lean_dec(x_39);
x_51 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_51, 0, x_42);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_37);
lean_ctor_set(x_51, 5, x_48);
lean_ctor_set(x_51, 6, x_49);
lean_ctor_set(x_51, 7, x_50);
x_52 = lean_st_ref_set(x_7, x_51, x_40);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_17 = x_6;
x_18 = x_7;
x_19 = x_53;
goto block_36;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_ctor_get(x_54, 0);
lean_inc(x_56);
x_57 = l_Lean_Kernel_enableDiag(x_56, x_16);
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_54, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_54, 3);
lean_inc(x_60);
x_61 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_61);
lean_inc(x_62);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_ctor_get(x_54, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_54, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_54, 7);
lean_inc(x_66);
lean_dec(x_54);
x_67 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_67, 0, x_57);
lean_ctor_set(x_67, 1, x_58);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_60);
lean_ctor_set(x_67, 4, x_63);
lean_ctor_set(x_67, 5, x_64);
lean_ctor_set(x_67, 6, x_65);
lean_ctor_set(x_67, 7, x_66);
x_68 = lean_st_ref_set(x_7, x_67, x_55);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_17 = x_6;
x_18 = x_7;
x_19 = x_69;
goto block_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
x_10 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_9);
x_11 = l_Lean_Name_str___override(x_9, x_10);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed), 12, 5);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_9);
lean_closure_set(x_12, 2, x_3);
lean_closure_set(x_12, 3, x_11);
lean_closure_set(x_12, 4, x_2);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__1), 2, 1);
lean_closure_set(x_13, 0, x_11);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_12);
x_17 = l_Lean_Meta_mapErrorImp___redArg(x_16, x_13, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_WF_mkUnfoldEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Lean_Elab_WF_mkUnfoldEq___lam__2(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_box(0);
lean_inc(x_12);
x_14 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_12, x_13);
x_15 = l_Lean_Expr_const___override(x_2, x_14);
x_16 = l_Lean_mkAppN(x_15, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_17 = l_Lean_Meta_mkEq(x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_box(0);
lean_inc(x_7);
lean_inc(x_18);
x_21 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_18, x_20, x_7, x_8, x_9, x_10, x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = l_Lean_Expr_mvarId_x21(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_26 = l_Lean_Elab_Eqns_deltaLHS(x_25, x_7, x_8, x_9, x_10, x_24);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_box(0);
x_30 = lean_box(1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 0, 4);
x_33 = lean_unbox(x_29);
lean_ctor_set_uint8(x_32, 0, x_33);
x_34 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, 1, x_34);
x_35 = lean_unbox(x_31);
lean_ctor_set_uint8(x_32, 2, x_35);
x_36 = lean_unbox(x_30);
lean_ctor_set_uint8(x_32, 3, x_36);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_27);
x_37 = l_Lean_MVarId_applyConst(x_27, x_3, x_32, x_7, x_8, x_9, x_10, x_28);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_List_isEmpty___redArg(x_38);
lean_dec(x_38);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_4);
x_41 = lean_mk_string_unchecked("Failed to apply '", 17, 17);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
x_43 = l_Lean_MessageData_ofName(x_3);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_43);
lean_ctor_set(x_21, 0, x_42);
x_44 = lean_mk_string_unchecked("' to '", 6, 6);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_21);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_27);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_mk_string_unchecked("'", 1, 1);
x_50 = l_Lean_stringToMessageData(x_49);
lean_dec(x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_51, x_7, x_8, x_9, x_10, x_39);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_52;
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_27);
lean_dec(x_3);
x_53 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_23, x_8, x_39);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_box(1);
x_58 = lean_unbox(x_31);
x_59 = lean_unbox(x_30);
x_60 = lean_unbox(x_57);
x_61 = l_Lean_Meta_mkForallFVars(x_5, x_18, x_58, x_59, x_60, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; lean_object* x_68; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_unbox(x_31);
x_65 = lean_unbox(x_30);
x_66 = lean_unbox(x_31);
x_67 = lean_unbox(x_57);
x_68 = l_Lean_Meta_mkLambdaFVars(x_5, x_55, x_64, x_65, x_66, x_67, x_7, x_8, x_9, x_10, x_63);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
lean_inc(x_4);
x_71 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_71, 0, x_4);
lean_ctor_set(x_71, 1, x_12);
lean_ctor_set(x_71, 2, x_62);
x_72 = lean_box(0);
lean_inc(x_4);
lean_ctor_set_tag(x_53, 1);
lean_ctor_set(x_53, 1, x_72);
lean_ctor_set(x_53, 0, x_4);
x_73 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_69);
lean_ctor_set(x_73, 2, x_53);
x_74 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_inc(x_10);
lean_inc(x_9);
x_75 = l_Lean_addDecl(x_74, x_9, x_10, x_70);
if (lean_obj_tag(x_75) == 0)
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_ctor_get(x_75, 1);
x_78 = lean_ctor_get(x_75, 0);
lean_dec(x_78);
x_79 = lean_mk_string_unchecked("Elab", 4, 4);
x_80 = lean_mk_string_unchecked("definition", 10, 10);
x_81 = lean_mk_string_unchecked("wf", 2, 2);
x_82 = l_Lean_Name_mkStr3(x_79, x_80, x_81);
lean_inc(x_82);
x_83 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_82, x_7, x_8, x_9, x_10, x_77);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
if (x_85 == 0)
{
uint8_t x_86; 
lean_dec(x_82);
lean_free_object(x_75);
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_83, 0, x_88);
return x_83;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_dec(x_83);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_83, 1);
lean_inc(x_92);
lean_dec(x_83);
x_93 = lean_mk_string_unchecked("mkBinaryUnfoldEq defined ", 25, 25);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_unbox(x_31);
x_96 = l_Lean_MessageData_ofConstName(x_4, x_95);
lean_ctor_set_tag(x_75, 7);
lean_ctor_set(x_75, 1, x_96);
lean_ctor_set(x_75, 0, x_94);
x_97 = lean_mk_string_unchecked("", 0, 0);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_98);
lean_ctor_set(x_21, 0, x_75);
x_99 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_82, x_21, x_7, x_8, x_9, x_10, x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_99;
}
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_100 = lean_ctor_get(x_75, 1);
lean_inc(x_100);
lean_dec(x_75);
x_101 = lean_mk_string_unchecked("Elab", 4, 4);
x_102 = lean_mk_string_unchecked("definition", 10, 10);
x_103 = lean_mk_string_unchecked("wf", 2, 2);
x_104 = l_Lean_Name_mkStr3(x_101, x_102, x_103);
lean_inc(x_104);
x_105 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_104, x_7, x_8, x_9, x_10, x_100);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
lean_dec(x_104);
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
x_110 = lean_box(0);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_112 = lean_ctor_get(x_105, 1);
lean_inc(x_112);
lean_dec(x_105);
x_113 = lean_mk_string_unchecked("mkBinaryUnfoldEq defined ", 25, 25);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = lean_unbox(x_31);
x_116 = l_Lean_MessageData_ofConstName(x_4, x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("", 0, 0);
x_119 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_119);
lean_ctor_set(x_21, 0, x_117);
x_120 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_104, x_21, x_7, x_8, x_9, x_10, x_112);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_120;
}
}
}
else
{
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_75;
}
}
else
{
uint8_t x_121; 
lean_dec(x_62);
lean_free_object(x_53);
lean_free_object(x_21);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_121 = !lean_is_exclusive(x_68);
if (x_121 == 0)
{
return x_68;
}
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_122 = lean_ctor_get(x_68, 0);
x_123 = lean_ctor_get(x_68, 1);
lean_inc(x_123);
lean_inc(x_122);
lean_dec(x_68);
x_124 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_124, 0, x_122);
lean_ctor_set(x_124, 1, x_123);
return x_124;
}
}
}
else
{
uint8_t x_125; 
lean_free_object(x_53);
lean_dec(x_55);
lean_free_object(x_21);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_125 = !lean_is_exclusive(x_61);
if (x_125 == 0)
{
return x_61;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_126 = lean_ctor_get(x_61, 0);
x_127 = lean_ctor_get(x_61, 1);
lean_inc(x_127);
lean_inc(x_126);
lean_dec(x_61);
x_128 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_128, 0, x_126);
lean_ctor_set(x_128, 1, x_127);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; uint8_t x_134; lean_object* x_135; 
x_129 = lean_ctor_get(x_53, 0);
x_130 = lean_ctor_get(x_53, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_53);
x_131 = lean_box(1);
x_132 = lean_unbox(x_31);
x_133 = lean_unbox(x_30);
x_134 = lean_unbox(x_131);
x_135 = l_Lean_Meta_mkForallFVars(x_5, x_18, x_132, x_133, x_134, x_7, x_8, x_9, x_10, x_130);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; uint8_t x_138; uint8_t x_139; uint8_t x_140; uint8_t x_141; lean_object* x_142; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_138 = lean_unbox(x_31);
x_139 = lean_unbox(x_30);
x_140 = lean_unbox(x_31);
x_141 = lean_unbox(x_131);
x_142 = l_Lean_Meta_mkLambdaFVars(x_5, x_129, x_138, x_139, x_140, x_141, x_7, x_8, x_9, x_10, x_137);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_4);
x_145 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_145, 0, x_4);
lean_ctor_set(x_145, 1, x_12);
lean_ctor_set(x_145, 2, x_136);
x_146 = lean_box(0);
lean_inc(x_4);
x_147 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_147, 0, x_4);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_148, 0, x_145);
lean_ctor_set(x_148, 1, x_143);
lean_ctor_set(x_148, 2, x_147);
x_149 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_149, 0, x_148);
lean_inc(x_10);
lean_inc(x_9);
x_150 = l_Lean_addDecl(x_149, x_9, x_10, x_144);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; 
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_150)) {
 lean_ctor_release(x_150, 0);
 lean_ctor_release(x_150, 1);
 x_152 = x_150;
} else {
 lean_dec_ref(x_150);
 x_152 = lean_box(0);
}
x_153 = lean_mk_string_unchecked("Elab", 4, 4);
x_154 = lean_mk_string_unchecked("definition", 10, 10);
x_155 = lean_mk_string_unchecked("wf", 2, 2);
x_156 = l_Lean_Name_mkStr3(x_153, x_154, x_155);
lean_inc(x_156);
x_157 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_156, x_7, x_8, x_9, x_10, x_151);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_unbox(x_158);
lean_dec(x_158);
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_156);
lean_dec(x_152);
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
return x_163;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_164 = lean_ctor_get(x_157, 1);
lean_inc(x_164);
lean_dec(x_157);
x_165 = lean_mk_string_unchecked("mkBinaryUnfoldEq defined ", 25, 25);
x_166 = l_Lean_stringToMessageData(x_165);
lean_dec(x_165);
x_167 = lean_unbox(x_31);
x_168 = l_Lean_MessageData_ofConstName(x_4, x_167);
if (lean_is_scalar(x_152)) {
 x_169 = lean_alloc_ctor(7, 2, 0);
} else {
 x_169 = x_152;
 lean_ctor_set_tag(x_169, 7);
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_mk_string_unchecked("", 0, 0);
x_171 = l_Lean_stringToMessageData(x_170);
lean_dec(x_170);
lean_ctor_set_tag(x_21, 7);
lean_ctor_set(x_21, 1, x_171);
lean_ctor_set(x_21, 0, x_169);
x_172 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_156, x_21, x_7, x_8, x_9, x_10, x_164);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_172;
}
}
else
{
lean_free_object(x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_150;
}
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
lean_dec(x_136);
lean_free_object(x_21);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_173 = lean_ctor_get(x_142, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_142, 1);
lean_inc(x_174);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_175 = x_142;
} else {
 lean_dec_ref(x_142);
 x_175 = lean_box(0);
}
if (lean_is_scalar(x_175)) {
 x_176 = lean_alloc_ctor(1, 2, 0);
} else {
 x_176 = x_175;
}
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
lean_dec(x_129);
lean_free_object(x_21);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_177 = lean_ctor_get(x_135, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_135, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_135)) {
 lean_ctor_release(x_135, 0);
 lean_ctor_release(x_135, 1);
 x_179 = x_135;
} else {
 lean_dec_ref(x_135);
 x_179 = lean_box(0);
}
if (lean_is_scalar(x_179)) {
 x_180 = lean_alloc_ctor(1, 2, 0);
} else {
 x_180 = x_179;
}
lean_ctor_set(x_180, 0, x_177);
lean_ctor_set(x_180, 1, x_178);
return x_180;
}
}
}
}
else
{
uint8_t x_181; 
lean_dec(x_27);
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_181 = !lean_is_exclusive(x_37);
if (x_181 == 0)
{
return x_37;
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_182 = lean_ctor_get(x_37, 0);
x_183 = lean_ctor_get(x_37, 1);
lean_inc(x_183);
lean_inc(x_182);
lean_dec(x_37);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
return x_184;
}
}
}
else
{
uint8_t x_185; 
lean_free_object(x_21);
lean_dec(x_23);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_185 = !lean_is_exclusive(x_26);
if (x_185 == 0)
{
return x_26;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_26, 0);
x_187 = lean_ctor_get(x_26, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_26);
x_188 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_188, 0, x_186);
lean_ctor_set(x_188, 1, x_187);
return x_188;
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_189 = lean_ctor_get(x_21, 0);
x_190 = lean_ctor_get(x_21, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_21);
x_191 = l_Lean_Expr_mvarId_x21(x_189);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_192 = l_Lean_Elab_Eqns_deltaLHS(x_191, x_7, x_8, x_9, x_10, x_190);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; uint8_t x_199; uint8_t x_200; uint8_t x_201; uint8_t x_202; lean_object* x_203; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = lean_box(0);
x_196 = lean_box(1);
x_197 = lean_box(0);
x_198 = lean_alloc_ctor(0, 0, 4);
x_199 = lean_unbox(x_195);
lean_ctor_set_uint8(x_198, 0, x_199);
x_200 = lean_unbox(x_196);
lean_ctor_set_uint8(x_198, 1, x_200);
x_201 = lean_unbox(x_197);
lean_ctor_set_uint8(x_198, 2, x_201);
x_202 = lean_unbox(x_196);
lean_ctor_set_uint8(x_198, 3, x_202);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_3);
lean_inc(x_193);
x_203 = l_Lean_MVarId_applyConst(x_193, x_3, x_198, x_7, x_8, x_9, x_10, x_194);
if (lean_obj_tag(x_203) == 0)
{
lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_204 = lean_ctor_get(x_203, 0);
lean_inc(x_204);
x_205 = lean_ctor_get(x_203, 1);
lean_inc(x_205);
lean_dec(x_203);
x_206 = l_List_isEmpty___redArg(x_204);
lean_dec(x_204);
if (x_206 == 0)
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
lean_dec(x_189);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_4);
x_207 = lean_mk_string_unchecked("Failed to apply '", 17, 17);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
x_209 = l_Lean_MessageData_ofName(x_3);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("' to '", 6, 6);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_214, 0, x_193);
x_215 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_215, 0, x_213);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_mk_string_unchecked("'", 1, 1);
x_217 = l_Lean_stringToMessageData(x_216);
lean_dec(x_216);
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_215);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_218, x_7, x_8, x_9, x_10, x_205);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_219;
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; uint8_t x_226; uint8_t x_227; lean_object* x_228; 
lean_dec(x_193);
lean_dec(x_3);
x_220 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_189, x_8, x_205);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_ctor_get(x_220, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_223 = x_220;
} else {
 lean_dec_ref(x_220);
 x_223 = lean_box(0);
}
x_224 = lean_box(1);
x_225 = lean_unbox(x_197);
x_226 = lean_unbox(x_196);
x_227 = lean_unbox(x_224);
x_228 = l_Lean_Meta_mkForallFVars(x_5, x_18, x_225, x_226, x_227, x_7, x_8, x_9, x_10, x_222);
if (lean_obj_tag(x_228) == 0)
{
lean_object* x_229; lean_object* x_230; uint8_t x_231; uint8_t x_232; uint8_t x_233; uint8_t x_234; lean_object* x_235; 
x_229 = lean_ctor_get(x_228, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_228, 1);
lean_inc(x_230);
lean_dec(x_228);
x_231 = lean_unbox(x_197);
x_232 = lean_unbox(x_196);
x_233 = lean_unbox(x_197);
x_234 = lean_unbox(x_224);
x_235 = l_Lean_Meta_mkLambdaFVars(x_5, x_221, x_231, x_232, x_233, x_234, x_7, x_8, x_9, x_10, x_230);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
lean_inc(x_4);
x_238 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_238, 0, x_4);
lean_ctor_set(x_238, 1, x_12);
lean_ctor_set(x_238, 2, x_229);
x_239 = lean_box(0);
lean_inc(x_4);
if (lean_is_scalar(x_223)) {
 x_240 = lean_alloc_ctor(1, 2, 0);
} else {
 x_240 = x_223;
 lean_ctor_set_tag(x_240, 1);
}
lean_ctor_set(x_240, 0, x_4);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_241, 0, x_238);
lean_ctor_set(x_241, 1, x_236);
lean_ctor_set(x_241, 2, x_240);
x_242 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_242, 0, x_241);
lean_inc(x_10);
lean_inc(x_9);
x_243 = l_Lean_addDecl(x_242, x_9, x_10, x_237);
if (lean_obj_tag(x_243) == 0)
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; 
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_243)) {
 lean_ctor_release(x_243, 0);
 lean_ctor_release(x_243, 1);
 x_245 = x_243;
} else {
 lean_dec_ref(x_243);
 x_245 = lean_box(0);
}
x_246 = lean_mk_string_unchecked("Elab", 4, 4);
x_247 = lean_mk_string_unchecked("definition", 10, 10);
x_248 = lean_mk_string_unchecked("wf", 2, 2);
x_249 = l_Lean_Name_mkStr3(x_246, x_247, x_248);
lean_inc(x_249);
x_250 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_249, x_7, x_8, x_9, x_10, x_244);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_unbox(x_251);
lean_dec(x_251);
if (x_252 == 0)
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; 
lean_dec(x_249);
lean_dec(x_245);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_254 = x_250;
} else {
 lean_dec_ref(x_250);
 x_254 = lean_box(0);
}
x_255 = lean_box(0);
if (lean_is_scalar(x_254)) {
 x_256 = lean_alloc_ctor(0, 2, 0);
} else {
 x_256 = x_254;
}
lean_ctor_set(x_256, 0, x_255);
lean_ctor_set(x_256, 1, x_253);
return x_256;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_257 = lean_ctor_get(x_250, 1);
lean_inc(x_257);
lean_dec(x_250);
x_258 = lean_mk_string_unchecked("mkBinaryUnfoldEq defined ", 25, 25);
x_259 = l_Lean_stringToMessageData(x_258);
lean_dec(x_258);
x_260 = lean_unbox(x_197);
x_261 = l_Lean_MessageData_ofConstName(x_4, x_260);
if (lean_is_scalar(x_245)) {
 x_262 = lean_alloc_ctor(7, 2, 0);
} else {
 x_262 = x_245;
 lean_ctor_set_tag(x_262, 7);
}
lean_ctor_set(x_262, 0, x_259);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_mk_string_unchecked("", 0, 0);
x_264 = l_Lean_stringToMessageData(x_263);
lean_dec(x_263);
x_265 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_265, 0, x_262);
lean_ctor_set(x_265, 1, x_264);
x_266 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_249, x_265, x_7, x_8, x_9, x_10, x_257);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_266;
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
return x_243;
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_dec(x_229);
lean_dec(x_223);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_267 = lean_ctor_get(x_235, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_235, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_235)) {
 lean_ctor_release(x_235, 0);
 lean_ctor_release(x_235, 1);
 x_269 = x_235;
} else {
 lean_dec_ref(x_235);
 x_269 = lean_box(0);
}
if (lean_is_scalar(x_269)) {
 x_270 = lean_alloc_ctor(1, 2, 0);
} else {
 x_270 = x_269;
}
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_268);
return x_270;
}
}
else
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_223);
lean_dec(x_221);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_271 = lean_ctor_get(x_228, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_228, 1);
lean_inc(x_272);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_273 = x_228;
} else {
 lean_dec_ref(x_228);
 x_273 = lean_box(0);
}
if (lean_is_scalar(x_273)) {
 x_274 = lean_alloc_ctor(1, 2, 0);
} else {
 x_274 = x_273;
}
lean_ctor_set(x_274, 0, x_271);
lean_ctor_set(x_274, 1, x_272);
return x_274;
}
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_193);
lean_dec(x_189);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_275 = lean_ctor_get(x_203, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_203, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_203)) {
 lean_ctor_release(x_203, 0);
 lean_ctor_release(x_203, 1);
 x_277 = x_203;
} else {
 lean_dec_ref(x_203);
 x_277 = lean_box(0);
}
if (lean_is_scalar(x_277)) {
 x_278 = lean_alloc_ctor(1, 2, 0);
} else {
 x_278 = x_277;
}
lean_ctor_set(x_278, 0, x_275);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_189);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_279 = lean_ctor_get(x_192, 0);
lean_inc(x_279);
x_280 = lean_ctor_get(x_192, 1);
lean_inc(x_280);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_281 = x_192;
} else {
 lean_dec_ref(x_192);
 x_281 = lean_box(0);
}
if (lean_is_scalar(x_281)) {
 x_282 = lean_alloc_ctor(1, 2, 0);
} else {
 x_282 = x_281;
}
lean_ctor_set(x_282, 0, x_279);
lean_ctor_set(x_282, 1, x_280);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_283 = !lean_is_exclusive(x_17);
if (x_283 == 0)
{
return x_17;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_17, 0);
x_285 = lean_ctor_get(x_17, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_17);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_4 = lean_mk_string_unchecked("Cannot derive ", 14, 14);
x_5 = l_Lean_stringToMessageData(x_4);
lean_dec(x_4);
x_6 = l_Lean_MessageData_ofName(x_1);
x_7 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_mk_string_unchecked(" from ", 6, 6);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_7);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_MessageData_ofName(x_2);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_mk_string_unchecked("", 0, 0);
x_14 = l_Lean_stringToMessageData(x_13);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = l_Lean_indentD(x_3);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_14);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_9);
lean_inc(x_8);
x_10 = l_Lean_Name_str___override(x_8, x_9);
x_11 = l_Lean_Name_str___override(x_2, x_9);
lean_inc(x_10);
lean_inc(x_11);
lean_inc(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed), 11, 4);
lean_closure_set(x_12, 0, x_1);
lean_closure_set(x_12, 1, x_8);
lean_closure_set(x_12, 2, x_11);
lean_closure_set(x_12, 3, x_10);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__1), 3, 2);
lean_closure_set(x_13, 0, x_10);
lean_closure_set(x_13, 1, x_11);
x_14 = lean_ctor_get(x_1, 5);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_box(0);
x_16 = lean_alloc_closure((void*)(l_Lean_Elab_WF_mkUnfoldEq___lam__2___boxed), 8, 3);
lean_closure_set(x_16, 0, x_15);
lean_closure_set(x_16, 1, x_14);
lean_closure_set(x_16, 2, x_12);
x_17 = l_Lean_Meta_mapErrorImp___redArg(x_16, x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_17);
if (x_22 == 0)
{
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 0);
x_24 = lean_ctor_get(x_17, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_WF_mkBinaryUnfoldEq___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2463_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_2 = lean_mk_string_unchecked("Elab", 4, 4);
x_3 = lean_mk_string_unchecked("definition", 10, 10);
x_4 = lean_mk_string_unchecked("wf", 2, 2);
x_5 = lean_mk_string_unchecked("eqns", 4, 4);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_9);
x_10 = l_Lean_Name_str___override(x_8, x_9);
lean_inc(x_2);
x_11 = l_Lean_Name_str___override(x_10, x_2);
x_12 = lean_mk_string_unchecked("WF", 2, 2);
lean_inc(x_12);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("initFn", 6, 6);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = lean_mk_string_unchecked("_@", 2, 2);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = l_Lean_Name_str___override(x_17, x_9);
x_19 = l_Lean_Name_str___override(x_18, x_2);
x_20 = lean_mk_string_unchecked("PreDefinition", 13, 13);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = l_Lean_Name_str___override(x_21, x_12);
x_23 = lean_mk_string_unchecked("Unfold", 6, 6);
x_24 = l_Lean_Name_str___override(x_22, x_23);
x_25 = lean_mk_string_unchecked("_hyg", 4, 4);
x_26 = l_Lean_Name_str___override(x_24, x_25);
x_27 = lean_unsigned_to_nat(2463u);
x_28 = l_Lean_Name_num___override(x_26, x_27);
x_29 = lean_unbox(x_7);
x_30 = l_Lean_registerTraceClass(x_6, x_29, x_28, x_1);
return x_30;
}
}
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_WF_Unfold(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Elab_WF_initFn____x40_Lean_Elab_PreDefinition_WF_Unfold___hyg_2463_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
