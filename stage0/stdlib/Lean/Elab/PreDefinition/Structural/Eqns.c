// Lean compiler output
// Module: Lean.Elab.PreDefinition.Structural.Eqns
// Imports: Lean.Meta.Eqns Lean.Meta.Tactic.Split Lean.Meta.Tactic.Simp.Main Lean.Meta.Tactic.Apply Lean.Elab.PreDefinition.Basic Lean.Elab.PreDefinition.Eqns Lean.Elab.PreDefinition.FixedParams Lean.Elab.PreDefinition.Structural.Basic
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
lean_object* l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282_(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpMatch_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_instInhabitedEqnInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_tactic_hygienic;
lean_object* l_Lean_Meta_registerGetUnfoldEqnFn(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryContradiction(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_maxRecDepth;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Kernel_enableDiag(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Kernel_isDiagnosticsEnabled(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_eqnInfoExt;
size_t lean_usize_of_nat(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_mkUnfoldProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaRHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_mkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1773_(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_diagnostics;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_simpIf_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_mkEqnTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_splitTarget_x3f(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_Meta_realizeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_registerGetEqnsFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
lean_object* l_Lean_Meta_ensureEqnReservedNamesAvailable(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Meta_casesOnStuckLHS_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_simpTargetStar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_tryURefl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282_(lean_object*);
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getUnfoldFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Elab_Eqns_deltaLHS(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addDecl(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns_doRealize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Structural_instInhabitedEqnInfo() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_box(0);
x_6 = l_Lean_Expr_const___override(x_4, x_5);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_2);
lean_ctor_set(x_7, 2, x_6);
lean_ctor_set(x_7, 3, x_6);
x_8 = lean_box(0);
x_9 = l_Array_empty(lean_box(0));
lean_inc_n(x_9, 2);
x_10 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
lean_ctor_set(x_10, 2, x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_8);
lean_ctor_set(x_11, 2, x_9);
lean_ctor_set(x_11, 3, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forM___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
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
x_12 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_10, x_3, x_4, x_5, x_6, x_7);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_13 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_1, x_12, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; 
x_294 = lean_mk_string_unchecked("Elab", 4, 4);
x_295 = lean_mk_string_unchecked("definition", 10, 10);
x_296 = lean_mk_string_unchecked("structural", 10, 10);
x_297 = lean_mk_string_unchecked("eqns", 4, 4);
x_298 = l_Lean_Name_mkStr4(x_294, x_295, x_296, x_297);
lean_inc(x_298);
x_299 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_298, x_3, x_4, x_5, x_6, x_7);
x_300 = lean_ctor_get(x_299, 0);
lean_inc(x_300);
x_301 = lean_unbox(x_300);
lean_dec(x_300);
if (x_301 == 0)
{
lean_object* x_302; 
lean_dec(x_298);
x_302 = lean_ctor_get(x_299, 1);
lean_inc(x_302);
lean_dec(x_299);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_302;
goto block_293;
}
else
{
uint8_t x_303; 
x_303 = !lean_is_exclusive(x_299);
if (x_303 == 0)
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_304 = lean_ctor_get(x_299, 1);
x_305 = lean_ctor_get(x_299, 0);
lean_dec(x_305);
x_306 = lean_mk_string_unchecked("step\n", 5, 5);
x_307 = l_Lean_stringToMessageData(x_306);
lean_dec(x_306);
lean_inc(x_2);
x_308 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_308, 0, x_2);
lean_ctor_set_tag(x_299, 7);
lean_ctor_set(x_299, 1, x_308);
lean_ctor_set(x_299, 0, x_307);
x_309 = lean_mk_string_unchecked("", 0, 0);
x_310 = l_Lean_stringToMessageData(x_309);
lean_dec(x_309);
x_311 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_311, 0, x_299);
lean_ctor_set(x_311, 1, x_310);
x_312 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_298, x_311, x_3, x_4, x_5, x_6, x_304);
x_313 = lean_ctor_get(x_312, 1);
lean_inc(x_313);
lean_dec(x_312);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_313;
goto block_293;
}
else
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_314 = lean_ctor_get(x_299, 1);
lean_inc(x_314);
lean_dec(x_299);
x_315 = lean_mk_string_unchecked("step\n", 5, 5);
x_316 = l_Lean_stringToMessageData(x_315);
lean_dec(x_315);
lean_inc(x_2);
x_317 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_317, 0, x_2);
x_318 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
x_319 = lean_mk_string_unchecked("", 0, 0);
x_320 = l_Lean_stringToMessageData(x_319);
lean_dec(x_319);
x_321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_321, 0, x_318);
lean_ctor_set(x_321, 1, x_320);
x_322 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_298, x_321, x_3, x_4, x_5, x_6, x_314);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
lean_dec(x_322);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_323;
goto block_293;
}
}
block_293:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_13 = l_Lean_Elab_Eqns_tryURefl(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_17 = l_Lean_Elab_Eqns_tryContradiction(x_2, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_21 = l_Lean_Elab_Eqns_whnfReducibleLHS_x3f(x_2, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_24 = l_Lean_Elab_Eqns_simpMatch_x3f(x_2, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_27 = l_Lean_Elab_Eqns_simpIf_x3f(x_2, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; uint8_t x_48; uint8_t x_49; uint8_t x_50; uint8_t x_51; uint8_t x_52; uint8_t x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; uint8_t x_70; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(1);
x_31 = lean_unsigned_to_nat(100000u);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 20);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
x_35 = lean_unbox(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2, x_35);
x_36 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 1, x_36);
x_37 = lean_unbox(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 2, x_37);
x_38 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 3, x_38);
x_39 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 4, x_39);
x_40 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 5, x_40);
x_41 = lean_unbox(x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 6, x_41);
x_42 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 7, x_42);
x_43 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 8, x_43);
x_44 = lean_unbox(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 9, x_44);
x_45 = lean_unbox(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 10, x_45);
x_46 = lean_unbox(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 11, x_46);
x_47 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 12, x_47);
x_48 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 13, x_48);
x_49 = lean_unbox(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 14, x_49);
x_50 = lean_unbox(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 15, x_50);
x_51 = lean_unbox(x_18);
lean_dec(x_18);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 16, x_51);
x_52 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 17, x_52);
x_53 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 18, x_53);
x_54 = lean_unbox(x_30);
lean_ctor_set_uint8(x_34, sizeof(void*)*2 + 19, x_54);
x_55 = l_Array_empty(lean_box(0));
x_56 = lean_unsigned_to_nat(8u);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_nat_shiftl(x_56, x_32);
x_59 = lean_unsigned_to_nat(3u);
x_60 = lean_nat_div(x_58, x_59);
lean_dec(x_58);
x_61 = l_Nat_nextPowerOfTwo(x_60);
lean_dec(x_60);
x_62 = lean_box(0);
x_63 = lean_mk_array(x_61, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
x_65 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_65);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_unbox(x_30);
lean_ctor_set_uint8(x_67, sizeof(void*)*2, x_68);
lean_inc(x_55);
x_69 = l_Lean_Meta_Simp_mkContext(x_34, x_55, x_67, x_8, x_9, x_10, x_11, x_29);
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; size_t x_77; lean_object* x_78; lean_object* x_79; size_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_71 = lean_ctor_get(x_69, 0);
x_72 = lean_ctor_get(x_69, 1);
x_73 = lean_box(0);
lean_inc(x_65);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_65);
lean_inc(x_74);
lean_ctor_set(x_69, 1, x_57);
lean_ctor_set(x_69, 0, x_74);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_65);
x_76 = lean_unsigned_to_nat(5u);
x_77 = lean_usize_of_nat(x_76);
x_78 = lean_usize_to_nat(x_77);
x_79 = lean_nat_pow(x_32, x_78);
lean_dec(x_78);
x_80 = lean_usize_of_nat(x_79);
lean_dec(x_79);
x_81 = lean_usize_to_nat(x_80);
x_82 = lean_mk_empty_array_with_capacity(x_81);
lean_dec(x_81);
lean_inc(x_82);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
lean_ctor_set(x_84, 2, x_57);
lean_ctor_set(x_84, 3, x_57);
lean_ctor_set_usize(x_84, 4, x_77);
lean_inc(x_74);
x_85 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_85, 0, x_74);
lean_ctor_set(x_85, 1, x_74);
lean_ctor_set(x_85, 2, x_75);
lean_ctor_set(x_85, 3, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_69);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_87 = l_Lean_Meta_simpTargetStar(x_2, x_71, x_55, x_73, x_86, x_8, x_9, x_10, x_11, x_72);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
lean_dec(x_88);
switch (lean_obj_tag(x_89)) {
case 0:
{
uint8_t x_90; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_90 = !lean_is_exclusive(x_87);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_ctor_get(x_87, 0);
lean_dec(x_91);
x_92 = lean_box(0);
lean_ctor_set(x_87, 0, x_92);
return x_87;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_87, 1);
lean_inc(x_93);
lean_dec(x_87);
x_94 = lean_box(0);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
case 1:
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_87, 1);
lean_inc(x_96);
lean_dec(x_87);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_2);
x_97 = l_Lean_Elab_Eqns_deltaRHS_x3f(x_2, x_1, x_8, x_9, x_10, x_11, x_96);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
lean_dec(x_97);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_100 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_8, x_9, x_10, x_11, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; uint8_t x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_unbox(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_104 = l_Lean_Meta_splitTarget_x3f(x_2, x_103, x_8, x_9, x_10, x_11, x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = l_Lean_MessageData_ofName(x_1);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_mk_string_unchecked("'\n", 2, 2);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
x_113 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_2);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("", 0, 0);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_118, x_8, x_9, x_10, x_11, x_106);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_2);
x_120 = lean_ctor_get(x_104, 1);
lean_inc(x_120);
lean_dec(x_104);
x_121 = lean_ctor_get(x_105, 0);
lean_inc(x_121);
lean_dec(x_105);
x_122 = l_List_forM___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(x_1, x_121, x_8, x_9, x_10, x_11, x_120);
return x_122;
}
}
else
{
uint8_t x_123; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_123 = !lean_is_exclusive(x_104);
if (x_123 == 0)
{
return x_104;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_104, 0);
x_125 = lean_ctor_get(x_104, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_104);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
uint8_t x_127; 
lean_dec(x_2);
x_127 = !lean_is_exclusive(x_100);
if (x_127 == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_128 = lean_ctor_get(x_100, 1);
x_129 = lean_ctor_get(x_100, 0);
lean_dec(x_129);
x_130 = lean_ctor_get(x_101, 0);
lean_inc(x_130);
lean_dec(x_101);
x_131 = lean_array_get_size(x_130);
x_132 = lean_box(0);
x_133 = lean_nat_dec_lt(x_57, x_131);
if (x_133 == 0)
{
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_100, 0, x_132);
return x_100;
}
else
{
uint8_t x_134; 
x_134 = lean_nat_dec_le(x_131, x_131);
if (x_134 == 0)
{
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
lean_ctor_set(x_100, 0, x_132);
return x_100;
}
else
{
size_t x_135; size_t x_136; lean_object* x_137; 
lean_free_object(x_100);
x_135 = lean_usize_of_nat(x_57);
x_136 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_137 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_1, x_130, x_135, x_136, x_132, x_8, x_9, x_10, x_11, x_128);
lean_dec(x_130);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_138 = lean_ctor_get(x_100, 1);
lean_inc(x_138);
lean_dec(x_100);
x_139 = lean_ctor_get(x_101, 0);
lean_inc(x_139);
lean_dec(x_101);
x_140 = lean_array_get_size(x_139);
x_141 = lean_box(0);
x_142 = lean_nat_dec_lt(x_57, x_140);
if (x_142 == 0)
{
lean_object* x_143; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_138);
return x_143;
}
else
{
uint8_t x_144; 
x_144 = lean_nat_dec_le(x_140, x_140);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_140);
lean_dec(x_139);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_141);
lean_ctor_set(x_145, 1, x_138);
return x_145;
}
else
{
size_t x_146; size_t x_147; lean_object* x_148; 
x_146 = lean_usize_of_nat(x_57);
x_147 = lean_usize_of_nat(x_140);
lean_dec(x_140);
x_148 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_1, x_139, x_146, x_147, x_141, x_8, x_9, x_10, x_11, x_138);
lean_dec(x_139);
return x_148;
}
}
}
}
}
else
{
uint8_t x_149; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_149 = !lean_is_exclusive(x_100);
if (x_149 == 0)
{
return x_100;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_100, 0);
x_151 = lean_ctor_get(x_100, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_100);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
lean_object* x_153; lean_object* x_154; 
lean_dec(x_2);
x_153 = lean_ctor_get(x_97, 1);
lean_inc(x_153);
lean_dec(x_97);
x_154 = lean_ctor_get(x_98, 0);
lean_inc(x_154);
lean_dec(x_98);
x_2 = x_154;
x_3 = x_8;
x_4 = x_9;
x_5 = x_10;
x_6 = x_11;
x_7 = x_153;
goto _start;
}
}
else
{
uint8_t x_156; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_156 = !lean_is_exclusive(x_97);
if (x_156 == 0)
{
return x_97;
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_97, 0);
x_158 = lean_ctor_get(x_97, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_97);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
return x_159;
}
}
}
default: 
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_2);
x_160 = lean_ctor_get(x_87, 1);
lean_inc(x_160);
lean_dec(x_87);
x_161 = lean_ctor_get(x_89, 0);
lean_inc(x_161);
lean_dec(x_89);
x_2 = x_161;
x_3 = x_8;
x_4 = x_9;
x_5 = x_10;
x_6 = x_11;
x_7 = x_160;
goto _start;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_87);
if (x_163 == 0)
{
return x_87;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_87, 0);
x_165 = lean_ctor_get(x_87, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_87);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; size_t x_174; lean_object* x_175; lean_object* x_176; size_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_167 = lean_ctor_get(x_69, 0);
x_168 = lean_ctor_get(x_69, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_69);
x_169 = lean_box(0);
lean_inc(x_65);
x_170 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_170, 0, x_65);
lean_inc(x_170);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_57);
x_172 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_172, 0, x_65);
x_173 = lean_unsigned_to_nat(5u);
x_174 = lean_usize_of_nat(x_173);
x_175 = lean_usize_to_nat(x_174);
x_176 = lean_nat_pow(x_32, x_175);
lean_dec(x_175);
x_177 = lean_usize_of_nat(x_176);
lean_dec(x_176);
x_178 = lean_usize_to_nat(x_177);
x_179 = lean_mk_empty_array_with_capacity(x_178);
lean_dec(x_178);
lean_inc(x_179);
x_180 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_179);
lean_ctor_set(x_181, 2, x_57);
lean_ctor_set(x_181, 3, x_57);
lean_ctor_set_usize(x_181, 4, x_174);
lean_inc(x_170);
x_182 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_182, 0, x_170);
lean_ctor_set(x_182, 1, x_170);
lean_ctor_set(x_182, 2, x_172);
lean_ctor_set(x_182, 3, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_171);
lean_ctor_set(x_183, 1, x_182);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_184 = l_Lean_Meta_simpTargetStar(x_2, x_167, x_55, x_169, x_183, x_8, x_9, x_10, x_11, x_168);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
lean_dec(x_185);
switch (lean_obj_tag(x_186)) {
case 0:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_187 = lean_ctor_get(x_184, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_188 = x_184;
} else {
 lean_dec_ref(x_184);
 x_188 = lean_box(0);
}
x_189 = lean_box(0);
if (lean_is_scalar(x_188)) {
 x_190 = lean_alloc_ctor(0, 2, 0);
} else {
 x_190 = x_188;
}
lean_ctor_set(x_190, 0, x_189);
lean_ctor_set(x_190, 1, x_187);
return x_190;
}
case 1:
{
lean_object* x_191; lean_object* x_192; 
x_191 = lean_ctor_get(x_184, 1);
lean_inc(x_191);
lean_dec(x_184);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_1);
lean_inc(x_2);
x_192 = l_Lean_Elab_Eqns_deltaRHS_x3f(x_2, x_1, x_8, x_9, x_10, x_11, x_191);
if (lean_obj_tag(x_192) == 0)
{
lean_object* x_193; 
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; 
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_195 = l_Lean_Meta_casesOnStuckLHS_x3f(x_2, x_8, x_9, x_10, x_11, x_194);
if (lean_obj_tag(x_195) == 0)
{
lean_object* x_196; 
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; uint8_t x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
lean_dec(x_195);
x_198 = lean_unbox(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
x_199 = l_Lean_Meta_splitTarget_x3f(x_2, x_198, x_8, x_9, x_10, x_11, x_197);
if (lean_obj_tag(x_199) == 0)
{
lean_object* x_200; 
x_200 = lean_ctor_get(x_199, 0);
lean_inc(x_200);
if (lean_obj_tag(x_200) == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_201 = lean_ctor_get(x_199, 1);
lean_inc(x_201);
lean_dec(x_199);
x_202 = lean_mk_string_unchecked("failed to generate equational theorem for '", 43, 43);
x_203 = l_Lean_stringToMessageData(x_202);
lean_dec(x_202);
x_204 = l_Lean_MessageData_ofName(x_1);
x_205 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_205, 0, x_203);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_mk_string_unchecked("'\n", 2, 2);
x_207 = l_Lean_stringToMessageData(x_206);
lean_dec(x_206);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_207);
x_209 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_209, 0, x_2);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("", 0, 0);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_213, x_8, x_9, x_10, x_11, x_201);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_214;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_dec(x_2);
x_215 = lean_ctor_get(x_199, 1);
lean_inc(x_215);
lean_dec(x_199);
x_216 = lean_ctor_get(x_200, 0);
lean_inc(x_216);
lean_dec(x_200);
x_217 = l_List_forM___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__0(x_1, x_216, x_8, x_9, x_10, x_11, x_215);
return x_217;
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_218 = lean_ctor_get(x_199, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_199, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_199)) {
 lean_ctor_release(x_199, 0);
 lean_ctor_release(x_199, 1);
 x_220 = x_199;
} else {
 lean_dec_ref(x_199);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(1, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
lean_dec(x_2);
x_222 = lean_ctor_get(x_195, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_223 = x_195;
} else {
 lean_dec_ref(x_195);
 x_223 = lean_box(0);
}
x_224 = lean_ctor_get(x_196, 0);
lean_inc(x_224);
lean_dec(x_196);
x_225 = lean_array_get_size(x_224);
x_226 = lean_box(0);
x_227 = lean_nat_dec_lt(x_57, x_225);
if (x_227 == 0)
{
lean_object* x_228; 
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_223)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_223;
}
lean_ctor_set(x_228, 0, x_226);
lean_ctor_set(x_228, 1, x_222);
return x_228;
}
else
{
uint8_t x_229; 
x_229 = lean_nat_dec_le(x_225, x_225);
if (x_229 == 0)
{
lean_object* x_230; 
lean_dec(x_225);
lean_dec(x_224);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
if (lean_is_scalar(x_223)) {
 x_230 = lean_alloc_ctor(0, 2, 0);
} else {
 x_230 = x_223;
}
lean_ctor_set(x_230, 0, x_226);
lean_ctor_set(x_230, 1, x_222);
return x_230;
}
else
{
size_t x_231; size_t x_232; lean_object* x_233; 
lean_dec(x_223);
x_231 = lean_usize_of_nat(x_57);
x_232 = lean_usize_of_nat(x_225);
lean_dec(x_225);
x_233 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_1, x_224, x_231, x_232, x_226, x_8, x_9, x_10, x_11, x_222);
lean_dec(x_224);
return x_233;
}
}
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_234 = lean_ctor_get(x_195, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_195, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_236 = x_195;
} else {
 lean_dec_ref(x_195);
 x_236 = lean_box(0);
}
if (lean_is_scalar(x_236)) {
 x_237 = lean_alloc_ctor(1, 2, 0);
} else {
 x_237 = x_236;
}
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_235);
return x_237;
}
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_2);
x_238 = lean_ctor_get(x_192, 1);
lean_inc(x_238);
lean_dec(x_192);
x_239 = lean_ctor_get(x_193, 0);
lean_inc(x_239);
lean_dec(x_193);
x_2 = x_239;
x_3 = x_8;
x_4 = x_9;
x_5 = x_10;
x_6 = x_11;
x_7 = x_238;
goto _start;
}
}
else
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_241 = lean_ctor_get(x_192, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_192, 1);
lean_inc(x_242);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_243 = x_192;
} else {
 lean_dec_ref(x_192);
 x_243 = lean_box(0);
}
if (lean_is_scalar(x_243)) {
 x_244 = lean_alloc_ctor(1, 2, 0);
} else {
 x_244 = x_243;
}
lean_ctor_set(x_244, 0, x_241);
lean_ctor_set(x_244, 1, x_242);
return x_244;
}
}
default: 
{
lean_object* x_245; lean_object* x_246; 
lean_dec(x_2);
x_245 = lean_ctor_get(x_184, 1);
lean_inc(x_245);
lean_dec(x_184);
x_246 = lean_ctor_get(x_186, 0);
lean_inc(x_246);
lean_dec(x_186);
x_2 = x_246;
x_3 = x_8;
x_4 = x_9;
x_5 = x_10;
x_6 = x_11;
x_7 = x_245;
goto _start;
}
}
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_ctor_get(x_184, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_184, 1);
lean_inc(x_249);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_250 = x_184;
} else {
 lean_dec_ref(x_184);
 x_250 = lean_box(0);
}
if (lean_is_scalar(x_250)) {
 x_251 = lean_alloc_ctor(1, 2, 0);
} else {
 x_251 = x_250;
}
lean_ctor_set(x_251, 0, x_248);
lean_ctor_set(x_251, 1, x_249);
return x_251;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; 
lean_dec(x_18);
lean_dec(x_2);
x_252 = lean_ctor_get(x_27, 1);
lean_inc(x_252);
lean_dec(x_27);
x_253 = lean_ctor_get(x_28, 0);
lean_inc(x_253);
lean_dec(x_28);
x_2 = x_253;
x_3 = x_8;
x_4 = x_9;
x_5 = x_10;
x_6 = x_11;
x_7 = x_252;
goto _start;
}
}
else
{
uint8_t x_255; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_255 = !lean_is_exclusive(x_27);
if (x_255 == 0)
{
return x_27;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_27, 0);
x_257 = lean_ctor_get(x_27, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_27);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
else
{
lean_object* x_259; lean_object* x_260; 
lean_dec(x_18);
lean_dec(x_2);
x_259 = lean_ctor_get(x_24, 1);
lean_inc(x_259);
lean_dec(x_24);
x_260 = lean_ctor_get(x_25, 0);
lean_inc(x_260);
lean_dec(x_25);
x_2 = x_260;
x_3 = x_8;
x_4 = x_9;
x_5 = x_10;
x_6 = x_11;
x_7 = x_259;
goto _start;
}
}
else
{
uint8_t x_262; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_262 = !lean_is_exclusive(x_24);
if (x_262 == 0)
{
return x_24;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; 
x_263 = lean_ctor_get(x_24, 0);
x_264 = lean_ctor_get(x_24, 1);
lean_inc(x_264);
lean_inc(x_263);
lean_dec(x_24);
x_265 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_265, 0, x_263);
lean_ctor_set(x_265, 1, x_264);
return x_265;
}
}
}
else
{
lean_object* x_266; lean_object* x_267; 
lean_dec(x_18);
lean_dec(x_2);
x_266 = lean_ctor_get(x_21, 1);
lean_inc(x_266);
lean_dec(x_21);
x_267 = lean_ctor_get(x_22, 0);
lean_inc(x_267);
lean_dec(x_22);
x_2 = x_267;
x_3 = x_8;
x_4 = x_9;
x_5 = x_10;
x_6 = x_11;
x_7 = x_266;
goto _start;
}
}
else
{
uint8_t x_269; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_269 = !lean_is_exclusive(x_21);
if (x_269 == 0)
{
return x_21;
}
else
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_270 = lean_ctor_get(x_21, 0);
x_271 = lean_ctor_get(x_21, 1);
lean_inc(x_271);
lean_inc(x_270);
lean_dec(x_21);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
return x_272;
}
}
}
else
{
uint8_t x_273; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_273 = !lean_is_exclusive(x_17);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; 
x_274 = lean_ctor_get(x_17, 0);
lean_dec(x_274);
x_275 = lean_box(0);
lean_ctor_set(x_17, 0, x_275);
return x_17;
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_276 = lean_ctor_get(x_17, 1);
lean_inc(x_276);
lean_dec(x_17);
x_277 = lean_box(0);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_276);
return x_278;
}
}
}
else
{
uint8_t x_279; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_279 = !lean_is_exclusive(x_17);
if (x_279 == 0)
{
return x_17;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_17, 0);
x_281 = lean_ctor_get(x_17, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_17);
x_282 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_282, 0, x_280);
lean_ctor_set(x_282, 1, x_281);
return x_282;
}
}
}
else
{
uint8_t x_283; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_283 = !lean_is_exclusive(x_13);
if (x_283 == 0)
{
lean_object* x_284; lean_object* x_285; 
x_284 = lean_ctor_get(x_13, 0);
lean_dec(x_284);
x_285 = lean_box(0);
lean_ctor_set(x_13, 0, x_285);
return x_13;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_13, 1);
lean_inc(x_286);
lean_dec(x_13);
x_287 = lean_box(0);
x_288 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_288, 0, x_287);
lean_ctor_set(x_288, 1, x_286);
return x_288;
}
}
}
else
{
uint8_t x_289; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_2);
lean_dec(x_1);
x_289 = !lean_is_exclusive(x_13);
if (x_289 == 0)
{
return x_13;
}
else
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_290 = lean_ctor_get(x_13, 0);
x_291 = lean_ctor_get(x_13, 1);
lean_inc(x_291);
lean_inc(x_290);
lean_dec(x_13);
x_292 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_292, 0, x_290);
lean_ctor_set(x_292, 1, x_291);
return x_292;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go_spec__1(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_4);
x_9 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Expr_mvarId_x21(x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_13 = l_Lean_MVarId_intros(x_12, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_16);
x_17 = l_Lean_Elab_Eqns_tryURefl(x_16, x_4, x_5, x_6, x_7, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_21 = l_Lean_Elab_Eqns_deltaLHS(x_16, x_4, x_5, x_6, x_7, x_20);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
lean_inc(x_5);
x_24 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof_go(x_3, x_22, x_4, x_5, x_6, x_7, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_10, x_5, x_25);
lean_dec(x_5);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_10);
lean_dec(x_5);
x_27 = !lean_is_exclusive(x_24);
if (x_27 == 0)
{
return x_24;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_24, 0);
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_24);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
uint8_t x_31; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_31 = !lean_is_exclusive(x_21);
if (x_31 == 0)
{
return x_21;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_21, 0);
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_21);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_35 = lean_ctor_get(x_17, 1);
lean_inc(x_35);
lean_dec(x_17);
x_36 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_10, x_5, x_35);
lean_dec(x_5);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_17);
if (x_37 == 0)
{
return x_17;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_17, 0);
x_39 = lean_ctor_get(x_17, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_17);
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
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_13);
if (x_41 == 0)
{
return x_13;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_13, 0);
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_13);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_19 = lean_mk_string_unchecked("Elab", 4, 4);
x_20 = lean_mk_string_unchecked("definition", 10, 10);
x_21 = lean_mk_string_unchecked("structural", 10, 10);
x_22 = lean_mk_string_unchecked("eqns", 4, 4);
x_23 = l_Lean_Name_mkStr4(x_19, x_20, x_21, x_22);
lean_inc(x_23);
x_24 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_23, x_3, x_4, x_5, x_6, x_7);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; 
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
lean_dec(x_24);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_27;
goto block_18;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_24);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_29 = lean_ctor_get(x_24, 1);
x_30 = lean_ctor_get(x_24, 0);
lean_dec(x_30);
x_31 = lean_mk_string_unchecked("proving: ", 9, 9);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
lean_inc(x_2);
x_33 = l_Lean_MessageData_ofExpr(x_2);
lean_ctor_set_tag(x_24, 7);
lean_ctor_set(x_24, 1, x_33);
lean_ctor_set(x_24, 0, x_32);
x_34 = lean_mk_string_unchecked("", 0, 0);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_24);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_23, x_36, x_3, x_4, x_5, x_6, x_29);
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_38;
goto block_18;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_dec(x_24);
x_40 = lean_mk_string_unchecked("proving: ", 9, 9);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
lean_inc(x_2);
x_42 = l_Lean_MessageData_ofExpr(x_2);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked("", 0, 0);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_23, x_46, x_3, x_4, x_5, x_6, x_39);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_8 = x_3;
x_9 = x_4;
x_10 = x_5;
x_11 = x_6;
x_12 = x_48;
goto block_18;
}
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_13 = lean_box(0);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof___lam__0), 8, 3);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_13);
lean_closure_set(x_14, 2, x_1);
x_15 = lean_box(0);
x_16 = lean_unbox(x_15);
x_17 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_14, x_16, x_8, x_9, x_10, x_11, x_12);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns_doRealize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_102; uint8_t x_103; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_6, 2);
lean_inc(x_12);
x_13 = l_Lean_Meta_tactic_hygienic;
x_14 = lean_box(0);
x_15 = l_Lean_diagnostics;
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
lean_dec(x_1);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_14);
x_19 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_12, x_13, x_18);
x_20 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_19, x_15);
x_102 = lean_ctor_get(x_10, 0);
lean_inc(x_102);
lean_dec(x_10);
x_103 = l_Lean_Kernel_isDiagnosticsEnabled(x_102);
lean_dec(x_102);
if (x_103 == 0)
{
if (x_20 == 0)
{
x_21 = x_6;
x_22 = x_7;
x_23 = x_11;
goto block_67;
}
else
{
goto block_101;
}
}
else
{
if (x_20 == 0)
{
goto block_101;
}
else
{
x_21 = x_6;
x_22 = x_7;
x_23 = x_11;
goto block_67;
}
}
block_67:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_24 = lean_ctor_get(x_21, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_21, 3);
lean_inc(x_26);
x_27 = l_Lean_maxRecDepth;
x_28 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_19, x_27);
x_29 = lean_ctor_get(x_21, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_21, 6);
lean_inc(x_30);
x_31 = lean_ctor_get(x_21, 7);
lean_inc(x_31);
x_32 = lean_ctor_get(x_21, 8);
lean_inc(x_32);
x_33 = lean_ctor_get(x_21, 9);
lean_inc(x_33);
x_34 = lean_ctor_get(x_21, 10);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 11);
lean_inc(x_35);
x_36 = lean_ctor_get_uint8(x_21, sizeof(void*)*13 + 1);
x_37 = lean_ctor_get(x_21, 12);
lean_inc(x_37);
lean_dec(x_21);
x_38 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_38, 0, x_24);
lean_ctor_set(x_38, 1, x_25);
lean_ctor_set(x_38, 2, x_19);
lean_ctor_set(x_38, 3, x_26);
lean_ctor_set(x_38, 4, x_28);
lean_ctor_set(x_38, 5, x_29);
lean_ctor_set(x_38, 6, x_30);
lean_ctor_set(x_38, 7, x_31);
lean_ctor_set(x_38, 8, x_32);
lean_ctor_set(x_38, 9, x_33);
lean_ctor_set(x_38, 10, x_34);
lean_ctor_set(x_38, 11, x_35);
lean_ctor_set(x_38, 12, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*13, x_20);
lean_ctor_set_uint8(x_38, sizeof(void*)*13 + 1, x_36);
lean_inc(x_22);
lean_inc(x_38);
lean_inc(x_3);
x_39 = l___private_Lean_Elab_PreDefinition_Structural_Eqns_0__Lean_Elab_Structural_mkProof(x_17, x_3, x_4, x_5, x_38, x_22, x_23);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Elab_Eqns_removeUnusedEqnHypotheses(x_3, x_40, x_38, x_22, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = !lean_is_exclusive(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_43, 0);
x_47 = lean_ctor_get(x_43, 1);
x_48 = lean_ctor_get(x_16, 1);
lean_inc(x_48);
lean_dec(x_16);
lean_inc(x_2);
x_49 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_49, 0, x_2);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_49, 2, x_46);
x_50 = lean_box(0);
lean_ctor_set_tag(x_43, 1);
lean_ctor_set(x_43, 1, x_50);
lean_ctor_set(x_43, 0, x_2);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_47);
lean_ctor_set(x_51, 2, x_43);
x_52 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Lean_addDecl(x_52, x_38, x_22, x_44);
return x_53;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_54 = lean_ctor_get(x_43, 0);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_43);
x_56 = lean_ctor_get(x_16, 1);
lean_inc(x_56);
lean_dec(x_16);
lean_inc(x_2);
x_57 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_57, 0, x_2);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set(x_57, 2, x_54);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_2);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_55);
lean_ctor_set(x_60, 2, x_59);
x_61 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = l_Lean_addDecl(x_61, x_38, x_22, x_44);
return x_62;
}
}
else
{
uint8_t x_63; 
lean_dec(x_38);
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_39);
if (x_63 == 0)
{
return x_39;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_39, 0);
x_65 = lean_ctor_get(x_39, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_39);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
block_101:
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_st_ref_take(x_7, x_11);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
x_72 = lean_ctor_get(x_70, 0);
lean_inc(x_72);
x_73 = l_Lean_Kernel_enableDiag(x_72, x_20);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
x_75 = lean_ctor_get(x_70, 2);
lean_inc(x_75);
x_76 = lean_ctor_get(x_70, 3);
lean_inc(x_76);
x_77 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_77);
lean_inc(x_78);
lean_ctor_set(x_68, 1, x_78);
lean_ctor_set(x_68, 0, x_78);
x_79 = lean_ctor_get(x_70, 5);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 6);
lean_inc(x_80);
x_81 = lean_ctor_get(x_70, 7);
lean_inc(x_81);
lean_dec(x_70);
x_82 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_82, 0, x_73);
lean_ctor_set(x_82, 1, x_74);
lean_ctor_set(x_82, 2, x_75);
lean_ctor_set(x_82, 3, x_76);
lean_ctor_set(x_82, 4, x_68);
lean_ctor_set(x_82, 5, x_79);
lean_ctor_set(x_82, 6, x_80);
lean_ctor_set(x_82, 7, x_81);
x_83 = lean_st_ref_set(x_7, x_82, x_71);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
lean_dec(x_83);
x_21 = x_6;
x_22 = x_7;
x_23 = x_84;
goto block_67;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_85 = lean_ctor_get(x_68, 0);
x_86 = lean_ctor_get(x_68, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_68);
x_87 = lean_ctor_get(x_85, 0);
lean_inc(x_87);
x_88 = l_Lean_Kernel_enableDiag(x_87, x_20);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_85, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_85, 3);
lean_inc(x_91);
x_92 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_93 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_93, 0, x_92);
lean_inc(x_93);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_ctor_get(x_85, 5);
lean_inc(x_95);
x_96 = lean_ctor_get(x_85, 6);
lean_inc(x_96);
x_97 = lean_ctor_get(x_85, 7);
lean_inc(x_97);
lean_dec(x_85);
x_98 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_98, 0, x_88);
lean_ctor_set(x_98, 1, x_89);
lean_ctor_set(x_98, 2, x_90);
lean_ctor_set(x_98, 3, x_91);
lean_ctor_set(x_98, 4, x_94);
lean_ctor_set(x_98, 5, x_95);
lean_ctor_set(x_98, 6, x_96);
lean_ctor_set(x_98, 7, x_97);
x_99 = lean_st_ref_set(x_7, x_98, x_86);
x_100 = lean_ctor_get(x_99, 1);
lean_inc(x_100);
lean_dec(x_99);
x_21 = x_6;
x_22 = x_7;
x_23 = x_100;
goto block_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_nat_dec_lt(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_mk_string_unchecked("Elab", 4, 4);
x_15 = lean_mk_string_unchecked("definition", 10, 10);
x_16 = lean_mk_string_unchecked("structural", 10, 10);
x_17 = lean_mk_string_unchecked("eqns", 4, 4);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
lean_inc(x_18);
x_19 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_18, x_6, x_7, x_8, x_9, x_10);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_fget(x_1, x_5);
x_53 = lean_unbox(x_21);
lean_dec(x_21);
if (x_53 == 0)
{
lean_free_object(x_19);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = x_4;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_22;
goto block_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_mk_string_unchecked("eqnType ", 8, 8);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
lean_inc(x_5);
x_56 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_55);
x_59 = lean_mk_string_unchecked(": ", 2, 2);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_19);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_28);
x_62 = l_Lean_MessageData_ofExpr(x_28);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_18, x_66, x_6, x_7, x_8, x_9, x_22);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = x_4;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_68;
goto block_52;
}
block_52:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_mk_string_unchecked("eq", 2, 2);
x_36 = l_Lean_Name_str___override(x_24, x_35);
x_37 = lean_nat_add(x_5, x_25);
x_38 = lean_name_append_index_after(x_36, x_37);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = lean_array_get(x_26, x_39, x_27);
lean_dec(x_39);
lean_inc(x_38);
lean_inc(x_2);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkEqns_doRealize), 8, 3);
lean_closure_set(x_41, 0, x_2);
lean_closure_set(x_41, 1, x_38);
lean_closure_set(x_41, 2, x_28);
lean_inc(x_38);
x_42 = l_Lean_Meta_realizeConst(x_40, x_38, x_41, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_array_push(x_29, x_38);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_nat_add(x_5, x_45);
lean_dec(x_5);
x_4 = x_44;
x_5 = x_46;
x_10 = x_43;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_101; 
x_69 = lean_ctor_get(x_19, 0);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_19);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_box(0);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_fget(x_1, x_5);
x_101 = lean_unbox(x_69);
lean_dec(x_69);
if (x_101 == 0)
{
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_77 = x_4;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_70;
goto block_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_102 = lean_mk_string_unchecked("eqnType ", 8, 8);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
lean_inc(x_5);
x_104 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_MessageData_ofFormat(x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked(": ", 2, 2);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
lean_inc(x_76);
x_111 = l_Lean_MessageData_ofExpr(x_76);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_mk_string_unchecked("", 0, 0);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_18, x_115, x_6, x_7, x_8, x_9, x_70);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_77 = x_4;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_117;
goto block_100;
}
block_100:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_mk_string_unchecked("eq", 2, 2);
x_84 = l_Lean_Name_str___override(x_72, x_83);
x_85 = lean_nat_add(x_5, x_73);
x_86 = lean_name_append_index_after(x_84, x_85);
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
x_88 = lean_array_get(x_74, x_87, x_75);
lean_dec(x_87);
lean_inc(x_86);
lean_inc(x_2);
x_89 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkEqns_doRealize), 8, 3);
lean_closure_set(x_89, 0, x_2);
lean_closure_set(x_89, 1, x_86);
lean_closure_set(x_89, 2, x_76);
lean_inc(x_86);
x_90 = l_Lean_Meta_realizeConst(x_88, x_86, x_89, x_78, x_79, x_80, x_81, x_82);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_array_push(x_77, x_86);
x_93 = lean_ctor_get(x_3, 2);
x_94 = lean_nat_add(x_5, x_93);
lean_dec(x_5);
x_4 = x_92;
x_5 = x_94;
x_10 = x_91;
goto _start;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_86);
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_nat_dec_lt(x_5, x_11);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_mk_string_unchecked("Elab", 4, 4);
x_15 = lean_mk_string_unchecked("definition", 10, 10);
x_16 = lean_mk_string_unchecked("structural", 10, 10);
x_17 = lean_mk_string_unchecked("eqns", 4, 4);
x_18 = l_Lean_Name_mkStr4(x_14, x_15, x_16, x_17);
lean_inc(x_18);
x_19 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_18, x_6, x_7, x_8, x_9, x_10);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_53; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_box(0);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_array_fget(x_1, x_5);
x_53 = lean_unbox(x_21);
lean_dec(x_21);
if (x_53 == 0)
{
lean_free_object(x_19);
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = x_4;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_22;
goto block_52;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_54 = lean_mk_string_unchecked("eqnType ", 8, 8);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
lean_inc(x_5);
x_56 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_57 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Lean_MessageData_ofFormat(x_57);
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_58);
lean_ctor_set(x_19, 0, x_55);
x_59 = lean_mk_string_unchecked(": ", 2, 2);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_61, 0, x_19);
lean_ctor_set(x_61, 1, x_60);
lean_inc(x_28);
x_62 = l_Lean_MessageData_ofExpr(x_28);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_mk_string_unchecked("", 0, 0);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_18, x_66, x_6, x_7, x_8, x_9, x_22);
x_68 = lean_ctor_get(x_67, 1);
lean_inc(x_68);
lean_dec(x_67);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_29 = x_4;
x_30 = x_6;
x_31 = x_7;
x_32 = x_8;
x_33 = x_9;
x_34 = x_68;
goto block_52;
}
block_52:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_mk_string_unchecked("eq", 2, 2);
x_36 = l_Lean_Name_str___override(x_24, x_35);
x_37 = lean_nat_add(x_5, x_25);
x_38 = lean_name_append_index_after(x_36, x_37);
x_39 = lean_ctor_get(x_2, 2);
lean_inc(x_39);
x_40 = lean_array_get(x_26, x_39, x_27);
lean_dec(x_39);
lean_inc(x_38);
lean_inc(x_2);
x_41 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkEqns_doRealize), 8, 3);
lean_closure_set(x_41, 0, x_2);
lean_closure_set(x_41, 1, x_38);
lean_closure_set(x_41, 2, x_28);
lean_inc(x_38);
x_42 = l_Lean_Meta_realizeConst(x_40, x_38, x_41, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_array_push(x_29, x_38);
x_45 = lean_ctor_get(x_3, 2);
x_46 = lean_nat_add(x_5, x_45);
lean_dec(x_5);
x_47 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg(x_1, x_2, x_3, x_44, x_46, x_6, x_7, x_8, x_9, x_43);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_38);
lean_dec(x_29);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_42);
if (x_48 == 0)
{
return x_42;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_42, 0);
x_50 = lean_ctor_get(x_42, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_42);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_101; 
x_69 = lean_ctor_get(x_19, 0);
x_70 = lean_ctor_get(x_19, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_19);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_unsigned_to_nat(1u);
x_74 = lean_box(0);
x_75 = lean_unsigned_to_nat(0u);
x_76 = lean_array_fget(x_1, x_5);
x_101 = lean_unbox(x_69);
lean_dec(x_69);
if (x_101 == 0)
{
lean_dec(x_18);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_77 = x_4;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_70;
goto block_100;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_102 = lean_mk_string_unchecked("eqnType ", 8, 8);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
lean_inc(x_5);
x_104 = l___private_Init_Data_Repr_0__Nat_reprFast(x_5);
x_105 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_105, 0, x_104);
x_106 = l_Lean_MessageData_ofFormat(x_105);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked(": ", 2, 2);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
lean_inc(x_76);
x_111 = l_Lean_MessageData_ofExpr(x_76);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_mk_string_unchecked("", 0, 0);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_18, x_115, x_6, x_7, x_8, x_9, x_70);
x_117 = lean_ctor_get(x_116, 1);
lean_inc(x_117);
lean_dec(x_116);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_77 = x_4;
x_78 = x_6;
x_79 = x_7;
x_80 = x_8;
x_81 = x_9;
x_82 = x_117;
goto block_100;
}
block_100:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_83 = lean_mk_string_unchecked("eq", 2, 2);
x_84 = l_Lean_Name_str___override(x_72, x_83);
x_85 = lean_nat_add(x_5, x_73);
x_86 = lean_name_append_index_after(x_84, x_85);
x_87 = lean_ctor_get(x_2, 2);
lean_inc(x_87);
x_88 = lean_array_get(x_74, x_87, x_75);
lean_dec(x_87);
lean_inc(x_86);
lean_inc(x_2);
x_89 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkEqns_doRealize), 8, 3);
lean_closure_set(x_89, 0, x_2);
lean_closure_set(x_89, 1, x_86);
lean_closure_set(x_89, 2, x_76);
lean_inc(x_86);
x_90 = l_Lean_Meta_realizeConst(x_88, x_86, x_89, x_78, x_79, x_80, x_81, x_82);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_array_push(x_77, x_86);
x_93 = lean_ctor_get(x_3, 2);
x_94 = lean_nat_add(x_5, x_93);
lean_dec(x_5);
x_95 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg(x_1, x_2, x_3, x_92, x_94, x_6, x_7, x_8, x_9, x_91);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_86);
lean_dec(x_77);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_96 = lean_ctor_get(x_90, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_90, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_98 = x_90;
} else {
 lean_dec_ref(x_90);
 x_98 = lean_box(0);
}
if (lean_is_scalar(x_98)) {
 x_99 = lean_alloc_ctor(1, 2, 0);
} else {
 x_99 = x_98;
}
lean_ctor_set(x_99, 0, x_96);
lean_ctor_set(x_99, 1, x_97);
return x_99;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_box(0);
x_12 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_10, x_11);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
lean_dec(x_1);
x_14 = l_Lean_Expr_const___override(x_13, x_12);
x_15 = l_Lean_mkAppN(x_14, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_16 = l_Lean_Meta_mkEq(x_15, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_5);
x_20 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_19, x_5, x_6, x_7, x_8, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
lean_dec(x_2);
x_24 = l_Lean_Expr_mvarId_x21(x_21);
lean_dec(x_21);
x_25 = l_Lean_Elab_Eqns_mkEqnTypes(x_23, x_24, x_5, x_6, x_7, x_8, x_22);
return x_25;
}
else
{
uint8_t x_26; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
x_26 = !lean_is_exclusive(x_16);
if (x_26 == 0)
{
return x_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_16, 0);
x_28 = lean_ctor_get(x_16, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_16);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_89; uint8_t x_90; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_1);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkEqns___lam__0___boxed), 9, 2);
lean_closure_set(x_11, 0, x_10);
lean_closure_set(x_11, 1, x_1);
x_12 = lean_ctor_get(x_10, 3);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(1);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
x_15 = l_Lean_Meta_tactic_hygienic;
x_16 = lean_box(0);
x_17 = l_Lean_diagnostics;
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___boxed), 9, 4);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_12);
lean_closure_set(x_18, 2, x_11);
lean_closure_set(x_18, 3, x_13);
x_19 = lean_unbox(x_16);
x_20 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_14, x_15, x_19);
x_21 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_20, x_17);
x_89 = lean_ctor_get(x_8, 0);
lean_inc(x_89);
lean_dec(x_8);
x_90 = l_Lean_Kernel_isDiagnosticsEnabled(x_89);
lean_dec(x_89);
if (x_90 == 0)
{
if (x_21 == 0)
{
x_22 = x_4;
x_23 = x_5;
x_24 = x_9;
goto block_54;
}
else
{
goto block_88;
}
}
else
{
if (x_21 == 0)
{
goto block_88;
}
else
{
x_22 = x_4;
x_23 = x_5;
x_24 = x_9;
goto block_54;
}
}
block_54:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 3);
lean_inc(x_27);
x_28 = l_Lean_maxRecDepth;
x_29 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_20, x_28);
x_30 = lean_ctor_get(x_22, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 6);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 7);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 8);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 9);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 10);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 11);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_22, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get(x_22, 12);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_20);
lean_ctor_set(x_39, 3, x_27);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_30);
lean_ctor_set(x_39, 6, x_31);
lean_ctor_set(x_39, 7, x_32);
lean_ctor_set(x_39, 8, x_33);
lean_ctor_set(x_39, 9, x_34);
lean_ctor_set(x_39, 10, x_35);
lean_ctor_set(x_39, 11, x_36);
lean_ctor_set(x_39, 12, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*13, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*13 + 1, x_37);
x_40 = lean_unbox(x_16);
lean_inc(x_23);
lean_inc(x_39);
lean_inc(x_3);
lean_inc(x_2);
x_41 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_18, x_40, x_2, x_3, x_39, x_23, x_24);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_unsigned_to_nat(0u);
x_45 = lean_mk_empty_array_with_capacity(x_44);
x_46 = lean_array_get_size(x_42);
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_44);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_47);
x_49 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___redArg(x_42, x_1, x_48, x_45, x_44, x_2, x_3, x_39, x_23, x_43);
lean_dec(x_48);
lean_dec(x_42);
return x_49;
}
else
{
uint8_t x_50; 
lean_dec(x_39);
lean_dec(x_23);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_41);
if (x_50 == 0)
{
return x_41;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_41, 0);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_41);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
block_88:
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_st_ref_take(x_5, x_9);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_57 = lean_ctor_get(x_55, 0);
x_58 = lean_ctor_get(x_55, 1);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = l_Lean_Kernel_enableDiag(x_59, x_21);
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 2);
lean_inc(x_62);
x_63 = lean_ctor_get(x_57, 3);
lean_inc(x_63);
x_64 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_64);
lean_inc(x_65);
lean_ctor_set(x_55, 1, x_65);
lean_ctor_set(x_55, 0, x_65);
x_66 = lean_ctor_get(x_57, 5);
lean_inc(x_66);
x_67 = lean_ctor_get(x_57, 6);
lean_inc(x_67);
x_68 = lean_ctor_get(x_57, 7);
lean_inc(x_68);
lean_dec(x_57);
x_69 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_69, 0, x_60);
lean_ctor_set(x_69, 1, x_61);
lean_ctor_set(x_69, 2, x_62);
lean_ctor_set(x_69, 3, x_63);
lean_ctor_set(x_69, 4, x_55);
lean_ctor_set(x_69, 5, x_66);
lean_ctor_set(x_69, 6, x_67);
lean_ctor_set(x_69, 7, x_68);
x_70 = lean_st_ref_set(x_5, x_69, x_58);
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_22 = x_4;
x_23 = x_5;
x_24 = x_71;
goto block_54;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_72 = lean_ctor_get(x_55, 0);
x_73 = lean_ctor_get(x_55, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_55);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
x_75 = l_Lean_Kernel_enableDiag(x_74, x_21);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
x_77 = lean_ctor_get(x_72, 2);
lean_inc(x_77);
x_78 = lean_ctor_get(x_72, 3);
lean_inc(x_78);
x_79 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_inc(x_80);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_ctor_get(x_72, 5);
lean_inc(x_82);
x_83 = lean_ctor_get(x_72, 6);
lean_inc(x_83);
x_84 = lean_ctor_get(x_72, 7);
lean_inc(x_84);
lean_dec(x_72);
x_85 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_85, 0, x_75);
lean_ctor_set(x_85, 1, x_76);
lean_ctor_set(x_85, 2, x_77);
lean_ctor_set(x_85, 3, x_78);
lean_ctor_set(x_85, 4, x_81);
lean_ctor_set(x_85, 5, x_82);
lean_ctor_set(x_85, 6, x_83);
lean_ctor_set(x_85, 7, x_84);
x_86 = lean_st_ref_set(x_5, x_85, x_73);
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_22 = x_4;
x_23 = x_5;
x_24 = x_87;
goto block_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Structural_mkEqns_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkEqns___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Structural_mkEqns___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBMap_toArray___at___Lean_mkMapDeclarationExtension_spec__1___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_initFn___lam__0____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282____boxed), 1, 0);
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Elab", 4, 4);
x_5 = lean_mk_string_unchecked("Structural", 10, 10);
x_6 = lean_mk_string_unchecked("eqnInfoExt", 10, 10);
x_7 = l_Lean_Name_mkStr4(x_3, x_4, x_5, x_6);
x_8 = l_Lean_mkMapDeclarationExtension___redArg(x_7, x_2, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn___lam__0____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Structural_initFn___lam__0____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
lean_inc(x_8);
x_9 = l_Lean_Meta_ensureEqnReservedNamesAvailable(x_8, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = l_Lean_Elab_Structural_eqnInfoExt;
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
lean_dec(x_1);
lean_inc(x_8);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_8);
lean_ctor_set(x_20, 1, x_17);
lean_ctor_set(x_20, 2, x_18);
lean_ctor_set(x_20, 3, x_19);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_3);
lean_ctor_set(x_21, 2, x_2);
lean_ctor_set(x_21, 3, x_4);
x_22 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_16, x_15, x_8, x_21);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_13, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_13, 3);
lean_inc(x_25);
x_26 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_26);
lean_inc(x_27);
lean_ctor_set(x_11, 1, x_27);
lean_ctor_set(x_11, 0, x_27);
x_28 = lean_ctor_get(x_13, 5);
lean_inc(x_28);
x_29 = lean_ctor_get(x_13, 6);
lean_inc(x_29);
x_30 = lean_ctor_get(x_13, 7);
lean_inc(x_30);
lean_dec(x_13);
x_31 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_31, 0, x_22);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_31, 2, x_24);
lean_ctor_set(x_31, 3, x_25);
lean_ctor_set(x_31, 4, x_11);
lean_ctor_set(x_31, 5, x_28);
lean_ctor_set(x_31, 6, x_29);
lean_ctor_set(x_31, 7, x_30);
x_32 = lean_st_ref_set(x_6, x_31, x_14);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_32, 0);
lean_dec(x_34);
x_35 = lean_box(0);
lean_ctor_set(x_32, 0, x_35);
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 1);
lean_inc(x_36);
lean_dec(x_32);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_39 = lean_ctor_get(x_11, 0);
x_40 = lean_ctor_get(x_11, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_11);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = l_Lean_Elab_Structural_eqnInfoExt;
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 4);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 5);
lean_inc(x_45);
lean_dec(x_1);
lean_inc(x_8);
x_46 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_46, 0, x_8);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_45);
x_47 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_3);
lean_ctor_set(x_47, 2, x_2);
lean_ctor_set(x_47, 3, x_4);
x_48 = l_Lean_MapDeclarationExtension_insert(lean_box(0), x_42, x_41, x_8, x_47);
x_49 = lean_ctor_get(x_39, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_39, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_39, 3);
lean_inc(x_51);
x_52 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_ctor_get(x_39, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_39, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_39, 7);
lean_inc(x_57);
lean_dec(x_39);
x_58 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_50);
lean_ctor_set(x_58, 3, x_51);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
lean_ctor_set(x_58, 6, x_56);
lean_ctor_set(x_58, 7, x_57);
x_59 = lean_st_ref_set(x_6, x_58, x_40);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_61 = x_59;
} else {
 lean_dec_ref(x_59);
 x_61 = lean_box(0);
}
x_62 = lean_box(0);
if (lean_is_scalar(x_61)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_61;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_60);
return x_63;
}
}
else
{
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_registerEqnsInfo___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_Structural_registerEqnsInfo(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getEqnsFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Elab_Structural_instInhabitedEqnInfo;
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Elab_Structural_eqnInfoExt;
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_11, x_13, x_12, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = lean_box(0);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
uint8_t x_18; 
lean_free_object(x_7);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_Elab_Structural_mkEqns(x_19, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_16, 0, x_22);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_16);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
x_31 = l_Lean_Elab_Structural_mkEqns(x_30, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_7);
x_43 = l_Lean_Elab_Structural_instInhabitedEqnInfo;
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Elab_Structural_eqnInfoExt;
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_43, x_45, x_44, x_1, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Elab_Structural_mkEqns(x_51, x_2, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_box(0);
lean_inc(x_11);
x_13 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_11, x_12);
lean_inc(x_2);
x_14 = l_Lean_Expr_const___override(x_2, x_13);
x_15 = l_Lean_mkAppN(x_14, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Meta_mkEq(x_15, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
lean_inc(x_6);
lean_inc(x_17);
x_20 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_17, x_19, x_6, x_7, x_8, x_9, x_18);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_Expr_mvarId_x21(x_21);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_24 = l_Lean_Elab_Eqns_mkUnfoldProof(x_2, x_23, x_6, x_7, x_8, x_9, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; 
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_box(1);
x_28 = lean_box(1);
x_29 = lean_unbox(x_26);
x_30 = lean_unbox(x_27);
x_31 = lean_unbox(x_28);
x_32 = l_Lean_Meta_mkForallFVars(x_4, x_17, x_29, x_30, x_31, x_6, x_7, x_8, x_9, x_25);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_21, x_7, x_34);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_unbox(x_26);
x_40 = lean_unbox(x_27);
x_41 = lean_unbox(x_26);
x_42 = lean_unbox(x_28);
x_43 = l_Lean_Meta_mkLambdaFVars(x_4, x_37, x_39, x_40, x_41, x_42, x_6, x_7, x_8, x_9, x_38);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
lean_inc(x_3);
x_46 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_46, 0, x_3);
lean_ctor_set(x_46, 1, x_11);
lean_ctor_set(x_46, 2, x_33);
x_47 = lean_box(0);
lean_ctor_set_tag(x_35, 1);
lean_ctor_set(x_35, 1, x_47);
lean_ctor_set(x_35, 0, x_3);
x_48 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_44);
lean_ctor_set(x_48, 2, x_35);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = l_Lean_addDecl(x_49, x_8, x_9, x_45);
return x_50;
}
else
{
uint8_t x_51; 
lean_free_object(x_35);
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_51 = !lean_is_exclusive(x_43);
if (x_51 == 0)
{
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_43, 0);
x_53 = lean_ctor_get(x_43, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_43);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
else
{
lean_object* x_55; lean_object* x_56; uint8_t x_57; uint8_t x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_55 = lean_ctor_get(x_35, 0);
x_56 = lean_ctor_get(x_35, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_35);
x_57 = lean_unbox(x_26);
x_58 = lean_unbox(x_27);
x_59 = lean_unbox(x_26);
x_60 = lean_unbox(x_28);
x_61 = l_Lean_Meta_mkLambdaFVars(x_4, x_55, x_57, x_58, x_59, x_60, x_6, x_7, x_8, x_9, x_56);
lean_dec(x_7);
lean_dec(x_6);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_3);
x_64 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_64, 0, x_3);
lean_ctor_set(x_64, 1, x_11);
lean_ctor_set(x_64, 2, x_33);
x_65 = lean_box(0);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_3);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_62);
lean_ctor_set(x_67, 2, x_66);
x_68 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = l_Lean_addDecl(x_68, x_8, x_9, x_63);
return x_69;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_70 = lean_ctor_get(x_61, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_61, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_72 = x_61;
} else {
 lean_dec_ref(x_61);
 x_72 = lean_box(0);
}
if (lean_is_scalar(x_72)) {
 x_73 = lean_alloc_ctor(1, 2, 0);
} else {
 x_73 = x_72;
}
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_32);
if (x_74 == 0)
{
return x_32;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_32, 0);
x_76 = lean_ctor_get(x_32, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_32);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_dec(x_21);
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_24;
}
}
else
{
uint8_t x_78; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_78 = !lean_is_exclusive(x_16);
if (x_78 == 0)
{
return x_16;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_16, 0);
x_80 = lean_ctor_get(x_16, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_16);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq_doRealize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_77; uint8_t x_78; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed), 10, 3);
lean_closure_set(x_13, 0, x_12);
lean_closure_set(x_13, 1, x_1);
lean_closure_set(x_13, 2, x_3);
x_14 = lean_ctor_get(x_6, 2);
lean_inc(x_14);
x_15 = l_Lean_Meta_tactic_hygienic;
x_16 = lean_box(0);
x_17 = l_Lean_diagnostics;
x_18 = lean_ctor_get(x_12, 3);
lean_inc(x_18);
lean_dec(x_12);
x_19 = lean_unbox(x_16);
x_20 = l_Lean_Option_set___at___Lean_Environment_realizeConst_spec__2(x_14, x_15, x_19);
x_21 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_20, x_17);
x_77 = lean_ctor_get(x_10, 0);
lean_inc(x_77);
lean_dec(x_10);
x_78 = l_Lean_Kernel_isDiagnosticsEnabled(x_77);
lean_dec(x_77);
if (x_78 == 0)
{
if (x_21 == 0)
{
x_22 = x_6;
x_23 = x_7;
x_24 = x_11;
goto block_42;
}
else
{
goto block_76;
}
}
else
{
if (x_21 == 0)
{
goto block_76;
}
else
{
x_22 = x_6;
x_23 = x_7;
x_24 = x_11;
goto block_42;
}
}
block_42:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 3);
lean_inc(x_27);
x_28 = l_Lean_maxRecDepth;
x_29 = l_Lean_Option_get___at___Lean_profiler_threshold_getSecs_spec__0(x_20, x_28);
x_30 = lean_ctor_get(x_22, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 6);
lean_inc(x_31);
x_32 = lean_ctor_get(x_22, 7);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 8);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 9);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 10);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 11);
lean_inc(x_36);
x_37 = lean_ctor_get_uint8(x_22, sizeof(void*)*13 + 1);
x_38 = lean_ctor_get(x_22, 12);
lean_inc(x_38);
lean_dec(x_22);
x_39 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_39, 0, x_25);
lean_ctor_set(x_39, 1, x_26);
lean_ctor_set(x_39, 2, x_20);
lean_ctor_set(x_39, 3, x_27);
lean_ctor_set(x_39, 4, x_29);
lean_ctor_set(x_39, 5, x_30);
lean_ctor_set(x_39, 6, x_31);
lean_ctor_set(x_39, 7, x_32);
lean_ctor_set(x_39, 8, x_33);
lean_ctor_set(x_39, 9, x_34);
lean_ctor_set(x_39, 10, x_35);
lean_ctor_set(x_39, 11, x_36);
lean_ctor_set(x_39, 12, x_38);
lean_ctor_set_uint8(x_39, sizeof(void*)*13, x_21);
lean_ctor_set_uint8(x_39, sizeof(void*)*13 + 1, x_37);
x_40 = lean_unbox(x_16);
x_41 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_18, x_13, x_40, x_4, x_5, x_39, x_23, x_24);
return x_41;
}
block_76:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_st_ref_take(x_7, x_11);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_43, 0);
x_46 = lean_ctor_get(x_43, 1);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = l_Lean_Kernel_enableDiag(x_47, x_21);
x_49 = lean_ctor_get(x_45, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 3);
lean_inc(x_51);
x_52 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_53);
lean_ctor_set(x_43, 1, x_53);
lean_ctor_set(x_43, 0, x_53);
x_54 = lean_ctor_get(x_45, 5);
lean_inc(x_54);
x_55 = lean_ctor_get(x_45, 6);
lean_inc(x_55);
x_56 = lean_ctor_get(x_45, 7);
lean_inc(x_56);
lean_dec(x_45);
x_57 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_57, 0, x_48);
lean_ctor_set(x_57, 1, x_49);
lean_ctor_set(x_57, 2, x_50);
lean_ctor_set(x_57, 3, x_51);
lean_ctor_set(x_57, 4, x_43);
lean_ctor_set(x_57, 5, x_54);
lean_ctor_set(x_57, 6, x_55);
lean_ctor_set(x_57, 7, x_56);
x_58 = lean_st_ref_set(x_7, x_57, x_46);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_22 = x_6;
x_23 = x_7;
x_24 = x_59;
goto block_42;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_43, 0);
x_61 = lean_ctor_get(x_43, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_43);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
x_63 = l_Lean_Kernel_enableDiag(x_62, x_21);
x_64 = lean_ctor_get(x_60, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_60, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 3);
lean_inc(x_66);
x_67 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_inc(x_68);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_ctor_get(x_60, 5);
lean_inc(x_70);
x_71 = lean_ctor_get(x_60, 6);
lean_inc(x_71);
x_72 = lean_ctor_get(x_60, 7);
lean_inc(x_72);
lean_dec(x_60);
x_73 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_73, 0, x_63);
lean_ctor_set(x_73, 1, x_64);
lean_ctor_set(x_73, 2, x_65);
lean_ctor_set(x_73, 3, x_66);
lean_ctor_set(x_73, 4, x_69);
lean_ctor_set(x_73, 5, x_70);
lean_ctor_set(x_73, 6, x_71);
lean_ctor_set(x_73, 7, x_72);
x_74 = lean_st_ref_set(x_7, x_73, x_61);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_22 = x_6;
x_23 = x_7;
x_24 = x_75;
goto block_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Structural_mkUnfoldEq_doRealize___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_mkUnfoldEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_box(0);
x_9 = lean_mk_string_unchecked("eq_def", 6, 6);
lean_inc(x_1);
x_10 = l_Lean_Name_str___override(x_1, x_9);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get(x_8, x_11, x_12);
lean_dec(x_11);
lean_inc(x_10);
x_14 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_mkUnfoldEq_doRealize), 8, 3);
lean_closure_set(x_14, 0, x_1);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_10);
lean_inc(x_10);
x_15 = l_Lean_Meta_realizeConst(x_13, x_10, x_14, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_10);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
else
{
uint8_t x_20; 
lean_dec(x_10);
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
return x_15;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_15, 0);
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getUnfoldFor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l_Lean_Elab_Structural_instInhabitedEqnInfo;
x_12 = lean_ctor_get(x_9, 0);
lean_inc(x_12);
lean_dec(x_9);
x_13 = l_Lean_Elab_Structural_eqnInfoExt;
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_inc(x_1);
x_16 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_11, x_13, x_12, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = lean_box(0);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
else
{
uint8_t x_18; 
lean_free_object(x_7);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = l_Lean_Elab_Structural_mkUnfoldEq(x_1, x_19, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_ctor_set(x_16, 0, x_22);
lean_ctor_set(x_20, 0, x_16);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_20, 0);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_20);
lean_ctor_set(x_16, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_16);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_free_object(x_16);
x_26 = !lean_is_exclusive(x_20);
if (x_26 == 0)
{
return x_20;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_20, 0);
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_20);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
lean_dec(x_16);
x_31 = l_Lean_Elab_Structural_mkUnfoldEq(x_1, x_30, x_2, x_3, x_4, x_5, x_10);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_34 = x_31;
} else {
 lean_dec_ref(x_31);
 x_34 = lean_box(0);
}
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_32);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_31, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_31, 1);
lean_inc(x_38);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_39 = x_31;
} else {
 lean_dec_ref(x_31);
 x_39 = lean_box(0);
}
if (lean_is_scalar(x_39)) {
 x_40 = lean_alloc_ctor(1, 2, 0);
} else {
 x_40 = x_39;
}
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_41 = lean_ctor_get(x_7, 0);
x_42 = lean_ctor_get(x_7, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_7);
x_43 = l_Lean_Elab_Structural_instInhabitedEqnInfo;
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Elab_Structural_eqnInfoExt;
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
lean_inc(x_1);
x_48 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_43, x_45, x_44, x_1, x_47);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_49 = lean_box(0);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_42);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
lean_inc(x_51);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 x_52 = x_48;
} else {
 lean_dec_ref(x_48);
 x_52 = lean_box(0);
}
x_53 = l_Lean_Elab_Structural_mkUnfoldEq(x_1, x_51, x_2, x_3, x_4, x_5, x_42);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_56 = x_53;
} else {
 lean_dec_ref(x_53);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_52)) {
 x_57 = lean_alloc_ctor(1, 1, 0);
} else {
 x_57 = x_52;
}
lean_ctor_set(x_57, 0, x_54);
if (lean_is_scalar(x_56)) {
 x_58 = lean_alloc_ctor(0, 2, 0);
} else {
 x_58 = x_56;
}
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_55);
return x_58;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_52);
x_59 = lean_ctor_get(x_53, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_61 = x_53;
} else {
 lean_dec_ref(x_53);
 x_61 = lean_box(0);
}
if (lean_is_scalar(x_61)) {
 x_62 = lean_alloc_ctor(1, 2, 0);
} else {
 x_62 = x_61;
}
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_60);
return x_62;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Elab_Structural_instInhabitedEqnInfo;
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Elab_Structural_eqnInfoExt;
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_7, x_9, x_8, x_1, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_box(0);
lean_ctor_set(x_4, 0, x_13);
return x_4;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_12, 0, x_16);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_4, 0, x_19);
return x_4;
}
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_4, 0);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_4);
x_22 = l_Lean_Elab_Structural_instInhabitedEqnInfo;
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Elab_Structural_eqnInfoExt;
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
x_27 = l_Lean_MapDeclarationExtension_find_x3f(lean_box(0), x_22, x_24, x_23, x_1, x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_21);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
if (lean_is_scalar(x_31)) {
 x_33 = lean_alloc_ctor(1, 1, 0);
} else {
 x_33 = x_31;
}
lean_ctor_set(x_33, 0, x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_21);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* lean_get_structural_rec_arg_pos(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
lean_dec(x_2);
x_5 = l_Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(x_1, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_Structural_getStructuralRecArgPosImp_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1773_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getEqnsFor_x3f), 6, 0);
x_3 = l_Lean_Meta_registerGetEqnsFn(x_2, x_1);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_alloc_closure((void*)(l_Lean_Elab_Structural_getUnfoldFor_x3f), 6, 0);
x_6 = l_Lean_Meta_registerGetUnfoldEqnFn(x_5, x_4);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_mk_string_unchecked("Elab", 4, 4);
x_9 = lean_mk_string_unchecked("definition", 10, 10);
x_10 = lean_mk_string_unchecked("structural", 10, 10);
x_11 = lean_mk_string_unchecked("eqns", 4, 4);
lean_inc(x_8);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
x_13 = lean_box(0);
x_14 = lean_box(0);
x_15 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_15);
x_16 = l_Lean_Name_str___override(x_14, x_15);
lean_inc(x_8);
x_17 = l_Lean_Name_str___override(x_16, x_8);
x_18 = lean_mk_string_unchecked("Structural", 10, 10);
lean_inc(x_18);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_mk_string_unchecked("initFn", 6, 6);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("_@", 2, 2);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = l_Lean_Name_str___override(x_23, x_15);
x_25 = l_Lean_Name_str___override(x_24, x_8);
x_26 = lean_mk_string_unchecked("PreDefinition", 13, 13);
x_27 = l_Lean_Name_str___override(x_25, x_26);
x_28 = l_Lean_Name_str___override(x_27, x_18);
x_29 = lean_mk_string_unchecked("Eqns", 4, 4);
x_30 = l_Lean_Name_str___override(x_28, x_29);
x_31 = lean_mk_string_unchecked("_hyg", 4, 4);
x_32 = l_Lean_Name_str___override(x_30, x_31);
x_33 = lean_unsigned_to_nat(1773u);
x_34 = l_Lean_Name_num___override(x_32, x_33);
x_35 = lean_unbox(x_13);
x_36 = l_Lean_registerTraceClass(x_12, x_35, x_34, x_7);
return x_36;
}
else
{
return x_6;
}
}
else
{
return x_3;
}
}
}
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Split(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Main(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Apply(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_FixedParams(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_PreDefinition_Structural_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_PreDefinition_Structural_Eqns(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Split(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Main(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Apply(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_FixedParams(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_PreDefinition_Structural_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Structural_instInhabitedEqnInfo = _init_l_Lean_Elab_Structural_instInhabitedEqnInfo();
lean_mark_persistent(l_Lean_Elab_Structural_instInhabitedEqnInfo);
if (builtin) {res = l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1282_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Structural_eqnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Structural_eqnInfoExt);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Structural_initFn____x40_Lean_Elab_PreDefinition_Structural_Eqns___hyg_1773_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
