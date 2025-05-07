// Lean compiler output
// Module: Lean.Meta.LevelDefEq
// Imports: Lean.Util.CollectMVars Lean.Meta.Basic Lean.Meta.InferType Lean.Meta.DecLevel
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
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Bool_toLBool(uint8_t);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvar___override(lean_object*);
lean_object* l_Lean_Meta_mkFreshLevelMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_exceptBoolEmoji(lean_object*, lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkLevelMax_x27(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern uint8_t l_instInhabitedBool;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_throwIsDefEqStuck___redArg(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_1927_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Meta_decLevel_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_occurs(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LMVarId_isReadOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(uint8_t, uint8_t);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_mvarId_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateLevelMVars___at___Lean_Meta_normalizeLevel_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getOffset(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_getLevelOffset(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofLevel(lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isParam(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_param___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Level_isMVar(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_level_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Level_normalize(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object*, lean_object*);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_9; 
x_9 = lean_level_eq(x_2, x_1);
if (x_9 == 0)
{
uint8_t x_10; 
x_10 = l_Lean_Level_occurs(x_1, x_2);
x_3 = x_10;
goto block_8;
}
else
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_3 = x_12;
goto block_8;
}
block_8:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_4);
if (x_6 == 0)
{
x_2 = x_5;
goto _start;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax_visit(x_1, x_4);
return x_6;
}
else
{
return x_5;
}
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_box(0);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
lean_inc(x_2);
lean_inc(x_3);
x_4 = l_Lean_mkLevelMax_x27(x_3, x_2);
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_4);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_5, x_3);
x_2 = x_6;
x_3 = x_7;
goto _start;
}
case 5:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_name_eq(x_9, x_1);
lean_dec(x_9);
if (x_10 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
lean_dec(x_4);
return x_3;
}
}
default: 
{
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_8, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_8, 4);
lean_inc(x_13);
x_14 = lean_ctor_get(x_8, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_8, 6);
lean_inc(x_15);
x_16 = l_Lean_PersistentHashMap_insert___at___Lean_assignLevelMVarExp_spec__0(lean_box(0), x_15, x_1, x_2);
x_17 = lean_ctor_get(x_8, 7);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 8);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_10);
lean_ctor_set(x_19, 2, x_11);
lean_ctor_set(x_19, 3, x_12);
lean_ctor_set(x_19, 4, x_13);
lean_ctor_set(x_19, 5, x_14);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set(x_19, 7, x_17);
lean_ctor_set(x_19, 8, x_18);
x_20 = lean_ctor_get(x_6, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 4);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_19);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_st_ref_set(x_3, x_24, x_7);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_25, 0);
lean_dec(x_27);
x_28 = lean_box(0);
lean_ctor_set(x_25, 0, x_28);
return x_25;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
lean_dec(x_25);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_1, x_2, x_4, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = l_Lean_Level_isMax(x_2);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_mk_string_unchecked("Lean.Meta.LevelDefEq", 20, 20);
x_10 = lean_mk_string_unchecked("_private.Lean.Meta.LevelDefEq.0.Lean.Meta.solveSelfMax", 54, 54);
x_11 = lean_unsigned_to_nat(36u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_mk_string_unchecked("assertion violation: v.isMax\n  ", 31, 31);
x_14 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_9, x_10, x_11, x_12, x_13);
lean_dec(x_13);
lean_dec(x_10);
lean_dec(x_9);
x_15 = l_panic___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__0(x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = l_Lean_Meta_mkFreshLevelMVar(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_mkMaxArgsDiff(x_1, x_2, x_17);
x_20 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_1, x_19, x_4, x_18);
lean_dec(x_4);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_level_eq(x_1, x_2);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
else
{
lean_object* x_9; uint8_t x_10; 
x_9 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_3, x_1, x_4, x_5);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
x_12 = lean_box(x_6);
lean_ctor_set(x_9, 0, x_12);
return x_9;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_box(x_6);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_2, x_3, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_8; 
lean_dec(x_1);
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_box(0);
switch (lean_obj_tag(x_9)) {
case 0:
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = l_Lean_Level_max___override(x_11, x_11);
x_13 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
return x_13;
}
case 1:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Level_succ___override(x_14);
x_16 = l_Lean_Level_max___override(x_11, x_15);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_16, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_dec(x_10);
x_20 = l_Lean_Level_max___override(x_18, x_19);
x_21 = l_Lean_Level_max___override(x_11, x_20);
x_22 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_21, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_21);
return x_22;
}
case 3:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_10, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_10, 1);
lean_inc(x_24);
lean_dec(x_10);
x_25 = l_Lean_Level_imax___override(x_23, x_24);
x_26 = l_Lean_Level_max___override(x_11, x_25);
x_27 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_26, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_26);
return x_27;
}
case 4:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_1);
x_28 = lean_ctor_get(x_10, 0);
lean_inc(x_28);
lean_dec(x_10);
x_29 = l_Lean_Level_param___override(x_28);
x_30 = l_Lean_Level_max___override(x_11, x_29);
x_31 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_30, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_30);
return x_31;
}
default: 
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_10, 0);
lean_inc(x_32);
lean_dec(x_10);
x_33 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_11, x_32, x_4, x_7);
return x_33;
}
}
}
case 1:
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_9, 0);
lean_inc(x_34);
lean_dec(x_9);
x_35 = l_Lean_Level_succ___override(x_34);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_1);
x_36 = l_Lean_Level_max___override(x_35, x_11);
x_37 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_36, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_36);
return x_37;
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_1);
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
lean_dec(x_10);
x_39 = l_Lean_Level_succ___override(x_38);
x_40 = l_Lean_Level_max___override(x_35, x_39);
x_41 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_40, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_40);
return x_41;
}
case 2:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_1);
x_42 = lean_ctor_get(x_10, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_10, 1);
lean_inc(x_43);
lean_dec(x_10);
x_44 = l_Lean_Level_max___override(x_42, x_43);
x_45 = l_Lean_Level_max___override(x_35, x_44);
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_45, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_45);
return x_46;
}
case 3:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_47 = lean_ctor_get(x_10, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_10, 1);
lean_inc(x_48);
lean_dec(x_10);
x_49 = l_Lean_Level_imax___override(x_47, x_48);
x_50 = l_Lean_Level_max___override(x_35, x_49);
x_51 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_50, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_50);
return x_51;
}
case 4:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_1);
x_52 = lean_ctor_get(x_10, 0);
lean_inc(x_52);
lean_dec(x_10);
x_53 = l_Lean_Level_param___override(x_52);
x_54 = l_Lean_Level_max___override(x_35, x_53);
x_55 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_54, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_54);
return x_55;
}
default: 
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_10, 0);
lean_inc(x_56);
lean_dec(x_10);
x_57 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_35, x_56, x_4, x_7);
lean_dec(x_35);
return x_57;
}
}
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_9, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_9, 1);
lean_inc(x_59);
lean_dec(x_9);
x_60 = l_Lean_Level_max___override(x_58, x_59);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_61; lean_object* x_62; 
lean_dec(x_1);
x_61 = l_Lean_Level_max___override(x_60, x_11);
x_62 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_61, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_61);
return x_62;
}
case 1:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_1);
x_63 = lean_ctor_get(x_10, 0);
lean_inc(x_63);
lean_dec(x_10);
x_64 = l_Lean_Level_succ___override(x_63);
x_65 = l_Lean_Level_max___override(x_60, x_64);
x_66 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_65, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_65);
return x_66;
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
lean_dec(x_1);
x_67 = lean_ctor_get(x_10, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_10, 1);
lean_inc(x_68);
lean_dec(x_10);
x_69 = l_Lean_Level_max___override(x_67, x_68);
x_70 = l_Lean_Level_max___override(x_60, x_69);
x_71 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_70, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_70);
return x_71;
}
case 3:
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_1);
x_72 = lean_ctor_get(x_10, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_dec(x_10);
x_74 = l_Lean_Level_imax___override(x_72, x_73);
x_75 = l_Lean_Level_max___override(x_60, x_74);
x_76 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_75, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_75);
return x_76;
}
case 4:
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_1);
x_77 = lean_ctor_get(x_10, 0);
lean_inc(x_77);
lean_dec(x_10);
x_78 = l_Lean_Level_param___override(x_77);
x_79 = l_Lean_Level_max___override(x_60, x_78);
x_80 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_79, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_79);
return x_80;
}
default: 
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_10, 0);
lean_inc(x_81);
lean_dec(x_10);
x_82 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_60, x_81, x_4, x_7);
lean_dec(x_60);
return x_82;
}
}
}
case 3:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_9, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_9, 1);
lean_inc(x_84);
lean_dec(x_9);
x_85 = l_Lean_Level_imax___override(x_83, x_84);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_86; lean_object* x_87; 
lean_dec(x_1);
x_86 = l_Lean_Level_max___override(x_85, x_11);
x_87 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_86, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_86);
return x_87;
}
case 1:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_1);
x_88 = lean_ctor_get(x_10, 0);
lean_inc(x_88);
lean_dec(x_10);
x_89 = l_Lean_Level_succ___override(x_88);
x_90 = l_Lean_Level_max___override(x_85, x_89);
x_91 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_90, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_90);
return x_91;
}
case 2:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_1);
x_92 = lean_ctor_get(x_10, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_10, 1);
lean_inc(x_93);
lean_dec(x_10);
x_94 = l_Lean_Level_max___override(x_92, x_93);
x_95 = l_Lean_Level_max___override(x_85, x_94);
x_96 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_95, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_95);
return x_96;
}
case 3:
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_1);
x_97 = lean_ctor_get(x_10, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_10, 1);
lean_inc(x_98);
lean_dec(x_10);
x_99 = l_Lean_Level_imax___override(x_97, x_98);
x_100 = l_Lean_Level_max___override(x_85, x_99);
x_101 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_100, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_100);
return x_101;
}
case 4:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_1);
x_102 = lean_ctor_get(x_10, 0);
lean_inc(x_102);
lean_dec(x_10);
x_103 = l_Lean_Level_param___override(x_102);
x_104 = l_Lean_Level_max___override(x_85, x_103);
x_105 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_104, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_104);
return x_105;
}
default: 
{
lean_object* x_106; lean_object* x_107; 
x_106 = lean_ctor_get(x_10, 0);
lean_inc(x_106);
lean_dec(x_10);
x_107 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_85, x_106, x_4, x_7);
lean_dec(x_85);
return x_107;
}
}
}
case 4:
{
lean_object* x_108; lean_object* x_109; 
x_108 = lean_ctor_get(x_9, 0);
lean_inc(x_108);
lean_dec(x_9);
x_109 = l_Lean_Level_param___override(x_108);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_1);
x_110 = l_Lean_Level_max___override(x_109, x_11);
x_111 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_110, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_110);
return x_111;
}
case 1:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_1);
x_112 = lean_ctor_get(x_10, 0);
lean_inc(x_112);
lean_dec(x_10);
x_113 = l_Lean_Level_succ___override(x_112);
x_114 = l_Lean_Level_max___override(x_109, x_113);
x_115 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_114, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_114);
return x_115;
}
case 2:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_1);
x_116 = lean_ctor_get(x_10, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_10, 1);
lean_inc(x_117);
lean_dec(x_10);
x_118 = l_Lean_Level_max___override(x_116, x_117);
x_119 = l_Lean_Level_max___override(x_109, x_118);
x_120 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_119, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_119);
return x_120;
}
case 3:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_121 = lean_ctor_get(x_10, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_10, 1);
lean_inc(x_122);
lean_dec(x_10);
x_123 = l_Lean_Level_imax___override(x_121, x_122);
x_124 = l_Lean_Level_max___override(x_109, x_123);
x_125 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_124, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_124);
return x_125;
}
case 4:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_1);
x_126 = lean_ctor_get(x_10, 0);
lean_inc(x_126);
lean_dec(x_10);
x_127 = l_Lean_Level_param___override(x_126);
x_128 = l_Lean_Level_max___override(x_109, x_127);
x_129 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_128, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_128);
return x_129;
}
default: 
{
lean_object* x_130; lean_object* x_131; 
x_130 = lean_ctor_get(x_10, 0);
lean_inc(x_130);
lean_dec(x_10);
x_131 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_109, x_130, x_4, x_7);
lean_dec(x_109);
return x_131;
}
}
}
default: 
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_9, 0);
lean_inc(x_132);
lean_dec(x_9);
x_133 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_10, x_132, x_4, x_7);
return x_133;
}
case 5:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_134 = lean_ctor_get(x_9, 0);
lean_inc(x_134);
lean_dec(x_9);
x_135 = lean_ctor_get(x_10, 0);
lean_inc(x_135);
lean_dec(x_10);
x_136 = l_Lean_Level_mvar___override(x_134);
x_137 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_136, x_135, x_4, x_7);
lean_dec(x_136);
return x_137;
}
default: 
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_9, 0);
lean_inc(x_138);
lean_dec(x_9);
x_139 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax_solve___redArg(x_1, x_10, x_138, x_4, x_7);
lean_dec(x_10);
return x_139;
}
}
}
}
}
default: 
{
lean_object* x_140; 
lean_dec(x_1);
x_140 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_140;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_level_eq(x_1, x_3);
x_8 = lean_box(1);
if (x_7 == 0)
{
uint8_t x_9; 
x_9 = lean_level_eq(x_2, x_3);
lean_dec(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
lean_dec(x_1);
x_10 = lean_box(x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_4, x_1, x_5, x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_17 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_4, x_2, x_5, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_8);
return x_17;
}
else
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_1, x_2, x_3, x_4, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
case 2:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
lean_inc(x_10);
lean_inc(x_9);
x_11 = l_Lean_Level_max___override(x_9, x_10);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_11);
return x_12;
}
case 2:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_2, 1);
lean_inc(x_14);
lean_dec(x_2);
x_15 = lean_box(0);
switch (lean_obj_tag(x_13)) {
case 0:
{
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_10);
lean_dec(x_9);
x_16 = l_Lean_Level_max___override(x_15, x_15);
x_17 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_16, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_16);
lean_dec(x_11);
return x_17;
}
case 1:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = l_Lean_Level_succ___override(x_18);
x_20 = l_Lean_Level_max___override(x_15, x_19);
x_21 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_20, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_20);
lean_dec(x_11);
return x_21;
}
case 2:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_10);
lean_dec(x_9);
x_22 = lean_ctor_get(x_14, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Level_max___override(x_22, x_23);
x_25 = l_Lean_Level_max___override(x_15, x_24);
x_26 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_25, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_25);
lean_dec(x_11);
return x_26;
}
case 3:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_10);
lean_dec(x_9);
x_27 = lean_ctor_get(x_14, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_dec(x_14);
x_29 = l_Lean_Level_imax___override(x_27, x_28);
x_30 = l_Lean_Level_max___override(x_15, x_29);
x_31 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_30, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_30);
lean_dec(x_11);
return x_31;
}
case 4:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
x_32 = lean_ctor_get(x_14, 0);
lean_inc(x_32);
lean_dec(x_14);
x_33 = l_Lean_Level_param___override(x_32);
x_34 = l_Lean_Level_max___override(x_15, x_33);
x_35 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_34, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_34);
lean_dec(x_11);
return x_35;
}
default: 
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
x_36 = lean_ctor_get(x_14, 0);
lean_inc(x_36);
lean_dec(x_14);
x_37 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_15, x_36, x_4, x_7);
return x_37;
}
}
}
case 1:
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
lean_dec(x_13);
x_39 = l_Lean_Level_succ___override(x_38);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_10);
lean_dec(x_9);
x_40 = l_Lean_Level_max___override(x_39, x_15);
x_41 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_40, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_40);
lean_dec(x_11);
return x_41;
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
lean_dec(x_9);
x_42 = lean_ctor_get(x_14, 0);
lean_inc(x_42);
lean_dec(x_14);
x_43 = l_Lean_Level_succ___override(x_42);
x_44 = l_Lean_Level_max___override(x_39, x_43);
x_45 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_44, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_44);
lean_dec(x_11);
return x_45;
}
case 2:
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_10);
lean_dec(x_9);
x_46 = lean_ctor_get(x_14, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_14, 1);
lean_inc(x_47);
lean_dec(x_14);
x_48 = l_Lean_Level_max___override(x_46, x_47);
x_49 = l_Lean_Level_max___override(x_39, x_48);
x_50 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_49, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_49);
lean_dec(x_11);
return x_50;
}
case 3:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_10);
lean_dec(x_9);
x_51 = lean_ctor_get(x_14, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_14, 1);
lean_inc(x_52);
lean_dec(x_14);
x_53 = l_Lean_Level_imax___override(x_51, x_52);
x_54 = l_Lean_Level_max___override(x_39, x_53);
x_55 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_54, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_54);
lean_dec(x_11);
return x_55;
}
case 4:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_10);
lean_dec(x_9);
x_56 = lean_ctor_get(x_14, 0);
lean_inc(x_56);
lean_dec(x_14);
x_57 = l_Lean_Level_param___override(x_56);
x_58 = l_Lean_Level_max___override(x_39, x_57);
x_59 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_58, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_58);
lean_dec(x_11);
return x_59;
}
default: 
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_11);
x_60 = lean_ctor_get(x_14, 0);
lean_inc(x_60);
lean_dec(x_14);
x_61 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_39, x_60, x_4, x_7);
lean_dec(x_39);
return x_61;
}
}
}
case 2:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_13, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_dec(x_13);
x_64 = l_Lean_Level_max___override(x_62, x_63);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_65; lean_object* x_66; 
lean_dec(x_10);
lean_dec(x_9);
x_65 = l_Lean_Level_max___override(x_64, x_15);
x_66 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_65, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_65);
lean_dec(x_11);
return x_66;
}
case 1:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_10);
lean_dec(x_9);
x_67 = lean_ctor_get(x_14, 0);
lean_inc(x_67);
lean_dec(x_14);
x_68 = l_Lean_Level_succ___override(x_67);
x_69 = l_Lean_Level_max___override(x_64, x_68);
x_70 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_69, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_69);
lean_dec(x_11);
return x_70;
}
case 2:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_10);
lean_dec(x_9);
x_71 = lean_ctor_get(x_14, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_14, 1);
lean_inc(x_72);
lean_dec(x_14);
x_73 = l_Lean_Level_max___override(x_71, x_72);
x_74 = l_Lean_Level_max___override(x_64, x_73);
x_75 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_74, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_74);
lean_dec(x_11);
return x_75;
}
case 3:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
lean_dec(x_10);
lean_dec(x_9);
x_76 = lean_ctor_get(x_14, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_14, 1);
lean_inc(x_77);
lean_dec(x_14);
x_78 = l_Lean_Level_imax___override(x_76, x_77);
x_79 = l_Lean_Level_max___override(x_64, x_78);
x_80 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_79, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_79);
lean_dec(x_11);
return x_80;
}
case 4:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_10);
lean_dec(x_9);
x_81 = lean_ctor_get(x_14, 0);
lean_inc(x_81);
lean_dec(x_14);
x_82 = l_Lean_Level_param___override(x_81);
x_83 = l_Lean_Level_max___override(x_64, x_82);
x_84 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_83, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_83);
lean_dec(x_11);
return x_84;
}
default: 
{
lean_object* x_85; lean_object* x_86; 
lean_dec(x_11);
x_85 = lean_ctor_get(x_14, 0);
lean_inc(x_85);
lean_dec(x_14);
x_86 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_64, x_85, x_4, x_7);
lean_dec(x_64);
return x_86;
}
}
}
case 3:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_13, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_13, 1);
lean_inc(x_88);
lean_dec(x_13);
x_89 = l_Lean_Level_imax___override(x_87, x_88);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_90; lean_object* x_91; 
lean_dec(x_10);
lean_dec(x_9);
x_90 = l_Lean_Level_max___override(x_89, x_15);
x_91 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_90, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_90);
lean_dec(x_11);
return x_91;
}
case 1:
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_10);
lean_dec(x_9);
x_92 = lean_ctor_get(x_14, 0);
lean_inc(x_92);
lean_dec(x_14);
x_93 = l_Lean_Level_succ___override(x_92);
x_94 = l_Lean_Level_max___override(x_89, x_93);
x_95 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_94, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_94);
lean_dec(x_11);
return x_95;
}
case 2:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_10);
lean_dec(x_9);
x_96 = lean_ctor_get(x_14, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_14, 1);
lean_inc(x_97);
lean_dec(x_14);
x_98 = l_Lean_Level_max___override(x_96, x_97);
x_99 = l_Lean_Level_max___override(x_89, x_98);
x_100 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_99, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_99);
lean_dec(x_11);
return x_100;
}
case 3:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_10);
lean_dec(x_9);
x_101 = lean_ctor_get(x_14, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_14, 1);
lean_inc(x_102);
lean_dec(x_14);
x_103 = l_Lean_Level_imax___override(x_101, x_102);
x_104 = l_Lean_Level_max___override(x_89, x_103);
x_105 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_104, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_104);
lean_dec(x_11);
return x_105;
}
case 4:
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_10);
lean_dec(x_9);
x_106 = lean_ctor_get(x_14, 0);
lean_inc(x_106);
lean_dec(x_14);
x_107 = l_Lean_Level_param___override(x_106);
x_108 = l_Lean_Level_max___override(x_89, x_107);
x_109 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_108, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_108);
lean_dec(x_11);
return x_109;
}
default: 
{
lean_object* x_110; lean_object* x_111; 
lean_dec(x_11);
x_110 = lean_ctor_get(x_14, 0);
lean_inc(x_110);
lean_dec(x_14);
x_111 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_89, x_110, x_4, x_7);
lean_dec(x_89);
return x_111;
}
}
}
case 4:
{
lean_object* x_112; lean_object* x_113; 
x_112 = lean_ctor_get(x_13, 0);
lean_inc(x_112);
lean_dec(x_13);
x_113 = l_Lean_Level_param___override(x_112);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_10);
lean_dec(x_9);
x_114 = l_Lean_Level_max___override(x_113, x_15);
x_115 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_114, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_114);
lean_dec(x_11);
return x_115;
}
case 1:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_10);
lean_dec(x_9);
x_116 = lean_ctor_get(x_14, 0);
lean_inc(x_116);
lean_dec(x_14);
x_117 = l_Lean_Level_succ___override(x_116);
x_118 = l_Lean_Level_max___override(x_113, x_117);
x_119 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_118, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_118);
lean_dec(x_11);
return x_119;
}
case 2:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_10);
lean_dec(x_9);
x_120 = lean_ctor_get(x_14, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_14, 1);
lean_inc(x_121);
lean_dec(x_14);
x_122 = l_Lean_Level_max___override(x_120, x_121);
x_123 = l_Lean_Level_max___override(x_113, x_122);
x_124 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_123, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_123);
lean_dec(x_11);
return x_124;
}
case 3:
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_10);
lean_dec(x_9);
x_125 = lean_ctor_get(x_14, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_14, 1);
lean_inc(x_126);
lean_dec(x_14);
x_127 = l_Lean_Level_imax___override(x_125, x_126);
x_128 = l_Lean_Level_max___override(x_113, x_127);
x_129 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_128, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_128);
lean_dec(x_11);
return x_129;
}
case 4:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_10);
lean_dec(x_9);
x_130 = lean_ctor_get(x_14, 0);
lean_inc(x_130);
lean_dec(x_14);
x_131 = l_Lean_Level_param___override(x_130);
x_132 = l_Lean_Level_max___override(x_113, x_131);
x_133 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_132, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_132);
lean_dec(x_11);
return x_133;
}
default: 
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_11);
x_134 = lean_ctor_get(x_14, 0);
lean_inc(x_134);
lean_dec(x_14);
x_135 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_113, x_134, x_4, x_7);
lean_dec(x_113);
return x_135;
}
}
}
default: 
{
lean_dec(x_11);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_13, 0);
lean_inc(x_136);
lean_dec(x_13);
x_137 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_14, x_136, x_4, x_7);
return x_137;
}
case 5:
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_138 = lean_ctor_get(x_13, 0);
lean_inc(x_138);
lean_dec(x_13);
x_139 = lean_ctor_get(x_14, 0);
lean_inc(x_139);
lean_dec(x_14);
x_140 = l_Lean_Level_mvar___override(x_138);
x_141 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_140, x_139, x_4, x_7);
lean_dec(x_140);
return x_141;
}
default: 
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_13, 0);
lean_inc(x_142);
lean_dec(x_13);
x_143 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax_solve___redArg(x_9, x_10, x_14, x_142, x_4, x_7);
lean_dec(x_14);
return x_143;
}
}
}
}
}
default: 
{
lean_object* x_144; 
lean_dec(x_10);
lean_dec(x_9);
x_144 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_11);
return x_144;
}
}
}
default: 
{
lean_object* x_145; 
x_145 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_145;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("isLevelDefEq", 12, 12);
x_10 = lean_mk_string_unchecked("stuck", 5, 5);
x_11 = l_Lean_Name_mkStr3(x_8, x_9, x_10);
lean_inc(x_11);
x_12 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_11, x_3, x_4, x_5, x_6, x_7);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_39; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_5, 5);
x_39 = lean_unbox(x_14);
lean_dec(x_14);
if (x_39 == 0)
{
lean_free_object(x_12);
lean_dec(x_11);
x_17 = x_4;
x_18 = x_15;
goto block_38;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
lean_inc(x_1);
x_42 = l_Lean_MessageData_ofLevel(x_1);
lean_inc(x_41);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_42);
lean_ctor_set(x_12, 0, x_41);
x_43 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
lean_inc(x_2);
x_46 = l_Lean_MessageData_ofLevel(x_2);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_41);
x_49 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_11, x_48, x_3, x_4, x_5, x_6, x_15);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_17 = x_4;
x_18 = x_50;
goto block_38;
}
block_38:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_19 = lean_st_ref_take(x_17, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_20, 2);
lean_inc(x_24);
x_25 = lean_ctor_get(x_20, 3);
lean_inc(x_25);
x_26 = lean_ctor_get(x_3, 4);
lean_inc(x_26);
lean_inc(x_16);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_16);
lean_ctor_set(x_27, 1, x_1);
lean_ctor_set(x_27, 2, x_2);
lean_ctor_set(x_27, 3, x_26);
x_28 = l_Lean_PersistentArray_push___redArg(x_25, x_27);
x_29 = lean_ctor_get(x_20, 4);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_30, 0, x_22);
lean_ctor_set(x_30, 1, x_23);
lean_ctor_set(x_30, 2, x_24);
lean_ctor_set(x_30, 3, x_28);
lean_ctor_set(x_30, 4, x_29);
x_31 = lean_st_ref_set(x_17, x_30, x_21);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_31, 0);
lean_dec(x_33);
x_34 = lean_box(0);
lean_ctor_set(x_31, 0, x_34);
return x_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_74; 
x_51 = lean_ctor_get(x_12, 0);
x_52 = lean_ctor_get(x_12, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_12);
x_53 = lean_ctor_get(x_5, 5);
x_74 = lean_unbox(x_51);
lean_dec(x_51);
if (x_74 == 0)
{
lean_dec(x_11);
x_54 = x_4;
x_55 = x_52;
goto block_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_75 = lean_mk_string_unchecked("", 0, 0);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
lean_inc(x_1);
x_77 = l_Lean_MessageData_ofLevel(x_1);
lean_inc(x_76);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_2);
x_82 = l_Lean_MessageData_ofLevel(x_2);
x_83 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_76);
x_85 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_11, x_84, x_3, x_4, x_5, x_6, x_52);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_54 = x_4;
x_55 = x_86;
goto block_73;
}
block_73:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_56 = lean_st_ref_take(x_54, x_55);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_ctor_get(x_57, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_57, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_57, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_3, 4);
lean_inc(x_63);
lean_inc(x_53);
x_64 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_64, 0, x_53);
lean_ctor_set(x_64, 1, x_1);
lean_ctor_set(x_64, 2, x_2);
lean_ctor_set(x_64, 3, x_63);
x_65 = l_Lean_PersistentArray_push___redArg(x_62, x_64);
x_66 = lean_ctor_get(x_57, 4);
lean_inc(x_66);
lean_dec(x_57);
x_67 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_60);
lean_ctor_set(x_67, 2, x_61);
lean_ctor_set(x_67, 3, x_65);
lean_ctor_set(x_67, 4, x_66);
x_68 = lean_st_ref_set(x_54, x_67, x_58);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_68)) {
 lean_ctor_release(x_68, 0);
 lean_ctor_release(x_68, 1);
 x_70 = x_68;
} else {
 lean_dec_ref(x_68);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
if (lean_is_scalar(x_70)) {
 x_72 = lean_alloc_ctor(0, 2, 0);
} else {
 x_72 = x_70;
}
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 5:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_LMVarId_getLevel(x_9, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_LMVarId_getLevel(x_2, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_nat_dec_lt(x_15, x_11);
lean_dec(x_11);
lean_dec(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_13, 0, x_17);
return x_13;
}
else
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_18 = lean_ctor_get(x_13, 0);
x_19 = lean_ctor_get(x_13, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_13);
x_20 = lean_nat_dec_lt(x_18, x_11);
lean_dec(x_11);
lean_dec(x_18);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_11);
x_23 = !lean_is_exclusive(x_13);
if (x_23 == 0)
{
return x_13;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_13, 0);
x_25 = lean_ctor_get(x_13, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_13);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
uint8_t x_27; 
lean_dec(x_2);
x_27 = !lean_is_exclusive(x_10);
if (x_27 == 0)
{
return x_10;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_10, 0);
x_29 = lean_ctor_get(x_10, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_10);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
default: 
{
lean_object* x_31; 
lean_dec(x_2);
x_31 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax___lam__0(x_1, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_14; 
x_14 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
if (x_14 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
x_10 = x_9;
goto block_13;
}
else
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
lean_inc(x_2);
lean_inc(x_1);
x_15 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxSelfMax(x_1, x_2, x_5, x_6, x_7, x_8, x_9);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_tryApproxMaxMax(x_1, x_2, x_5, x_6, x_7, x_8, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_unbox(x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_10 = x_22;
goto block_13;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
lean_dec(x_24);
x_25 = lean_box(1);
lean_ctor_set(x_19, 0, x_25);
return x_19;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_dec(x_19);
x_27 = lean_box(1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_2);
lean_dec(x_1);
x_29 = !lean_is_exclusive(x_15);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_15, 0);
lean_dec(x_30);
x_31 = lean_box(1);
lean_ctor_set(x_15, 0, x_31);
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 1);
lean_inc(x_32);
lean_dec(x_15);
x_33 = lean_box(1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(2);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_42; 
x_42 = l_Lean_Level_isParam(x_2);
if (x_42 == 0)
{
uint8_t x_43; 
x_43 = l_Lean_Level_isMVar(x_1);
if (x_43 == 0)
{
x_8 = x_43;
goto block_41;
}
else
{
uint8_t x_44; 
x_44 = l_Lean_Level_occurs(x_1, x_2);
x_8 = x_44;
goto block_41;
}
}
else
{
lean_object* x_45; lean_object* x_46; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
block_41:
{
if (x_8 == 0)
{
lean_object* x_9; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = l_Lean_Meta_decLevel_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(2);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_ctor_get(x_10, 0);
lean_inc(x_18);
lean_dec(x_10);
x_19 = lean_is_level_def_eq(x_1, x_18, x_3, x_4, x_5, x_6, x_17);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; uint8_t x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_unbox(x_21);
lean_dec(x_21);
x_23 = l_Bool_toLBool(x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_19, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_25 = lean_ctor_get(x_19, 0);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_19);
x_27 = lean_unbox(x_25);
lean_dec(x_25);
x_28 = l_Bool_toLBool(x_27);
x_29 = lean_box(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_26);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_19);
if (x_31 == 0)
{
return x_19;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_9);
if (x_35 == 0)
{
return x_9;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_9, 0);
x_37 = lean_ctor_get(x_9, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_9);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_box(2);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_7);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_3);
x_10 = l_Lean_LMVarId_isReadOnly(x_3, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
lean_inc(x_1);
x_14 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_isMVarWithGreaterDepth(x_1, x_3, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_21; uint8_t x_35; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_17 = x_14;
} else {
 lean_dec_ref(x_14);
 x_17 = lean_box(0);
}
x_35 = lean_unbox(x_15);
lean_dec(x_15);
if (x_35 == 0)
{
uint8_t x_36; 
x_36 = l_Lean_Level_occurs(x_2, x_1);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_37 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_38 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_37, x_1, x_6, x_16);
lean_dec(x_6);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(1);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
else
{
uint8_t x_45; 
x_45 = l_Lean_Level_isMax(x_1);
if (x_45 == 0)
{
x_21 = x_45;
goto block_34;
}
else
{
uint8_t x_46; 
x_46 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_strictOccursMax(x_2, x_1);
if (x_46 == 0)
{
x_21 = x_45;
goto block_34;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
goto block_20;
}
}
}
}
else
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
x_47 = l_Lean_Level_mvarId_x21(x_1);
lean_dec(x_1);
x_48 = l_Lean_assignLevelMVar___at_____private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax_spec__1___redArg(x_47, x_2, x_6, x_16);
lean_dec(x_6);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
x_51 = lean_box(1);
lean_ctor_set(x_48, 0, x_51);
return x_48;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
lean_dec(x_48);
x_53 = lean_box(1);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_box(2);
if (lean_is_scalar(x_17)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_17;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
block_34:
{
if (x_21 == 0)
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
goto block_20;
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_17);
x_22 = l_Lean_Level_mvarId_x21(x_2);
lean_dec(x_2);
x_23 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solveSelfMax(x_22, x_1, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = lean_box(1);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = lean_box(1);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_23);
if (x_30 == 0)
{
return x_23;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_23, 0);
x_32 = lean_ctor_get(x_23, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_23);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_14);
if (x_55 == 0)
{
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
uint8_t x_59; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_10);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_10, 0);
lean_dec(x_60);
x_61 = lean_box(2);
lean_ctor_set(x_10, 0, x_61);
return x_10;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_10, 1);
lean_inc(x_62);
lean_dec(x_10);
x_63 = lean_box(2);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_62);
return x_64;
}
}
}
else
{
uint8_t x_65; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_65 = !lean_is_exclusive(x_10);
if (x_65 == 0)
{
return x_10;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_10, 0);
x_67 = lean_ctor_get(x_10, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_10);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_25; 
x_25 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_2, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_25;
}
case 1:
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_7);
return x_27;
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 1);
lean_inc(x_29);
lean_dec(x_2);
x_30 = lean_box(0);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_31 = lean_is_level_def_eq(x_30, x_28, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = x_31;
goto block_24;
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_is_level_def_eq(x_30, x_29, x_3, x_4, x_5, x_6, x_34);
x_8 = x_35;
goto block_24;
}
}
else
{
lean_dec(x_29);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_8 = x_31;
goto block_24;
}
}
case 3:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
lean_dec(x_2);
x_37 = lean_box(0);
x_38 = lean_is_level_def_eq(x_37, x_36, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 0);
x_41 = lean_unbox(x_40);
lean_dec(x_40);
x_42 = l_Bool_toLBool(x_41);
x_43 = lean_box(x_42);
lean_ctor_set(x_38, 0, x_43);
return x_38;
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; 
x_44 = lean_ctor_get(x_38, 0);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_38);
x_46 = lean_unbox(x_44);
lean_dec(x_44);
x_47 = l_Bool_toLBool(x_46);
x_48 = lean_box(x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_45);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_38);
if (x_50 == 0)
{
return x_38;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_38, 0);
x_52 = lean_ctor_get(x_38, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_38);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
case 4:
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_box(0);
lean_inc(x_2);
x_55 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_54, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
default: 
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_2, 0);
lean_inc(x_56);
lean_dec(x_2);
x_57 = lean_box(0);
x_58 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(x_57, x_56, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_56);
return x_58;
}
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_1, 0);
lean_inc(x_59);
lean_dec(x_1);
x_60 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__2(x_59, x_2, x_3, x_4, x_5, x_6, x_7);
return x_60;
}
case 5:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_ctor_get(x_2, 0);
lean_inc(x_62);
lean_dec(x_2);
x_63 = l_Lean_Level_succ___override(x_61);
x_64 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(x_63, x_62, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_62);
lean_dec(x_63);
return x_64;
}
default: 
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_1, 0);
lean_inc(x_65);
lean_dec(x_1);
x_66 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__2(x_65, x_2, x_3, x_4, x_5, x_6, x_7);
return x_66;
}
}
}
case 2:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_1, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 1);
lean_inc(x_68);
x_69 = l_Lean_Level_max___override(x_67, x_68);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_70; 
x_70 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_69, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_69);
return x_70;
}
case 5:
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_ctor_get(x_2, 0);
lean_inc(x_71);
lean_dec(x_2);
x_72 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(x_69, x_71, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_71);
lean_dec(x_69);
return x_72;
}
default: 
{
lean_object* x_73; 
lean_inc(x_2);
x_73 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_69, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_69);
lean_dec(x_2);
return x_73;
}
}
}
case 3:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_1, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 1);
lean_inc(x_75);
x_76 = l_Lean_Level_imax___override(x_74, x_75);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_77; 
x_77 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_76, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_76);
return x_77;
}
case 5:
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
lean_dec(x_2);
x_79 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(x_76, x_78, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_78);
lean_dec(x_76);
return x_79;
}
default: 
{
lean_object* x_80; 
lean_inc(x_2);
x_80 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_76, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_76);
lean_dec(x_2);
return x_80;
}
}
}
case 4:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = l_Lean_Level_param___override(x_81);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_83; 
x_83 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_82, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_82);
return x_83;
}
case 5:
{
lean_object* x_84; lean_object* x_85; 
lean_dec(x_1);
x_84 = lean_ctor_get(x_2, 0);
lean_inc(x_84);
lean_dec(x_2);
x_85 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(x_82, x_84, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_84);
lean_dec(x_82);
return x_85;
}
default: 
{
lean_object* x_86; 
lean_inc(x_2);
x_86 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_82, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_82);
lean_dec(x_2);
return x_86;
}
}
}
default: 
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_1, 0);
lean_inc(x_87);
x_88 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__3(x_2, x_1, x_87, x_2, x_3, x_4, x_5, x_6, x_7);
return x_88;
}
else
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
lean_inc(x_2);
x_90 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__3(x_2, x_1, x_89, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_90;
}
}
}
block_24:
{
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
x_12 = l_Bool_toLBool(x_11);
x_13 = lean_box(x_12);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
else
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; 
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_8);
x_16 = lean_unbox(x_14);
lean_dec(x_14);
x_17 = l_Bool_toLBool(x_16);
x_18 = lean_box(x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_15);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_8);
if (x_20 == 0)
{
return x_8;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_8, 0);
x_22 = lean_ctor_get(x_8, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_8);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_11 = l_instMonadEIO(lean_box(0));
x_12 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
lean_inc(x_14);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_24, 0, lean_box(0));
lean_closure_set(x_24, 1, lean_box(0));
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
lean_inc(x_26);
lean_inc(x_23);
lean_inc(x_20);
x_27 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 2, x_20);
lean_ctor_set(x_27, 3, x_23);
lean_ctor_set(x_27, 4, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_33, 0, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_20);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_37, 0, x_23);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_26);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_7);
lean_ctor_set(x_41, 2, x_36);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_8);
x_43 = l_instInhabitedBool;
x_44 = lean_box(x_43);
x_45 = l_instInhabitedOfMonad___redArg(x_42, x_44);
x_46 = lean_panic_fn(x_45, x_1);
x_47 = lean_apply_5(x_46, x_2, x_3, x_4, x_5, x_6);
return x_47;
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_st_ref_get(x_3, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_12, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_dec(x_11);
lean_free_object(x_7);
x_14 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_15 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_16 = lean_unsigned_to_nat(425u);
x_17 = lean_unsigned_to_nat(14u);
x_18 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_19 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_14, x_15, x_16, x_17, x_18);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
x_20 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0_spec__0(x_19, x_2, x_3, x_4, x_5, x_10);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_dec(x_11);
x_23 = lean_nat_dec_le(x_22, x_21);
lean_dec(x_21);
lean_dec(x_22);
x_24 = lean_box(x_23);
lean_ctor_set(x_7, 0, x_24);
return x_7;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_25 = lean_ctor_get(x_7, 0);
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_7);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
x_29 = l_Lean_PersistentHashMap_find_x3f___at___Lean_getLevelMVarAssignmentExp_spec__0___redArg(x_28, x_1);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_27);
x_30 = lean_mk_string_unchecked("Lean.MetavarContext", 19, 19);
x_31 = lean_mk_string_unchecked("Lean.isLevelMVarAssignable", 26, 26);
x_32 = lean_unsigned_to_nat(425u);
x_33 = lean_unsigned_to_nat(14u);
x_34 = lean_mk_string_unchecked("unknown universe metavariable", 29, 29);
x_35 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_30, x_31, x_32, x_33, x_34);
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = l_panic___at___Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0_spec__0(x_35, x_2, x_3, x_4, x_5, x_26);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = lean_ctor_get(x_29, 0);
lean_inc(x_37);
lean_dec(x_29);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_dec(x_27);
x_39 = lean_nat_dec_le(x_38, x_37);
lean_dec(x_37);
lean_dec(x_38);
x_40 = lean_box(x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_26);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; uint8_t x_16; 
x_16 = l_Lean_Level_hasMVar(x_1);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_box(x_16);
lean_inc(x_7);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_7);
x_8 = x_18;
x_9 = x_16;
x_10 = x_7;
goto block_15;
}
else
{
lean_object* x_19; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_19 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
x_22 = lean_unbox(x_20);
lean_dec(x_20);
x_8 = x_19;
x_9 = x_22;
x_10 = x_21;
goto block_15;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_19;
}
}
block_15:
{
if (x_9 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
x_11 = l_Lean_Level_hasMVar(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_2, x_3, x_4, x_5, x_6, x_10);
return x_14;
}
}
else
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lean_Level_hasMVar(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_6);
return x_10;
}
else
{
x_1 = x_7;
goto _start;
}
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___lam__0(x_12, x_13, x_2, x_3, x_4, x_5, x_6);
return x_14;
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_1, 0);
x_16 = lean_ctor_get(x_1, 1);
x_17 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___lam__0(x_15, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
case 5:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_1, 0);
x_19 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0(x_18, x_2, x_3, x_4, x_5, x_6);
return x_19;
}
default: 
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_mk_string_unchecked("", 0, 0);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_exceptBoolEmoji(lean_box(0), x_3);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
lean_inc(x_10);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked(" ", 1, 1);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofLevel(x_1);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_MessageData_ofLevel(x_2);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_10);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_8);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_50; uint8_t x_51; lean_object* x_55; 
if (x_1 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
lean_inc(x_2);
x_75 = l_Lean_instantiateLevelMVars___at___Lean_Meta_normalizeLevel_spec__0___redArg(x_2, x_8, x_11);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
lean_inc(x_3);
x_78 = l_Lean_instantiateLevelMVars___at___Lean_Meta_normalizeLevel_spec__0___redArg(x_3, x_8, x_77);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = l_Lean_Level_normalize(x_76);
lean_dec(x_76);
x_82 = l_Lean_Level_normalize(x_79);
lean_dec(x_79);
x_83 = lean_level_eq(x_2, x_81);
if (x_83 == 0)
{
lean_object* x_84; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_84 = lean_is_level_def_eq(x_81, x_82, x_7, x_8, x_9, x_10, x_80);
return x_84;
}
else
{
uint8_t x_85; 
x_85 = lean_level_eq(x_3, x_82);
if (x_85 == 0)
{
lean_object* x_86; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_86 = lean_is_level_def_eq(x_81, x_82, x_7, x_8, x_9, x_10, x_80);
return x_86;
}
else
{
lean_object* x_87; 
lean_dec(x_82);
lean_dec(x_81);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_87 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_2, x_3, x_7, x_8, x_9, x_10, x_80);
if (lean_obj_tag(x_87) == 0)
{
uint8_t x_88; 
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; uint8_t x_93; uint8_t x_94; 
x_89 = lean_ctor_get(x_87, 0);
x_90 = lean_ctor_get(x_87, 1);
x_91 = lean_box(2);
x_92 = lean_unbox(x_89);
x_93 = lean_unbox(x_91);
x_94 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_92, x_93);
if (x_94 == 0)
{
lean_object* x_95; uint8_t x_96; uint8_t x_97; uint8_t x_98; lean_object* x_99; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_95 = lean_box(1);
x_96 = lean_unbox(x_89);
lean_dec(x_89);
x_97 = lean_unbox(x_95);
x_98 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_96, x_97);
x_99 = lean_box(x_98);
lean_ctor_set(x_87, 0, x_99);
return x_87;
}
else
{
lean_object* x_100; 
lean_free_object(x_87);
lean_dec(x_89);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_3);
x_100 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_3, x_2, x_7, x_8, x_9, x_10, x_90);
if (lean_obj_tag(x_100) == 0)
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; uint8_t x_104; uint8_t x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_100, 0);
x_103 = lean_ctor_get(x_100, 1);
x_104 = lean_unbox(x_102);
x_105 = lean_unbox(x_91);
x_106 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; uint8_t x_108; uint8_t x_109; uint8_t x_110; lean_object* x_111; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_107 = lean_box(1);
x_108 = lean_unbox(x_102);
lean_dec(x_102);
x_109 = lean_unbox(x_107);
x_110 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_108, x_109);
x_111 = lean_box(x_110);
lean_ctor_set(x_100, 0, x_111);
return x_100;
}
else
{
lean_object* x_112; 
lean_free_object(x_100);
lean_dec(x_102);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_112 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_2, x_7, x_8, x_9, x_10, x_103);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; uint8_t x_114; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_unbox(x_113);
lean_dec(x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
lean_dec(x_112);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_116 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_3, x_7, x_8, x_9, x_10, x_115);
x_55 = x_116;
goto block_74;
}
else
{
x_55 = x_112;
goto block_74;
}
}
else
{
x_55 = x_112;
goto block_74;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; uint8_t x_119; uint8_t x_120; uint8_t x_121; 
x_117 = lean_ctor_get(x_100, 0);
x_118 = lean_ctor_get(x_100, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_100);
x_119 = lean_unbox(x_117);
x_120 = lean_unbox(x_91);
x_121 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_119, x_120);
if (x_121 == 0)
{
lean_object* x_122; uint8_t x_123; uint8_t x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_122 = lean_box(1);
x_123 = lean_unbox(x_117);
lean_dec(x_117);
x_124 = lean_unbox(x_122);
x_125 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_123, x_124);
x_126 = lean_box(x_125);
x_127 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_118);
return x_127;
}
else
{
lean_object* x_128; 
lean_dec(x_117);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_128 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_2, x_7, x_8, x_9, x_10, x_118);
if (lean_obj_tag(x_128) == 0)
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_unbox(x_129);
lean_dec(x_129);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_128, 1);
lean_inc(x_131);
lean_dec(x_128);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_132 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_3, x_7, x_8, x_9, x_10, x_131);
x_55 = x_132;
goto block_74;
}
else
{
x_55 = x_128;
goto block_74;
}
}
else
{
x_55 = x_128;
goto block_74;
}
}
}
}
else
{
uint8_t x_133; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_133 = !lean_is_exclusive(x_100);
if (x_133 == 0)
{
return x_100;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_134 = lean_ctor_get(x_100, 0);
x_135 = lean_ctor_get(x_100, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_100);
x_136 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_136, 0, x_134);
lean_ctor_set(x_136, 1, x_135);
return x_136;
}
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; uint8_t x_141; uint8_t x_142; 
x_137 = lean_ctor_get(x_87, 0);
x_138 = lean_ctor_get(x_87, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_87);
x_139 = lean_box(2);
x_140 = lean_unbox(x_137);
x_141 = lean_unbox(x_139);
x_142 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_140, x_141);
if (x_142 == 0)
{
lean_object* x_143; uint8_t x_144; uint8_t x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_143 = lean_box(1);
x_144 = lean_unbox(x_137);
lean_dec(x_137);
x_145 = lean_unbox(x_143);
x_146 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_144, x_145);
x_147 = lean_box(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_138);
return x_148;
}
else
{
lean_object* x_149; 
lean_dec(x_137);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_3);
x_149 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_solve(x_3, x_2, x_7, x_8, x_9, x_10, x_138);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; uint8_t x_153; uint8_t x_154; uint8_t x_155; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_152 = x_149;
} else {
 lean_dec_ref(x_149);
 x_152 = lean_box(0);
}
x_153 = lean_unbox(x_150);
x_154 = lean_unbox(x_139);
x_155 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_153, x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; uint8_t x_158; uint8_t x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_156 = lean_box(1);
x_157 = lean_unbox(x_150);
lean_dec(x_150);
x_158 = lean_unbox(x_156);
x_159 = l___private_Lean_Data_LBool_0__Lean_beqLBool____x40_Lean_Data_LBool___hyg_18_(x_157, x_158);
x_160 = lean_box(x_159);
if (lean_is_scalar(x_152)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_152;
}
lean_ctor_set(x_161, 0, x_160);
lean_ctor_set(x_161, 1, x_151);
return x_161;
}
else
{
lean_object* x_162; 
lean_dec(x_152);
lean_dec(x_150);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_162 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_2, x_7, x_8, x_9, x_10, x_151);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; uint8_t x_164; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_unbox(x_163);
lean_dec(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_162, 1);
lean_inc(x_165);
lean_dec(x_162);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_166 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_3, x_7, x_8, x_9, x_10, x_165);
x_55 = x_166;
goto block_74;
}
else
{
x_55 = x_162;
goto block_74;
}
}
else
{
x_55 = x_162;
goto block_74;
}
}
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_167 = lean_ctor_get(x_149, 0);
lean_inc(x_167);
x_168 = lean_ctor_get(x_149, 1);
lean_inc(x_168);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_169 = x_149;
} else {
 lean_dec_ref(x_149);
 x_169 = lean_box(0);
}
if (lean_is_scalar(x_169)) {
 x_170 = lean_alloc_ctor(1, 2, 0);
} else {
 x_170 = x_169;
}
lean_ctor_set(x_170, 0, x_167);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
}
}
else
{
uint8_t x_171; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_171 = !lean_is_exclusive(x_87);
if (x_171 == 0)
{
return x_87;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_87, 0);
x_173 = lean_ctor_get(x_87, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_87);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
}
else
{
lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
x_175 = l_Lean_Level_getOffset(x_2);
lean_dec(x_2);
x_176 = l_Lean_Level_getOffset(x_3);
lean_dec(x_3);
x_177 = lean_nat_dec_eq(x_175, x_176);
lean_dec(x_176);
lean_dec(x_175);
x_178 = lean_box(x_177);
x_179 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_179, 0, x_178);
lean_ctor_set(x_179, 1, x_11);
return x_179;
}
block_49:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_mk_string_unchecked("stuck", 5, 5);
x_14 = l_Lean_Name_mkStr3(x_4, x_5, x_13);
lean_inc(x_14);
x_15 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_14, x_7, x_8, x_9, x_10, x_12);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = l_Lean_Meta_throwIsDefEqStuck___redArg(x_18);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_15);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_21 = lean_ctor_get(x_15, 1);
x_22 = lean_ctor_get(x_15, 0);
lean_dec(x_22);
x_23 = lean_mk_string_unchecked("", 0, 0);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = l_Lean_MessageData_ofLevel(x_2);
lean_inc(x_24);
lean_ctor_set_tag(x_15, 7);
lean_ctor_set(x_15, 1, x_25);
lean_ctor_set(x_15, 0, x_24);
x_26 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_15);
lean_ctor_set(x_28, 1, x_27);
x_29 = l_Lean_MessageData_ofLevel(x_3);
x_30 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_24);
x_32 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_14, x_31, x_7, x_8, x_9, x_10, x_21);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = l_Lean_Meta_throwIsDefEqStuck___redArg(x_33);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_35 = lean_ctor_get(x_15, 1);
lean_inc(x_35);
lean_dec(x_15);
x_36 = lean_mk_string_unchecked("", 0, 0);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofLevel(x_2);
lean_inc(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked(" =\?= ", 5, 5);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_MessageData_ofLevel(x_3);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_37);
x_46 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_14, x_45, x_7, x_8, x_9, x_10, x_35);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = l_Lean_Meta_throwIsDefEqStuck___redArg(x_47);
return x_48;
}
}
}
block_54:
{
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_52 = lean_box(x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_50);
return x_53;
}
else
{
x_12 = x_50;
goto block_49;
}
}
block_74:
{
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; uint8_t x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_56);
lean_dec(x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
lean_dec(x_55);
x_59 = l_Lean_Meta_getConfig(x_7, x_8, x_9, x_10, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get_uint8(x_60, 4);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_50 = x_62;
x_51 = x_61;
goto block_54;
}
else
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = l_Lean_Level_isMVar(x_2);
if (x_64 == 0)
{
uint8_t x_65; 
x_65 = l_Lean_Level_isMVar(x_3);
x_50 = x_63;
x_51 = x_65;
goto block_54;
}
else
{
x_12 = x_63;
goto block_49;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; uint8_t x_68; 
lean_dec(x_5);
lean_dec(x_4);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
lean_dec(x_55);
x_67 = l___private_Lean_Meta_LevelDefEq_0__Lean_Meta_postponeIsLevelDefEq(x_2, x_3, x_7, x_8, x_9, x_10, x_66);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_67, 0);
lean_dec(x_69);
x_70 = lean_box(x_6);
lean_ctor_set(x_67, 0, x_70);
return x_67;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_box(x_6);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_55;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed), 8, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = lean_mk_string_unchecked("isLevelDefEq", 12, 12);
lean_inc(x_10);
lean_inc(x_9);
x_11 = l_Lean_Name_mkStr2(x_9, x_10);
x_12 = l_Lean_Level_getLevelOffset(x_1);
x_13 = l_Lean_Level_getLevelOffset(x_2);
x_14 = lean_level_eq(x_12, x_13);
lean_dec(x_13);
lean_dec(x_12);
x_15 = lean_box(1);
x_16 = lean_box(x_14);
x_17 = lean_alloc_closure((void*)(l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed), 11, 6);
lean_closure_set(x_17, 0, x_16);
lean_closure_set(x_17, 1, x_1);
lean_closure_set(x_17, 2, x_2);
lean_closure_set(x_17, 3, x_9);
lean_closure_set(x_17, 4, x_10);
lean_closure_set(x_17, 5, x_15);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = lean_unbox(x_15);
x_20 = l_Lean_withTraceNode___at___Lean_Meta_processPostponed_spec__0(lean_box(0), x_11, x_8, x_17, x_19, x_18, x_3, x_4, x_5, x_6, x_7);
return x_20;
}
}
LEAN_EXPORT lean_object* lean_is_level_def_eq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isLevelDefEqAuxImpl___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
case 1:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
lean_inc(x_9);
x_10 = l_Lean_Level_succ___override(x_9);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_11; 
lean_dec(x_9);
x_11 = l_Lean_Meta_isLevelDefEqAuxImpl___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_is_level_def_eq(x_9, x_12, x_3, x_4, x_5, x_6, x_7);
return x_13;
}
default: 
{
lean_object* x_14; 
lean_dec(x_9);
x_14 = l_Lean_Meta_isLevelDefEqAuxImpl___lam__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7);
return x_14;
}
}
}
default: 
{
lean_object* x_15; 
x_15 = l_Lean_Meta_isLevelDefEqAuxImpl___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isLevelMVarAssignable___at___Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_hasAssignableLevelMVar___at___Lean_Meta_isLevelDefEqAuxImpl_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_isLevelDefEqAuxImpl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isLevelDefEqAuxImpl___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = lean_unbox(x_6);
lean_dec(x_6);
x_14 = l_Lean_Meta_isLevelDefEqAuxImpl___lam__1(x_12, x_2, x_3, x_4, x_5, x_13, x_7, x_8, x_9, x_10, x_11);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_1927_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_2 = lean_mk_string_unchecked("Meta", 4, 4);
x_3 = lean_mk_string_unchecked("isLevelDefEq", 12, 12);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("initFn", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("_@", 2, 2);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = l_Lean_Name_str___override(x_13, x_7);
lean_inc(x_2);
x_15 = l_Lean_Name_str___override(x_14, x_2);
x_16 = lean_mk_string_unchecked("LevelDefEq", 10, 10);
x_17 = l_Lean_Name_str___override(x_15, x_16);
x_18 = lean_mk_string_unchecked("_hyg", 4, 4);
x_19 = l_Lean_Name_str___override(x_17, x_18);
x_20 = lean_unsigned_to_nat(1927u);
x_21 = l_Lean_Name_num___override(x_19, x_20);
x_22 = lean_unbox(x_5);
lean_inc(x_21);
x_23 = l_Lean_registerTraceClass(x_4, x_22, x_21, x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_mk_string_unchecked("stuck", 5, 5);
x_26 = l_Lean_Name_mkStr3(x_2, x_3, x_25);
x_27 = lean_box(1);
x_28 = lean_unbox(x_27);
x_29 = l_Lean_registerTraceClass(x_26, x_28, x_21, x_24);
return x_29;
}
else
{
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
return x_23;
}
}
}
lean_object* initialize_Lean_Util_CollectMVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DecLevel(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_LevelDefEq(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Util_CollectMVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DecLevel(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_LevelDefEq___hyg_1927_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
