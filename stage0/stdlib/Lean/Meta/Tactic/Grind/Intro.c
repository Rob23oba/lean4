// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Intro
// Imports: Init.Grind.Lemmas Lean.Meta.Tactic.Assert Lean.Meta.Tactic.Grind.Simp Lean.Meta.Tactic.Grind.Types Lean.Meta.Tactic.Grind.Cases Lean.Meta.Tactic.Grind.CasesMatch Lean.Meta.Tactic.Grind.Injection Lean.Meta.Tactic.Grind.Core Lean.Meta.Tactic.Grind.Combinators
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingName_x21(lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_Result_getProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_injection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object*, lean_object*);
uint32_t lean_string_utf8_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedIntroResult;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkFreshExprMVarAt(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_expandLet(lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instBEqENodeKey;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object**);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLet(lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instHashableInt___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* l_Lean_MVarId_getTag(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isLetFun(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Meta_Grind_intros_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkApp4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_instBEqProd___redArg(lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_empty(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_Grind_CasesTypes_isEagerSplit(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_anyAux___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_add(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint32_t lean_uint32_of_nat(lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Lean_MVarId_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_Meta_Grind_addNewEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_exfalso(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_value(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getLevel(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_Grind_instBEqCongrKey___lam__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instHashablePreInstance;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instHashableENodeKey;
lean_object* l_instBEqOfDecidableEq___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_saveCases(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_Meta_Grind_GrindTactic_iterate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assign___at___Lean_Meta_Grind_closeGoal_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MVarId_assert(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalContext_mkLocalDecl(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Meta_Grind_instHashableCongrKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Queue_dequeue_x3f___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_addHypothesis(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instHashableOrigin;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_hasMacroScopes(lean_object*);
lean_object* l_String_findAux(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingDomain_x21(lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Int_instDecidableEq___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cheapCasesOnly(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instBEqPreInstance;
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
uint8_t l_Lean_Meta_Simp_isEqnThmHypothesis(lean_object*);
extern lean_object* l_Lean_Expr_instHashable;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__1___boxed(lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_MVarId_intro(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object**);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_MVarId_byContra_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isClass_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Meta_Grind_intros_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
lean_object* l_instHashableProd___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Meta_Grind_shareCommon___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bindingBody_x21(lean_object*);
lean_object* l_Lean_Meta_getLocalInstances___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Grind_instBEqOrigin__1;
lean_object* l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_canon(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* l_Lean_Meta_Grind_preprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_cases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Char_utf8Size(uint32_t);
LEAN_EXPORT uint8_t l_String_anyAux___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letFun_x3f(lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_markAsPreMatchCond(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqPos(lean_object*, lean_object*);
uint8_t l_Lean_Expr_bindingInfo_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_instDecidableEqChar(uint32_t, uint32_t);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint32_t l_Char_ofNat(lean_object*);
extern lean_object* l_Lean_instHashableName;
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedIntroResult() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; uint8_t x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_99; 
x_1 = lean_box(0);
x_2 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_3 = l_Lean_Expr_instHashable;
x_4 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_4);
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_4);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_4);
lean_inc(x_6);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_6);
lean_ctor_set(x_7, 2, x_6);
x_8 = l_Lean_Meta_Grind_instBEqENodeKey;
x_9 = l_Lean_Meta_Grind_instHashableENodeKey;
lean_inc(x_4);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_4);
x_11 = l_Array_empty(lean_box(0));
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_box(0);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_usize_of_nat(x_14);
lean_inc(x_11);
x_16 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_16, 2, x_13);
lean_ctor_set(x_16, 3, x_13);
lean_ctor_set_usize(x_16, 4, x_15);
lean_inc(x_4);
x_17 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_17, 0, x_4);
lean_inc(x_10);
x_18 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqCongrKey___lam__0___boxed), 3, 1);
lean_closure_set(x_18, 0, x_10);
lean_inc(x_10);
x_19 = l_Lean_Meta_Grind_instHashableCongrKey(x_10);
x_20 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_18, x_19);
lean_dec(x_19);
lean_dec(x_18);
lean_inc(x_4);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_4);
x_22 = lean_box(0);
x_23 = l_Std_Queue_empty(lean_box(0));
lean_inc(x_4);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_4);
x_25 = l_Lean_Meta_Grind_instBEqPreInstance;
x_26 = l_Lean_Meta_Grind_instHashablePreInstance;
x_27 = l_Lean_Name_instBEq;
x_28 = l_Lean_instHashableName;
x_29 = l_Lean_Meta_Grind_instBEqOrigin__1;
x_30 = l_Lean_Meta_Grind_instHashableOrigin;
lean_inc(x_4);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_4);
x_32 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_29, x_30);
lean_inc(x_4);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_4);
lean_inc(x_32);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_32);
lean_ctor_set(x_34, 2, x_32);
lean_ctor_set(x_34, 3, x_33);
lean_inc(x_11);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_11);
lean_inc(x_11);
x_36 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_11);
lean_ctor_set(x_36, 2, x_13);
lean_ctor_set(x_36, 3, x_13);
lean_ctor_set_usize(x_36, 4, x_15);
x_37 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_25, x_26);
x_38 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_27, x_28);
lean_inc(x_38);
lean_inc(x_36);
x_39 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_13);
lean_ctor_set(x_39, 2, x_36);
lean_ctor_set(x_39, 3, x_36);
lean_ctor_set(x_39, 4, x_13);
lean_ctor_set(x_39, 5, x_13);
lean_ctor_set(x_39, 6, x_37);
lean_ctor_set(x_39, 7, x_13);
lean_ctor_set(x_39, 8, x_38);
lean_inc(x_4);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_4);
x_41 = lean_box(0);
x_42 = lean_unsigned_to_nat(8u);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_shiftl(x_42, x_43);
x_45 = lean_unsigned_to_nat(3u);
x_46 = lean_nat_div(x_44, x_45);
lean_dec(x_44);
x_47 = l_Nat_nextPowerOfTwo(x_46);
lean_dec(x_46);
x_48 = lean_box(0);
lean_inc(x_47);
x_49 = lean_mk_array(x_47, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_14);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_8, x_9);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = lean_mk_array(x_47, x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_14);
lean_ctor_set(x_55, 1, x_54);
lean_inc(x_4);
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_4);
x_57 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_57, 0, x_13);
lean_ctor_set(x_57, 1, x_40);
lean_ctor_set(x_57, 2, x_41);
lean_ctor_set(x_57, 3, x_50);
lean_ctor_set(x_57, 4, x_51);
lean_ctor_set(x_57, 5, x_52);
lean_ctor_set(x_57, 6, x_41);
lean_ctor_set(x_57, 7, x_55);
lean_ctor_set(x_57, 8, x_56);
lean_inc(x_4);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_4);
lean_inc(x_4);
x_59 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_59, 0, x_4);
lean_inc(x_4);
x_60 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_60, 0, x_4);
lean_inc(x_11);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_11);
lean_inc(x_11);
x_62 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_11);
lean_ctor_set(x_62, 2, x_13);
lean_ctor_set(x_62, 3, x_13);
lean_ctor_set_usize(x_62, 4, x_15);
lean_inc(x_11);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_11);
lean_inc(x_11);
x_64 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_11);
lean_ctor_set(x_64, 2, x_13);
lean_ctor_set(x_64, 3, x_13);
lean_ctor_set_usize(x_64, 4, x_15);
x_65 = lean_box(0);
lean_inc(x_62);
lean_inc(x_58);
lean_inc(x_16);
x_66 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_66, 0, x_16);
lean_ctor_set(x_66, 1, x_58);
lean_ctor_set(x_66, 2, x_59);
lean_ctor_set(x_66, 3, x_60);
lean_ctor_set(x_66, 4, x_62);
lean_ctor_set(x_66, 5, x_62);
lean_ctor_set(x_66, 6, x_64);
lean_ctor_set(x_66, 7, x_65);
lean_inc(x_4);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_4);
lean_inc(x_4);
x_68 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_68, 0, x_4);
lean_inc(x_11);
x_69 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_69, 0, x_11);
lean_inc(x_11);
x_70 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_11);
lean_ctor_set(x_70, 2, x_13);
lean_ctor_set(x_70, 3, x_13);
lean_ctor_set_usize(x_70, 4, x_15);
lean_inc(x_11);
x_71 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_71, 0, x_11);
lean_inc(x_11);
x_72 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_11);
lean_ctor_set(x_72, 2, x_13);
lean_ctor_set(x_72, 3, x_13);
lean_ctor_set_usize(x_72, 4, x_15);
lean_inc(x_11);
x_73 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_73, 0, x_11);
lean_inc(x_11);
x_74 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_11);
lean_ctor_set(x_74, 2, x_13);
lean_ctor_set(x_74, 3, x_13);
lean_ctor_set_usize(x_74, 4, x_15);
lean_inc(x_11);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_11);
lean_inc(x_11);
x_76 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_11);
lean_ctor_set(x_76, 2, x_13);
lean_ctor_set(x_76, 3, x_13);
lean_ctor_set_usize(x_76, 4, x_15);
x_77 = lean_box(0);
lean_inc(x_11);
x_78 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_78, 0, x_11);
lean_inc(x_11);
x_79 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_11);
lean_ctor_set(x_79, 2, x_13);
lean_ctor_set(x_79, 3, x_13);
lean_ctor_set_usize(x_79, 4, x_15);
lean_inc(x_11);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_11);
lean_inc(x_11);
x_81 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_11);
lean_ctor_set(x_81, 2, x_13);
lean_ctor_set(x_81, 3, x_13);
lean_ctor_set_usize(x_81, 4, x_15);
x_82 = lean_box(0);
lean_inc(x_4);
x_83 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_83, 0, x_4);
x_84 = lean_alloc_closure((void*)(l_Int_instDecidableEq___boxed), 2, 0);
x_85 = l_instBEqOfDecidableEq___redArg(x_84);
x_86 = l_instBEqProd___redArg(x_2, x_85);
x_87 = lean_alloc_closure((void*)(l_instHashableInt___lam__0___boxed), 1, 0);
x_88 = lean_alloc_closure((void*)(l_instHashableProd___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_88, 0, x_3);
lean_closure_set(x_88, 1, x_87);
x_89 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_86, x_88);
lean_dec(x_88);
lean_dec(x_86);
lean_inc(x_72);
lean_inc_n(x_58, 2);
lean_inc(x_16);
x_90 = lean_alloc_ctor(0, 17, 1);
lean_ctor_set(x_90, 0, x_16);
lean_ctor_set(x_90, 1, x_58);
lean_ctor_set(x_90, 2, x_67);
lean_ctor_set(x_90, 3, x_68);
lean_ctor_set(x_90, 4, x_58);
lean_ctor_set(x_90, 5, x_70);
lean_ctor_set(x_90, 6, x_72);
lean_ctor_set(x_90, 7, x_72);
lean_ctor_set(x_90, 8, x_74);
lean_ctor_set(x_90, 9, x_76);
lean_ctor_set(x_90, 10, x_77);
lean_ctor_set(x_90, 11, x_79);
lean_ctor_set(x_90, 12, x_81);
lean_ctor_set(x_90, 13, x_13);
lean_ctor_set(x_90, 14, x_82);
lean_ctor_set(x_90, 15, x_83);
lean_ctor_set(x_90, 16, x_89);
x_91 = lean_unbox(x_22);
lean_ctor_set_uint8(x_90, sizeof(void*)*17, x_91);
lean_inc(x_4);
x_92 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_92, 0, x_4);
lean_inc(x_11);
x_93 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_93, 0, x_11);
lean_ctor_set(x_93, 1, x_92);
lean_ctor_set(x_93, 2, x_58);
lean_ctor_set(x_93, 3, x_13);
x_94 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_94, 0, x_66);
lean_ctor_set(x_94, 1, x_90);
lean_ctor_set(x_94, 2, x_93);
x_95 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_95, 0, x_4);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_38);
lean_ctor_set(x_96, 1, x_95);
lean_inc(x_16);
x_97 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_97, 0, x_1);
lean_ctor_set(x_97, 1, x_7);
lean_ctor_set(x_97, 2, x_10);
lean_ctor_set(x_97, 3, x_16);
lean_ctor_set(x_97, 4, x_17);
lean_ctor_set(x_97, 5, x_20);
lean_ctor_set(x_97, 6, x_21);
lean_ctor_set(x_97, 7, x_11);
lean_ctor_set(x_97, 8, x_13);
lean_ctor_set(x_97, 9, x_23);
lean_ctor_set(x_97, 10, x_16);
lean_ctor_set(x_97, 11, x_24);
lean_ctor_set(x_97, 12, x_39);
lean_ctor_set(x_97, 13, x_57);
lean_ctor_set(x_97, 14, x_94);
lean_ctor_set(x_97, 15, x_96);
x_98 = lean_unbox(x_22);
lean_ctor_set_uint8(x_97, sizeof(void*)*16, x_98);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_97);
return x_99;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l_Lean_Expr_cleanupAnnotations(x_1);
x_3 = l_Lean_Expr_isApp(x_2);
if (x_3 == 0)
{
lean_object* x_4; 
lean_dec(x_2);
x_4 = lean_box(0);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
x_7 = lean_mk_string_unchecked("Grind", 5, 5);
x_8 = lean_mk_string_unchecked("alreadyNorm", 11, 11);
x_9 = l_Lean_Name_mkStr3(x_6, x_7, x_8);
x_10 = l_Lean_Expr_isConstOf(x_5, x_9);
lean_dec(x_9);
lean_dec(x_5);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_box(0);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
lean_inc(x_1);
x_11 = l_Lean_Meta_Simp_isEqnThmHypothesis(x_1);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_1);
x_12 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isAlreadyNorm_x3f(x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_preprocess(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_5);
x_15 = l_Lean_Meta_Grind_canon(x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Meta_Grind_shareCommon___redArg(x_16, x_5, x_17);
lean_dec(x_5);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_box(1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_unbox(x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_18, 0);
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_18);
x_27 = lean_box(1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_unbox(x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*2, x_30);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_26);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_15);
if (x_32 == 0)
{
return x_15;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_15, 0);
x_34 = lean_ctor_get(x_15, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_15);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Lean_Meta_Grind_markAsPreMatchCond(x_1);
x_37 = l_Lean_Meta_Grind_preprocess(x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_String_anyAux___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; 
x_5 = lean_nat_dec_lt(x_4, x_3);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
lean_object* x_10; uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(48u);
x_11 = lean_uint32_of_nat(x_10);
x_12 = lean_string_utf8_get(x_2, x_4);
x_13 = lean_uint32_dec_le(x_11, x_12);
if (x_13 == 0)
{
x_6 = x_13;
goto block_9;
}
else
{
lean_object* x_14; uint32_t x_15; uint8_t x_16; 
x_14 = lean_unsigned_to_nat(57u);
x_15 = lean_uint32_of_nat(x_14);
x_16 = lean_uint32_dec_le(x_12, x_15);
x_6 = x_16;
goto block_9;
}
}
block_9:
{
if (x_6 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_7; 
x_7 = lean_string_utf8_next(x_2, x_4);
lean_dec(x_4);
x_4 = x_7;
goto _start;
}
else
{
lean_dec(x_4);
return x_1;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_isProp(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_8);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_mk_string_unchecked("x", 1, 1);
x_14 = l_Lean_Name_mkStr1(x_13);
lean_ctor_set(x_8, 0, x_14);
return x_8;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_mk_string_unchecked("x", 1, 1);
x_17 = l_Lean_Name_mkStr1(x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_8);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_8, 0);
lean_dec(x_20);
x_21 = lean_mk_string_unchecked("h", 1, 1);
x_22 = l_Lean_Name_mkStr1(x_21);
lean_ctor_set(x_8, 0, x_22);
return x_8;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_8, 1);
lean_inc(x_23);
lean_dec(x_8);
x_24 = lean_mk_string_unchecked("h", 1, 1);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_8);
if (x_27 == 0)
{
return x_8;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_8, 0);
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_8);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__1(uint32_t x_1) {
_start:
{
lean_object* x_2; uint32_t x_3; uint8_t x_4; 
x_2 = lean_unsigned_to_nat(95u);
x_3 = l_Char_ofNat(x_2);
x_4 = l_instDecidableEqChar(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_26; 
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_dec(x_1);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__1___boxed), 1, 0);
x_14 = lean_string_utf8_byte_size(x_8);
x_15 = lean_unsigned_to_nat(0u);
x_16 = l_String_findAux(x_8, x_13, x_14, x_15);
x_26 = lean_nat_dec_lt(x_16, x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_dec(x_16);
lean_dec(x_14);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_27 = lean_box(0);
x_28 = l_Lean_Name_str___override(x_27, x_8);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_7);
return x_29;
}
else
{
lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_unsigned_to_nat(95u);
x_31 = l_Char_ofNat(x_30);
x_32 = l_Char_utf8Size(x_31);
x_33 = lean_nat_add(x_16, x_32);
lean_dec(x_32);
x_34 = lean_string_utf8_extract(x_8, x_33, x_14);
lean_dec(x_14);
lean_dec(x_33);
x_35 = lean_string_utf8_byte_size(x_34);
x_36 = l_instDecidableEqPos(x_35, x_15);
if (x_36 == 0)
{
uint8_t x_37; 
x_37 = l_String_anyAux___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(x_36, x_34, x_35, x_15);
lean_dec(x_35);
lean_dec(x_34);
if (x_37 == 0)
{
goto block_25;
}
else
{
if (x_36 == 0)
{
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_12;
}
else
{
goto block_25;
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_16);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_box(0);
x_10 = l_Lean_Name_str___override(x_9, x_8);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
block_25:
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_string_utf8_extract(x_8, x_15, x_16);
lean_dec(x_16);
lean_dec(x_8);
x_18 = lean_mk_string_unchecked("", 0, 0);
x_19 = lean_string_dec_eq(x_17, x_18);
lean_dec(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_box(0);
x_21 = l_Lean_Name_str___override(x_20, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_7);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_17);
x_23 = lean_box(0);
x_24 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__0(x_2, x_23, x_3, x_4, x_5, x_6, x_7);
return x_24;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_1);
x_38 = lean_box(0);
x_39 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__0(x_2, x_38, x_3, x_4, x_5, x_6, x_7);
return x_39;
}
}
}
LEAN_EXPORT lean_object* l_String_anyAux___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_String_anyAux___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName_spec__0(x_5, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__1___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName___lam__1(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_unsigned_to_nat(1u);
lean_inc(x_9);
lean_inc(x_1);
x_11 = lean_name_append_index_after(x_1, x_9);
x_12 = lean_nat_add(x_9, x_10);
lean_dec(x_9);
x_13 = lean_ctor_get(x_7, 15);
lean_inc(x_13);
lean_dec(x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_14, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_11);
lean_ctor_set(x_5, 0, x_16);
return x_5;
}
else
{
lean_object* x_17; 
lean_free_object(x_5);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_11);
x_2 = x_17;
x_4 = x_8;
goto _start;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_ctor_get(x_5, 0);
x_20 = lean_ctor_get(x_5, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_5);
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_unsigned_to_nat(1u);
lean_inc(x_21);
lean_inc(x_1);
x_23 = lean_name_append_index_after(x_1, x_21);
x_24 = lean_nat_add(x_21, x_22);
lean_dec(x_21);
x_25 = lean_ctor_get(x_19, 15);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_26, x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_24);
lean_ctor_set(x_28, 1, x_23);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_20);
return x_29;
}
else
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_24);
lean_ctor_set(x_30, 1, x_23);
x_2 = x_30;
x_4 = x_20;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(x_1, x_2, x_3, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
x_176 = l_Lean_Meta_Grind_getConfig___redArg(x_5, x_11);
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get_uint8(x_177, sizeof(void*)*7 + 11);
lean_dec(x_177);
if (x_178 == 0)
{
uint8_t x_179; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_179 = !lean_is_exclusive(x_176);
if (x_179 == 0)
{
lean_object* x_180; 
x_180 = lean_ctor_get(x_176, 0);
lean_dec(x_180);
lean_ctor_set(x_176, 0, x_1);
return x_176;
}
else
{
lean_object* x_181; lean_object* x_182; 
x_181 = lean_ctor_get(x_176, 1);
lean_inc(x_181);
lean_dec(x_176);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_1);
lean_ctor_set(x_182, 1, x_181);
return x_182;
}
}
else
{
lean_object* x_183; uint8_t x_184; 
x_183 = lean_ctor_get(x_176, 1);
lean_inc(x_183);
lean_dec(x_176);
x_184 = l_Lean_Name_hasMacroScopes(x_1);
if (x_184 == 0)
{
x_148 = x_1;
x_149 = x_3;
x_150 = x_4;
x_151 = x_5;
x_152 = x_6;
x_153 = x_7;
x_154 = x_8;
x_155 = x_9;
x_156 = x_10;
x_157 = x_183;
goto block_175;
}
else
{
lean_object* x_185; uint8_t x_186; lean_object* x_199; lean_object* x_200; uint8_t x_201; 
x_185 = lean_erase_macro_scopes(x_1);
x_199 = lean_mk_string_unchecked("x", 1, 1);
x_200 = l_Lean_Name_mkStr1(x_199);
x_201 = lean_name_eq(x_185, x_200);
lean_dec(x_200);
if (x_201 == 0)
{
lean_object* x_202; lean_object* x_203; uint8_t x_204; 
x_202 = lean_mk_string_unchecked("a", 1, 1);
x_203 = l_Lean_Name_mkStr1(x_202);
x_204 = lean_name_eq(x_185, x_203);
lean_dec(x_203);
x_186 = x_204;
goto block_198;
}
else
{
x_186 = x_178;
goto block_198;
}
block_198:
{
if (x_186 == 0)
{
x_148 = x_185;
x_149 = x_3;
x_150 = x_4;
x_151 = x_5;
x_152 = x_6;
x_153 = x_7;
x_154 = x_8;
x_155 = x_9;
x_156 = x_10;
x_157 = x_183;
goto block_175;
}
else
{
lean_object* x_187; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
x_187 = l_Lean_Meta_isProp(x_2, x_7, x_8, x_9, x_10, x_183);
if (lean_obj_tag(x_187) == 0)
{
lean_object* x_188; uint8_t x_189; 
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_unbox(x_188);
lean_dec(x_188);
if (x_189 == 0)
{
lean_object* x_190; 
x_190 = lean_ctor_get(x_187, 1);
lean_inc(x_190);
lean_dec(x_187);
x_148 = x_185;
x_149 = x_3;
x_150 = x_4;
x_151 = x_5;
x_152 = x_6;
x_153 = x_7;
x_154 = x_8;
x_155 = x_9;
x_156 = x_10;
x_157 = x_190;
goto block_175;
}
else
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_185);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
x_192 = lean_mk_string_unchecked("h", 1, 1);
x_193 = l_Lean_Name_mkStr1(x_192);
x_148 = x_193;
x_149 = x_3;
x_150 = x_4;
x_151 = x_5;
x_152 = x_6;
x_153 = x_7;
x_154 = x_8;
x_155 = x_9;
x_156 = x_10;
x_157 = x_191;
goto block_175;
}
}
else
{
uint8_t x_194; 
lean_dec(x_185);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_2);
x_194 = !lean_is_exclusive(x_187);
if (x_194 == 0)
{
return x_187;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_187, 0);
x_196 = lean_ctor_get(x_187, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_187);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
}
}
block_75:
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_st_ref_take(x_13, x_14);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_17, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_17, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_17, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_17, 5);
lean_inc(x_24);
x_25 = lean_ctor_get(x_17, 6);
lean_inc(x_25);
x_26 = lean_ctor_get(x_17, 7);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_17, sizeof(void*)*16);
x_28 = lean_ctor_get(x_17, 8);
lean_inc(x_28);
x_29 = lean_ctor_get(x_17, 9);
lean_inc(x_29);
x_30 = lean_ctor_get(x_17, 10);
lean_inc(x_30);
x_31 = lean_ctor_get(x_17, 11);
lean_inc(x_31);
x_32 = lean_ctor_get(x_17, 12);
lean_inc(x_32);
x_33 = lean_ctor_get(x_17, 13);
lean_inc(x_33);
x_34 = lean_ctor_get(x_17, 14);
lean_inc(x_34);
x_35 = lean_ctor_get(x_17, 15);
lean_inc(x_35);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_box(0);
lean_inc(x_12);
x_38 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_36, x_12, x_37);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
lean_ctor_set(x_15, 1, x_39);
lean_ctor_set(x_15, 0, x_38);
x_40 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_40, 0, x_19);
lean_ctor_set(x_40, 1, x_20);
lean_ctor_set(x_40, 2, x_21);
lean_ctor_set(x_40, 3, x_22);
lean_ctor_set(x_40, 4, x_23);
lean_ctor_set(x_40, 5, x_24);
lean_ctor_set(x_40, 6, x_25);
lean_ctor_set(x_40, 7, x_26);
lean_ctor_set(x_40, 8, x_28);
lean_ctor_set(x_40, 9, x_29);
lean_ctor_set(x_40, 10, x_30);
lean_ctor_set(x_40, 11, x_31);
lean_ctor_set(x_40, 12, x_32);
lean_ctor_set(x_40, 13, x_33);
lean_ctor_set(x_40, 14, x_34);
lean_ctor_set(x_40, 15, x_15);
lean_ctor_set_uint8(x_40, sizeof(void*)*16, x_27);
x_41 = lean_st_ref_set(x_13, x_40, x_18);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_12);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_12);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_46 = lean_ctor_get(x_15, 0);
x_47 = lean_ctor_get(x_15, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_15);
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_46, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_46, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_46, 3);
lean_inc(x_51);
x_52 = lean_ctor_get(x_46, 4);
lean_inc(x_52);
x_53 = lean_ctor_get(x_46, 5);
lean_inc(x_53);
x_54 = lean_ctor_get(x_46, 6);
lean_inc(x_54);
x_55 = lean_ctor_get(x_46, 7);
lean_inc(x_55);
x_56 = lean_ctor_get_uint8(x_46, sizeof(void*)*16);
x_57 = lean_ctor_get(x_46, 8);
lean_inc(x_57);
x_58 = lean_ctor_get(x_46, 9);
lean_inc(x_58);
x_59 = lean_ctor_get(x_46, 10);
lean_inc(x_59);
x_60 = lean_ctor_get(x_46, 11);
lean_inc(x_60);
x_61 = lean_ctor_get(x_46, 12);
lean_inc(x_61);
x_62 = lean_ctor_get(x_46, 13);
lean_inc(x_62);
x_63 = lean_ctor_get(x_46, 14);
lean_inc(x_63);
x_64 = lean_ctor_get(x_46, 15);
lean_inc(x_64);
lean_dec(x_46);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_box(0);
lean_inc(x_12);
x_67 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_65, x_12, x_66);
x_68 = lean_ctor_get(x_64, 1);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_70, 0, x_48);
lean_ctor_set(x_70, 1, x_49);
lean_ctor_set(x_70, 2, x_50);
lean_ctor_set(x_70, 3, x_51);
lean_ctor_set(x_70, 4, x_52);
lean_ctor_set(x_70, 5, x_53);
lean_ctor_set(x_70, 6, x_54);
lean_ctor_set(x_70, 7, x_55);
lean_ctor_set(x_70, 8, x_57);
lean_ctor_set(x_70, 9, x_58);
lean_ctor_set(x_70, 10, x_59);
lean_ctor_set(x_70, 11, x_60);
lean_ctor_set(x_70, 12, x_61);
lean_ctor_set(x_70, 13, x_62);
lean_ctor_set(x_70, 14, x_63);
lean_ctor_set(x_70, 15, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*16, x_56);
x_71 = lean_st_ref_set(x_13, x_70, x_47);
x_72 = lean_ctor_get(x_71, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_73 = x_71;
} else {
 lean_dec_ref(x_71);
 x_73 = lean_box(0);
}
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_12);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
block_147:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
lean_dec(x_86);
lean_dec(x_81);
lean_dec(x_77);
lean_dec(x_76);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_85);
lean_inc(x_84);
x_89 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(x_84, x_88, x_79, x_80);
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
lean_dec(x_90);
x_94 = lean_st_ref_take(x_79, x_91);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_96 = lean_ctor_get(x_94, 0);
x_97 = lean_ctor_get(x_94, 1);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_96, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_96, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_96, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_96, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_96, 6);
lean_inc(x_104);
x_105 = lean_ctor_get(x_96, 7);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_96, sizeof(void*)*16);
x_107 = lean_ctor_get(x_96, 8);
lean_inc(x_107);
x_108 = lean_ctor_get(x_96, 9);
lean_inc(x_108);
x_109 = lean_ctor_get(x_96, 10);
lean_inc(x_109);
x_110 = lean_ctor_get(x_96, 11);
lean_inc(x_110);
x_111 = lean_ctor_get(x_96, 12);
lean_inc(x_111);
x_112 = lean_ctor_get(x_96, 13);
lean_inc(x_112);
x_113 = lean_ctor_get(x_96, 14);
lean_inc(x_113);
x_114 = lean_ctor_get(x_96, 15);
lean_inc(x_114);
lean_dec(x_96);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_116, x_84, x_92);
lean_ctor_set(x_94, 1, x_117);
lean_ctor_set(x_94, 0, x_115);
x_118 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_118, 0, x_98);
lean_ctor_set(x_118, 1, x_99);
lean_ctor_set(x_118, 2, x_100);
lean_ctor_set(x_118, 3, x_101);
lean_ctor_set(x_118, 4, x_102);
lean_ctor_set(x_118, 5, x_103);
lean_ctor_set(x_118, 6, x_104);
lean_ctor_set(x_118, 7, x_105);
lean_ctor_set(x_118, 8, x_107);
lean_ctor_set(x_118, 9, x_108);
lean_ctor_set(x_118, 10, x_109);
lean_ctor_set(x_118, 11, x_110);
lean_ctor_set(x_118, 12, x_111);
lean_ctor_set(x_118, 13, x_112);
lean_ctor_set(x_118, 14, x_113);
lean_ctor_set(x_118, 15, x_94);
lean_ctor_set_uint8(x_118, sizeof(void*)*16, x_106);
x_119 = lean_st_ref_set(x_79, x_118, x_97);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_12 = x_93;
x_13 = x_79;
x_14 = x_120;
goto block_75;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_121 = lean_ctor_get(x_94, 0);
x_122 = lean_ctor_get(x_94, 1);
lean_inc(x_122);
lean_inc(x_121);
lean_dec(x_94);
x_123 = lean_ctor_get(x_121, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
x_125 = lean_ctor_get(x_121, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_121, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_121, 4);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 5);
lean_inc(x_128);
x_129 = lean_ctor_get(x_121, 6);
lean_inc(x_129);
x_130 = lean_ctor_get(x_121, 7);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_121, sizeof(void*)*16);
x_132 = lean_ctor_get(x_121, 8);
lean_inc(x_132);
x_133 = lean_ctor_get(x_121, 9);
lean_inc(x_133);
x_134 = lean_ctor_get(x_121, 10);
lean_inc(x_134);
x_135 = lean_ctor_get(x_121, 11);
lean_inc(x_135);
x_136 = lean_ctor_get(x_121, 12);
lean_inc(x_136);
x_137 = lean_ctor_get(x_121, 13);
lean_inc(x_137);
x_138 = lean_ctor_get(x_121, 14);
lean_inc(x_138);
x_139 = lean_ctor_get(x_121, 15);
lean_inc(x_139);
lean_dec(x_121);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
lean_dec(x_139);
x_142 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_141, x_84, x_92);
x_143 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_144, 0, x_123);
lean_ctor_set(x_144, 1, x_124);
lean_ctor_set(x_144, 2, x_125);
lean_ctor_set(x_144, 3, x_126);
lean_ctor_set(x_144, 4, x_127);
lean_ctor_set(x_144, 5, x_128);
lean_ctor_set(x_144, 6, x_129);
lean_ctor_set(x_144, 7, x_130);
lean_ctor_set(x_144, 8, x_132);
lean_ctor_set(x_144, 9, x_133);
lean_ctor_set(x_144, 10, x_134);
lean_ctor_set(x_144, 11, x_135);
lean_ctor_set(x_144, 12, x_136);
lean_ctor_set(x_144, 13, x_137);
lean_ctor_set(x_144, 14, x_138);
lean_ctor_set(x_144, 15, x_143);
lean_ctor_set_uint8(x_144, sizeof(void*)*16, x_131);
x_145 = lean_st_ref_set(x_79, x_144, x_122);
x_146 = lean_ctor_get(x_145, 1);
lean_inc(x_146);
lean_dec(x_145);
x_12 = x_93;
x_13 = x_79;
x_14 = x_146;
goto block_75;
}
}
block_175:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; uint8_t x_163; 
x_158 = lean_st_ref_get(x_149, x_157);
x_159 = lean_ctor_get(x_158, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_158, 1);
lean_inc(x_160);
lean_dec(x_158);
x_161 = lean_ctor_get(x_159, 15);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_162, x_148);
if (x_163 == 0)
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_2);
x_12 = x_148;
x_13 = x_149;
x_14 = x_160;
goto block_75;
}
else
{
lean_object* x_164; 
lean_inc(x_156);
lean_inc(x_155);
lean_inc(x_154);
lean_inc(x_153);
lean_inc(x_148);
x_164 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkBaseName(x_148, x_2, x_153, x_154, x_155, x_156, x_160);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
lean_dec(x_164);
x_167 = lean_st_ref_get(x_149, x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = lean_ctor_get(x_168, 15);
lean_inc(x_170);
lean_dec(x_168);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
lean_dec(x_170);
x_172 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_box(0), x_171, x_165);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_unsigned_to_nat(1u);
x_76 = x_154;
x_77 = x_156;
x_78 = x_151;
x_79 = x_149;
x_80 = x_169;
x_81 = x_153;
x_82 = x_150;
x_83 = x_152;
x_84 = x_165;
x_85 = x_148;
x_86 = x_155;
x_87 = x_173;
goto block_147;
}
else
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_76 = x_154;
x_77 = x_156;
x_78 = x_151;
x_79 = x_149;
x_80 = x_169;
x_81 = x_153;
x_82 = x_150;
x_83 = x_152;
x_84 = x_165;
x_85 = x_148;
x_86 = x_155;
x_87 = x_174;
goto block_147;
}
}
else
{
lean_dec(x_156);
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_153);
lean_dec(x_148);
return x_164;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(x_11, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_st_ref_get(x_2, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_MVarId_intro(x_19, x_14, x_6, x_7, x_8, x_9, x_18);
lean_dec(x_6);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_st_ref_take(x_2, x_22);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_26, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_26, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_26, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_26, 7);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_26, sizeof(void*)*16);
x_36 = lean_ctor_get(x_26, 8);
lean_inc(x_36);
x_37 = lean_ctor_get(x_26, 9);
lean_inc(x_37);
x_38 = lean_ctor_get(x_26, 10);
lean_inc(x_38);
x_39 = lean_ctor_get(x_26, 11);
lean_inc(x_39);
x_40 = lean_ctor_get(x_26, 12);
lean_inc(x_40);
x_41 = lean_ctor_get(x_26, 13);
lean_inc(x_41);
x_42 = lean_ctor_get(x_26, 14);
lean_inc(x_42);
x_43 = lean_ctor_get(x_26, 15);
lean_inc(x_43);
lean_dec(x_26);
x_44 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_30);
lean_ctor_set(x_44, 4, x_31);
lean_ctor_set(x_44, 5, x_32);
lean_ctor_set(x_44, 6, x_33);
lean_ctor_set(x_44, 7, x_34);
lean_ctor_set(x_44, 8, x_36);
lean_ctor_set(x_44, 9, x_37);
lean_ctor_set(x_44, 10, x_38);
lean_ctor_set(x_44, 11, x_39);
lean_ctor_set(x_44, 12, x_40);
lean_ctor_set(x_44, 13, x_41);
lean_ctor_set(x_44, 14, x_42);
lean_ctor_set(x_44, 15, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*16, x_35);
x_45 = lean_st_ref_set(x_2, x_44, x_27);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_23);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_23);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
else
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_20);
if (x_50 == 0)
{
return x_20;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_20, 0);
x_52 = lean_ctor_get(x_20, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_20);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
uint8_t x_54; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_54 = !lean_is_exclusive(x_13);
if (x_54 == 0)
{
return x_13;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_13, 0);
x_56 = lean_ctor_get(x_13, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_13);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_1, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_MVarId_getType(x_14, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
switch (lean_obj_tag(x_16)) {
case 7:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_19);
lean_ctor_set(x_10, 0, x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_17);
return x_20;
}
case 8:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_dec(x_15);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
lean_ctor_set(x_10, 1, x_23);
lean_ctor_set(x_10, 0, x_22);
x_24 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_21);
return x_24;
}
default: 
{
lean_object* x_25; lean_object* x_26; 
lean_free_object(x_10);
x_25 = lean_ctor_get(x_15, 1);
lean_inc(x_25);
lean_dec(x_15);
x_26 = l_Lean_Expr_letFun_x3f(x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_27 = lean_mk_string_unchecked("`grind` internal error, binder expected", 39, 39);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(x_28, x_5, x_6, x_7, x_8, x_25);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
return x_29;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_29);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_26, 0);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = !lean_is_exclusive(x_35);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_35, 0);
x_39 = lean_ctor_get(x_35, 1);
lean_dec(x_39);
lean_ctor_set(x_35, 1, x_38);
lean_ctor_set(x_35, 0, x_36);
x_40 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_35, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
lean_dec(x_35);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_36);
lean_ctor_set(x_42, 1, x_41);
x_43 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_42, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_25);
return x_43;
}
}
}
}
}
else
{
uint8_t x_44; 
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_15);
if (x_44 == 0)
{
return x_15;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_15, 0);
x_46 = lean_ctor_get(x_15, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_15);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_48 = lean_ctor_get(x_10, 0);
x_49 = lean_ctor_get(x_10, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_10);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
lean_dec(x_48);
x_51 = l_Lean_MVarId_getType(x_50, x_5, x_6, x_7, x_8, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
switch (lean_obj_tag(x_52)) {
case 7:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_ctor_get(x_52, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
x_57 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_56, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_53);
return x_57;
}
case 8:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_51, 1);
lean_inc(x_58);
lean_dec(x_51);
x_59 = lean_ctor_get(x_52, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_52, 1);
lean_inc(x_60);
lean_dec(x_52);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_61, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
return x_62;
}
default: 
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_51, 1);
lean_inc(x_63);
lean_dec(x_51);
x_64 = l_Lean_Expr_letFun_x3f(x_52);
if (lean_obj_tag(x_64) == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_65 = lean_mk_string_unchecked("`grind` internal error, binder expected", 39, 39);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = l_Lean_throwError___at___Lean_Meta_Grind_addNewRawFact_spec__0___redArg(x_66, x_5, x_6, x_7, x_8, x_63);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_67, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_70 = x_67;
} else {
 lean_dec_ref(x_67);
 x_70 = lean_box(0);
}
if (lean_is_scalar(x_70)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_70;
}
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_69);
return x_71;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_72 = lean_ctor_get(x_64, 0);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_ctor_get(x_73, 0);
lean_inc(x_75);
if (lean_is_exclusive(x_73)) {
 lean_ctor_release(x_73, 0);
 lean_ctor_release(x_73, 1);
 x_76 = x_73;
} else {
 lean_dec_ref(x_73);
 x_76 = lean_box(0);
}
if (lean_is_scalar(x_76)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_76;
}
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_75);
x_78 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_77, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_63);
return x_78;
}
}
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_79 = lean_ctor_get(x_51, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_51, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_81 = x_51;
} else {
 lean_dec_ref(x_51);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___lam__0), 10, 5);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_3);
lean_closure_set(x_12, 2, x_4);
lean_closure_set(x_12, 3, x_5);
lean_closure_set(x_12, 4, x_6);
x_13 = l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_box(0), x_1, x_12, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
return x_13;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_13);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = lean_ctor_get(x_4, 2);
lean_inc(x_6);
lean_dec(x_4);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_st_ref_take(x_1, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_6, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_13);
lean_dec(x_6);
x_14 = lean_nat_add(x_13, x_7);
lean_inc(x_12);
lean_ctor_set(x_8, 1, x_14);
lean_ctor_set(x_8, 0, x_12);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_10, 3);
lean_inc(x_17);
x_18 = lean_ctor_get(x_10, 4);
lean_inc(x_18);
x_19 = lean_ctor_get(x_10, 5);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 6);
lean_inc(x_20);
x_21 = lean_ctor_get(x_10, 7);
lean_inc(x_21);
lean_dec(x_10);
x_22 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_22, 0, x_15);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_22, 2, x_8);
lean_ctor_set(x_22, 3, x_17);
lean_ctor_set(x_22, 4, x_18);
lean_ctor_set(x_22, 5, x_19);
lean_ctor_set(x_22, 6, x_20);
lean_ctor_set(x_22, 7, x_21);
x_23 = lean_st_ref_set(x_1, x_22, x_11);
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_23, 0);
lean_dec(x_25);
x_26 = l_Lean_Name_num___override(x_12, x_13);
lean_ctor_set(x_23, 0, x_26);
return x_23;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_23, 1);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Name_num___override(x_12, x_13);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_ctor_get(x_6, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_6, 1);
lean_inc(x_33);
lean_dec(x_6);
x_34 = lean_nat_add(x_33, x_7);
lean_inc(x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_30, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_30, 4);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 5);
lean_inc(x_40);
x_41 = lean_ctor_get(x_30, 6);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 7);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_37);
lean_ctor_set(x_43, 2, x_35);
lean_ctor_set(x_43, 3, x_38);
lean_ctor_set(x_43, 4, x_39);
lean_ctor_set(x_43, 5, x_40);
lean_ctor_set(x_43, 6, x_41);
lean_ctor_set(x_43, 7, x_42);
x_44 = lean_st_ref_set(x_1, x_43, x_31);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_44)) {
 lean_ctor_release(x_44, 0);
 lean_ctor_release(x_44, 1);
 x_46 = x_44;
} else {
 lean_dec_ref(x_44);
 x_46 = lean_box(0);
}
x_47 = l_Lean_Name_num___override(x_32, x_33);
if (lean_is_scalar(x_46)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_46;
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(x_8, x_9);
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
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_7);
lean_inc(x_1);
x_12 = l_Lean_FVarId_getDecl___redArg(x_1, x_7, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_151; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_151 = lean_ctor_get(x_13, 3);
lean_inc(x_151);
lean_dec(x_13);
x_15 = x_151;
goto block_150;
block_150:
{
lean_object* x_16; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_16 = l_Lean_Meta_isProp(x_15, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_15);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
lean_inc(x_7);
lean_inc(x_1);
x_20 = l_Lean_FVarId_getDecl___redArg(x_1, x_7, x_9, x_10, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = l_Lean_LocalDecl_value(x_21);
lean_dec(x_21);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_24 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_22);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
lean_inc(x_1);
x_27 = l_Lean_Expr_fvar___override(x_1);
x_28 = l_Lean_Meta_Grind_shareCommon___redArg(x_27, x_6, x_26);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
x_32 = l_Lean_Meta_Simp_Result_getProof(x_25, x_7, x_8, x_9, x_10, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_25, 0);
lean_inc(x_35);
lean_dec(x_25);
lean_inc(x_3);
x_36 = l_Lean_Meta_Grind_addNewEq(x_30, x_35, x_33, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_get(x_3, x_37);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set_tag(x_28, 3);
lean_ctor_set(x_28, 1, x_40);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_38, 0, x_28);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set_tag(x_28, 3);
lean_ctor_set(x_28, 1, x_41);
lean_ctor_set(x_28, 0, x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_28);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_28);
lean_dec(x_3);
lean_dec(x_1);
x_44 = !lean_is_exclusive(x_36);
if (x_44 == 0)
{
return x_36;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_36, 0);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_36);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_free_object(x_28);
lean_dec(x_30);
lean_dec(x_25);
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
x_48 = !lean_is_exclusive(x_32);
if (x_48 == 0)
{
return x_32;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_32, 0);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_32);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_28, 0);
x_53 = lean_ctor_get(x_28, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_25);
x_54 = l_Lean_Meta_Simp_Result_getProof(x_25, x_7, x_8, x_9, x_10, x_53);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
lean_dec(x_54);
x_57 = lean_ctor_get(x_25, 0);
lean_inc(x_57);
lean_dec(x_25);
lean_inc(x_3);
x_58 = l_Lean_Meta_Grind_addNewEq(x_52, x_57, x_55, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_st_ref_get(x_3, x_59);
lean_dec(x_3);
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_60)) {
 lean_ctor_release(x_60, 0);
 lean_ctor_release(x_60, 1);
 x_63 = x_60;
} else {
 lean_dec_ref(x_60);
 x_63 = lean_box(0);
}
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_1);
lean_ctor_set(x_64, 1, x_61);
if (lean_is_scalar(x_63)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_63;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_62);
return x_65;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_ctor_get(x_58, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_58, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_68 = x_58;
} else {
 lean_dec_ref(x_58);
 x_68 = lean_box(0);
}
if (lean_is_scalar(x_68)) {
 x_69 = lean_alloc_ctor(1, 2, 0);
} else {
 x_69 = x_68;
}
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_67);
return x_69;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_52);
lean_dec(x_25);
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
x_70 = lean_ctor_get(x_54, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_54, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_72 = x_54;
} else {
 lean_dec_ref(x_54);
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
x_74 = !lean_is_exclusive(x_24);
if (x_74 == 0)
{
return x_24;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_24, 0);
x_76 = lean_ctor_get(x_24, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_24);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
uint8_t x_78; 
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
x_78 = !lean_is_exclusive(x_20);
if (x_78 == 0)
{
return x_20;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_20, 0);
x_80 = lean_ctor_get(x_20, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_20);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
lean_dec(x_2);
x_82 = lean_ctor_get(x_16, 1);
lean_inc(x_82);
lean_dec(x_16);
x_83 = lean_st_ref_get(x_3, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_mk_string_unchecked("h", 1, 1);
x_87 = l_Lean_Name_mkStr1(x_86);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_15);
x_88 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(x_87, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_85);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_84, 0);
lean_inc(x_91);
lean_dec(x_84);
x_92 = l_Lean_Expr_fvar___override(x_1);
x_93 = l_Lean_MVarId_assert(x_91, x_89, x_15, x_92, x_7, x_8, x_9, x_10, x_90);
lean_dec(x_7);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_st_ref_get(x_3, x_95);
lean_dec(x_3);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_98, 1);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 2);
lean_inc(x_100);
x_101 = lean_ctor_get(x_98, 3);
lean_inc(x_101);
x_102 = lean_ctor_get(x_98, 4);
lean_inc(x_102);
x_103 = lean_ctor_get(x_98, 5);
lean_inc(x_103);
x_104 = lean_ctor_get(x_98, 6);
lean_inc(x_104);
x_105 = lean_ctor_get(x_98, 7);
lean_inc(x_105);
x_106 = lean_ctor_get_uint8(x_98, sizeof(void*)*16);
x_107 = lean_ctor_get(x_98, 8);
lean_inc(x_107);
x_108 = lean_ctor_get(x_98, 9);
lean_inc(x_108);
x_109 = lean_ctor_get(x_98, 10);
lean_inc(x_109);
x_110 = lean_ctor_get(x_98, 11);
lean_inc(x_110);
x_111 = lean_ctor_get(x_98, 12);
lean_inc(x_111);
x_112 = lean_ctor_get(x_98, 13);
lean_inc(x_112);
x_113 = lean_ctor_get(x_98, 14);
lean_inc(x_113);
x_114 = lean_ctor_get(x_98, 15);
lean_inc(x_114);
lean_dec(x_98);
x_115 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_115, 0, x_94);
lean_ctor_set(x_115, 1, x_99);
lean_ctor_set(x_115, 2, x_100);
lean_ctor_set(x_115, 3, x_101);
lean_ctor_set(x_115, 4, x_102);
lean_ctor_set(x_115, 5, x_103);
lean_ctor_set(x_115, 6, x_104);
lean_ctor_set(x_115, 7, x_105);
lean_ctor_set(x_115, 8, x_107);
lean_ctor_set(x_115, 9, x_108);
lean_ctor_set(x_115, 10, x_109);
lean_ctor_set(x_115, 11, x_110);
lean_ctor_set(x_115, 12, x_111);
lean_ctor_set(x_115, 13, x_112);
lean_ctor_set(x_115, 14, x_113);
lean_ctor_set(x_115, 15, x_114);
lean_ctor_set_uint8(x_115, sizeof(void*)*16, x_106);
x_116 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_96, 0, x_116);
return x_96;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_117 = lean_ctor_get(x_96, 0);
x_118 = lean_ctor_get(x_96, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_96);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 2);
lean_inc(x_120);
x_121 = lean_ctor_get(x_117, 3);
lean_inc(x_121);
x_122 = lean_ctor_get(x_117, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_117, 5);
lean_inc(x_123);
x_124 = lean_ctor_get(x_117, 6);
lean_inc(x_124);
x_125 = lean_ctor_get(x_117, 7);
lean_inc(x_125);
x_126 = lean_ctor_get_uint8(x_117, sizeof(void*)*16);
x_127 = lean_ctor_get(x_117, 8);
lean_inc(x_127);
x_128 = lean_ctor_get(x_117, 9);
lean_inc(x_128);
x_129 = lean_ctor_get(x_117, 10);
lean_inc(x_129);
x_130 = lean_ctor_get(x_117, 11);
lean_inc(x_130);
x_131 = lean_ctor_get(x_117, 12);
lean_inc(x_131);
x_132 = lean_ctor_get(x_117, 13);
lean_inc(x_132);
x_133 = lean_ctor_get(x_117, 14);
lean_inc(x_133);
x_134 = lean_ctor_get(x_117, 15);
lean_inc(x_134);
lean_dec(x_117);
x_135 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_135, 0, x_94);
lean_ctor_set(x_135, 1, x_119);
lean_ctor_set(x_135, 2, x_120);
lean_ctor_set(x_135, 3, x_121);
lean_ctor_set(x_135, 4, x_122);
lean_ctor_set(x_135, 5, x_123);
lean_ctor_set(x_135, 6, x_124);
lean_ctor_set(x_135, 7, x_125);
lean_ctor_set(x_135, 8, x_127);
lean_ctor_set(x_135, 9, x_128);
lean_ctor_set(x_135, 10, x_129);
lean_ctor_set(x_135, 11, x_130);
lean_ctor_set(x_135, 12, x_131);
lean_ctor_set(x_135, 13, x_132);
lean_ctor_set(x_135, 14, x_133);
lean_ctor_set(x_135, 15, x_134);
lean_ctor_set_uint8(x_135, sizeof(void*)*16, x_126);
x_136 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_136, 0, x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_118);
return x_137;
}
}
else
{
uint8_t x_138; 
lean_dec(x_3);
x_138 = !lean_is_exclusive(x_93);
if (x_138 == 0)
{
return x_93;
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_139 = lean_ctor_get(x_93, 0);
x_140 = lean_ctor_get(x_93, 1);
lean_inc(x_140);
lean_inc(x_139);
lean_dec(x_93);
x_141 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_141, 0, x_139);
lean_ctor_set(x_141, 1, x_140);
return x_141;
}
}
}
else
{
uint8_t x_142; 
lean_dec(x_84);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_142 = !lean_is_exclusive(x_88);
if (x_142 == 0)
{
return x_88;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_88, 0);
x_144 = lean_ctor_get(x_88, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_88);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
}
}
else
{
uint8_t x_146; 
lean_dec(x_15);
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
x_146 = !lean_is_exclusive(x_16);
if (x_146 == 0)
{
return x_16;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_16, 0);
x_148 = lean_ctor_get(x_16, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_16);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
}
else
{
uint8_t x_152; 
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
x_152 = !lean_is_exclusive(x_12);
if (x_152 == 0)
{
return x_12;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_153 = lean_ctor_get(x_12, 0);
x_154 = lean_ctor_get(x_12, 1);
lean_inc(x_154);
lean_inc(x_153);
lean_dec(x_12);
x_155 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
return x_155;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_1);
x_13 = l_Lean_MVarId_getTag(x_1, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_8);
x_16 = l_Lean_Meta_mkFreshExprSyntheticOpaqueMVar(x_2, x_14, x_8, x_9, x_10, x_11, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_17);
x_19 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_closeGoal_spec__1(x_1, x_17, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_st_ref_get(x_4, x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = l_Lean_Expr_mvarId_x21(x_17);
lean_dec(x_17);
x_25 = lean_ctor_get(x_22, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_22, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 4);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_22, 6);
lean_inc(x_30);
x_31 = lean_ctor_get(x_22, 7);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_22, sizeof(void*)*16);
x_33 = lean_ctor_get(x_22, 8);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 9);
lean_inc(x_34);
x_35 = lean_ctor_get(x_22, 10);
lean_inc(x_35);
x_36 = lean_ctor_get(x_22, 11);
lean_inc(x_36);
x_37 = lean_ctor_get(x_22, 12);
lean_inc(x_37);
x_38 = lean_ctor_get(x_22, 13);
lean_inc(x_38);
x_39 = lean_ctor_get(x_22, 14);
lean_inc(x_39);
x_40 = lean_ctor_get(x_22, 15);
lean_inc(x_40);
lean_dec(x_22);
x_41 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_41, 0, x_24);
lean_ctor_set(x_41, 1, x_25);
lean_ctor_set(x_41, 2, x_26);
lean_ctor_set(x_41, 3, x_27);
lean_ctor_set(x_41, 4, x_28);
lean_ctor_set(x_41, 5, x_29);
lean_ctor_set(x_41, 6, x_30);
lean_ctor_set(x_41, 7, x_31);
lean_ctor_set(x_41, 8, x_33);
lean_ctor_set(x_41, 9, x_34);
lean_ctor_set(x_41, 10, x_35);
lean_ctor_set(x_41, 11, x_36);
lean_ctor_set(x_41, 12, x_37);
lean_ctor_set(x_41, 13, x_38);
lean_ctor_set(x_41, 14, x_39);
lean_ctor_set(x_41, 15, x_40);
lean_ctor_set_uint8(x_41, sizeof(void*)*16, x_32);
x_42 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_41, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_23);
lean_dec(x_8);
return x_42;
}
else
{
uint8_t x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_13);
if (x_43 == 0)
{
return x_13;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_13, 0);
x_45 = lean_ctor_get(x_13, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_13);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17) {
_start:
{
lean_object* x_18; 
x_18 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_3, x_4, x_3, x_5, x_13, x_14, x_15, x_16, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_closeGoal_spec__1(x_6, x_19, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_20);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_23 = lean_ctor_get(x_21, 1);
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_st_ref_get(x_9, x_23);
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 2);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 3);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 4);
lean_inc(x_31);
x_32 = lean_ctor_get(x_27, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_27, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 7);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_27, sizeof(void*)*16);
x_36 = lean_ctor_get(x_27, 8);
lean_inc(x_36);
x_37 = lean_ctor_get(x_27, 9);
lean_inc(x_37);
x_38 = lean_ctor_get(x_27, 10);
lean_inc(x_38);
x_39 = lean_ctor_get(x_27, 11);
lean_inc(x_39);
x_40 = lean_ctor_get(x_27, 12);
lean_inc(x_40);
x_41 = lean_ctor_get(x_27, 13);
lean_inc(x_41);
x_42 = lean_ctor_get(x_27, 14);
lean_inc(x_42);
x_43 = lean_ctor_get(x_27, 15);
lean_inc(x_43);
lean_dec(x_27);
x_44 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_44, 0, x_7);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_30);
lean_ctor_set(x_44, 4, x_31);
lean_ctor_set(x_44, 5, x_32);
lean_ctor_set(x_44, 6, x_33);
lean_ctor_set(x_44, 7, x_34);
lean_ctor_set(x_44, 8, x_36);
lean_ctor_set(x_44, 9, x_37);
lean_ctor_set(x_44, 10, x_38);
lean_ctor_set(x_44, 11, x_39);
lean_ctor_set(x_44, 12, x_40);
lean_ctor_set(x_44, 13, x_41);
lean_ctor_set(x_44, 14, x_42);
lean_ctor_set(x_44, 15, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*16, x_35);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_44);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_25, 0, x_21);
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_45 = lean_ctor_get(x_25, 0);
x_46 = lean_ctor_get(x_25, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_25);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
x_48 = lean_ctor_get(x_45, 2);
lean_inc(x_48);
x_49 = lean_ctor_get(x_45, 3);
lean_inc(x_49);
x_50 = lean_ctor_get(x_45, 4);
lean_inc(x_50);
x_51 = lean_ctor_get(x_45, 5);
lean_inc(x_51);
x_52 = lean_ctor_get(x_45, 6);
lean_inc(x_52);
x_53 = lean_ctor_get(x_45, 7);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_45, sizeof(void*)*16);
x_55 = lean_ctor_get(x_45, 8);
lean_inc(x_55);
x_56 = lean_ctor_get(x_45, 9);
lean_inc(x_56);
x_57 = lean_ctor_get(x_45, 10);
lean_inc(x_57);
x_58 = lean_ctor_get(x_45, 11);
lean_inc(x_58);
x_59 = lean_ctor_get(x_45, 12);
lean_inc(x_59);
x_60 = lean_ctor_get(x_45, 13);
lean_inc(x_60);
x_61 = lean_ctor_get(x_45, 14);
lean_inc(x_61);
x_62 = lean_ctor_get(x_45, 15);
lean_inc(x_62);
lean_dec(x_45);
x_63 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_63, 0, x_7);
lean_ctor_set(x_63, 1, x_47);
lean_ctor_set(x_63, 2, x_48);
lean_ctor_set(x_63, 3, x_49);
lean_ctor_set(x_63, 4, x_50);
lean_ctor_set(x_63, 5, x_51);
lean_ctor_set(x_63, 6, x_52);
lean_ctor_set(x_63, 7, x_53);
lean_ctor_set(x_63, 8, x_55);
lean_ctor_set(x_63, 9, x_56);
lean_ctor_set(x_63, 10, x_57);
lean_ctor_set(x_63, 11, x_58);
lean_ctor_set(x_63, 12, x_59);
lean_ctor_set(x_63, 13, x_60);
lean_ctor_set(x_63, 14, x_61);
lean_ctor_set(x_63, 15, x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*16, x_54);
lean_ctor_set_tag(x_21, 1);
lean_ctor_set(x_21, 1, x_63);
lean_ctor_set(x_21, 0, x_8);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_21);
lean_ctor_set(x_64, 1, x_46);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_65 = lean_ctor_get(x_21, 1);
lean_inc(x_65);
lean_dec(x_21);
x_66 = lean_st_ref_get(x_9, x_65);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_69 = x_66;
} else {
 lean_dec_ref(x_66);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_67, 2);
lean_inc(x_71);
x_72 = lean_ctor_get(x_67, 3);
lean_inc(x_72);
x_73 = lean_ctor_get(x_67, 4);
lean_inc(x_73);
x_74 = lean_ctor_get(x_67, 5);
lean_inc(x_74);
x_75 = lean_ctor_get(x_67, 6);
lean_inc(x_75);
x_76 = lean_ctor_get(x_67, 7);
lean_inc(x_76);
x_77 = lean_ctor_get_uint8(x_67, sizeof(void*)*16);
x_78 = lean_ctor_get(x_67, 8);
lean_inc(x_78);
x_79 = lean_ctor_get(x_67, 9);
lean_inc(x_79);
x_80 = lean_ctor_get(x_67, 10);
lean_inc(x_80);
x_81 = lean_ctor_get(x_67, 11);
lean_inc(x_81);
x_82 = lean_ctor_get(x_67, 12);
lean_inc(x_82);
x_83 = lean_ctor_get(x_67, 13);
lean_inc(x_83);
x_84 = lean_ctor_get(x_67, 14);
lean_inc(x_84);
x_85 = lean_ctor_get(x_67, 15);
lean_inc(x_85);
lean_dec(x_67);
x_86 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_86, 0, x_7);
lean_ctor_set(x_86, 1, x_70);
lean_ctor_set(x_86, 2, x_71);
lean_ctor_set(x_86, 3, x_72);
lean_ctor_set(x_86, 4, x_73);
lean_ctor_set(x_86, 5, x_74);
lean_ctor_set(x_86, 6, x_75);
lean_ctor_set(x_86, 7, x_76);
lean_ctor_set(x_86, 8, x_78);
lean_ctor_set(x_86, 9, x_79);
lean_ctor_set(x_86, 10, x_80);
lean_ctor_set(x_86, 11, x_81);
lean_ctor_set(x_86, 12, x_82);
lean_ctor_set(x_86, 13, x_83);
lean_ctor_set(x_86, 14, x_84);
lean_ctor_set(x_86, 15, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*16, x_77);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_8);
lean_ctor_set(x_87, 1, x_86);
if (lean_is_scalar(x_69)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_69;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_68);
return x_88;
}
}
else
{
uint8_t x_89; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_89 = !lean_is_exclusive(x_18);
if (x_89 == 0)
{
return x_18;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_18, 0);
x_91 = lean_ctor_get(x_18, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_18);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23) {
_start:
{
lean_object* x_24; 
x_24 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_3, x_4, x_3, x_5, x_19, x_20, x_21, x_22, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_mk_string_unchecked("Lean", 4, 4);
x_28 = lean_mk_string_unchecked("Grind", 5, 5);
x_29 = lean_mk_string_unchecked("intro_with_eq'", 14, 14);
x_30 = l_Lean_Name_mkStr3(x_27, x_28, x_29);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_7);
x_32 = l_Lean_Expr_const___override(x_30, x_31);
x_33 = lean_unsigned_to_nat(5u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_8);
x_36 = lean_array_push(x_35, x_9);
x_37 = lean_array_push(x_36, x_10);
x_38 = lean_array_push(x_37, x_11);
x_39 = lean_array_push(x_38, x_25);
x_40 = l_Lean_mkAppN(x_32, x_39);
lean_dec(x_39);
x_41 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_closeGoal_spec__1(x_12, x_40, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_26);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_st_ref_get(x_15, x_43);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 6);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 7);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_47, sizeof(void*)*16);
x_56 = lean_ctor_get(x_47, 8);
lean_inc(x_56);
x_57 = lean_ctor_get(x_47, 9);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 10);
lean_inc(x_58);
x_59 = lean_ctor_get(x_47, 11);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 12);
lean_inc(x_60);
x_61 = lean_ctor_get(x_47, 13);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 14);
lean_inc(x_62);
x_63 = lean_ctor_get(x_47, 15);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_64, 0, x_13);
lean_ctor_set(x_64, 1, x_48);
lean_ctor_set(x_64, 2, x_49);
lean_ctor_set(x_64, 3, x_50);
lean_ctor_set(x_64, 4, x_51);
lean_ctor_set(x_64, 5, x_52);
lean_ctor_set(x_64, 6, x_53);
lean_ctor_set(x_64, 7, x_54);
lean_ctor_set(x_64, 8, x_56);
lean_ctor_set(x_64, 9, x_57);
lean_ctor_set(x_64, 10, x_58);
lean_ctor_set(x_64, 11, x_59);
lean_ctor_set(x_64, 12, x_60);
lean_ctor_set(x_64, 13, x_61);
lean_ctor_set(x_64, 14, x_62);
lean_ctor_set(x_64, 15, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*16, x_55);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_64);
lean_ctor_set(x_41, 0, x_14);
lean_ctor_set(x_45, 0, x_41);
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_65, sizeof(void*)*16);
x_75 = lean_ctor_get(x_65, 8);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 9);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 10);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 11);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 12);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 13);
lean_inc(x_80);
x_81 = lean_ctor_get(x_65, 14);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 15);
lean_inc(x_82);
lean_dec(x_65);
x_83 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_83, 0, x_13);
lean_ctor_set(x_83, 1, x_67);
lean_ctor_set(x_83, 2, x_68);
lean_ctor_set(x_83, 3, x_69);
lean_ctor_set(x_83, 4, x_70);
lean_ctor_set(x_83, 5, x_71);
lean_ctor_set(x_83, 6, x_72);
lean_ctor_set(x_83, 7, x_73);
lean_ctor_set(x_83, 8, x_75);
lean_ctor_set(x_83, 9, x_76);
lean_ctor_set(x_83, 10, x_77);
lean_ctor_set(x_83, 11, x_78);
lean_ctor_set(x_83, 12, x_79);
lean_ctor_set(x_83, 13, x_80);
lean_ctor_set(x_83, 14, x_81);
lean_ctor_set(x_83, 15, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*16, x_74);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_83);
lean_ctor_set(x_41, 0, x_14);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_41);
lean_ctor_set(x_84, 1, x_66);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_85 = lean_ctor_get(x_41, 1);
lean_inc(x_85);
lean_dec(x_41);
x_86 = lean_st_ref_get(x_15, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 6);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 7);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_87, sizeof(void*)*16);
x_98 = lean_ctor_get(x_87, 8);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 9);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 10);
lean_inc(x_100);
x_101 = lean_ctor_get(x_87, 11);
lean_inc(x_101);
x_102 = lean_ctor_get(x_87, 12);
lean_inc(x_102);
x_103 = lean_ctor_get(x_87, 13);
lean_inc(x_103);
x_104 = lean_ctor_get(x_87, 14);
lean_inc(x_104);
x_105 = lean_ctor_get(x_87, 15);
lean_inc(x_105);
lean_dec(x_87);
x_106 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_106, 0, x_13);
lean_ctor_set(x_106, 1, x_90);
lean_ctor_set(x_106, 2, x_91);
lean_ctor_set(x_106, 3, x_92);
lean_ctor_set(x_106, 4, x_93);
lean_ctor_set(x_106, 5, x_94);
lean_ctor_set(x_106, 6, x_95);
lean_ctor_set(x_106, 7, x_96);
lean_ctor_set(x_106, 8, x_98);
lean_ctor_set(x_106, 9, x_99);
lean_ctor_set(x_106, 10, x_100);
lean_ctor_set(x_106, 11, x_101);
lean_ctor_set(x_106, 12, x_102);
lean_ctor_set(x_106, 13, x_103);
lean_ctor_set(x_106, 14, x_104);
lean_ctor_set(x_106, 15, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*16, x_97);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_14);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_89)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_89;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_88);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_109 = !lean_is_exclusive(x_24);
if (x_109 == 0)
{
return x_24;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_24, 0);
x_111 = lean_ctor_get(x_24, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_24);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22) {
_start:
{
lean_object* x_23; 
x_23 = l_Lean_Meta_mkLambdaFVars(x_1, x_2, x_3, x_4, x_3, x_5, x_18, x_19, x_20, x_21, x_22);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_mk_string_unchecked("Lean", 4, 4);
x_27 = lean_mk_string_unchecked("Grind", 5, 5);
x_28 = lean_mk_string_unchecked("intro_with_eq", 13, 13);
x_29 = l_Lean_Name_mkStr3(x_26, x_27, x_28);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_6);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_Expr_const___override(x_29, x_31);
x_33 = lean_unsigned_to_nat(5u);
x_34 = lean_mk_empty_array_with_capacity(x_33);
x_35 = lean_array_push(x_34, x_7);
x_36 = lean_array_push(x_35, x_8);
x_37 = lean_array_push(x_36, x_9);
x_38 = lean_array_push(x_37, x_10);
x_39 = lean_array_push(x_38, x_24);
x_40 = l_Lean_mkAppN(x_32, x_39);
lean_dec(x_39);
x_41 = l_Lean_MVarId_assign___at___Lean_Meta_Grind_closeGoal_spec__1(x_11, x_40, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_25);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_41, 1);
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_st_ref_get(x_14, x_43);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_47 = lean_ctor_get(x_45, 0);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_47, 3);
lean_inc(x_50);
x_51 = lean_ctor_get(x_47, 4);
lean_inc(x_51);
x_52 = lean_ctor_get(x_47, 5);
lean_inc(x_52);
x_53 = lean_ctor_get(x_47, 6);
lean_inc(x_53);
x_54 = lean_ctor_get(x_47, 7);
lean_inc(x_54);
x_55 = lean_ctor_get_uint8(x_47, sizeof(void*)*16);
x_56 = lean_ctor_get(x_47, 8);
lean_inc(x_56);
x_57 = lean_ctor_get(x_47, 9);
lean_inc(x_57);
x_58 = lean_ctor_get(x_47, 10);
lean_inc(x_58);
x_59 = lean_ctor_get(x_47, 11);
lean_inc(x_59);
x_60 = lean_ctor_get(x_47, 12);
lean_inc(x_60);
x_61 = lean_ctor_get(x_47, 13);
lean_inc(x_61);
x_62 = lean_ctor_get(x_47, 14);
lean_inc(x_62);
x_63 = lean_ctor_get(x_47, 15);
lean_inc(x_63);
lean_dec(x_47);
x_64 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_64, 0, x_12);
lean_ctor_set(x_64, 1, x_48);
lean_ctor_set(x_64, 2, x_49);
lean_ctor_set(x_64, 3, x_50);
lean_ctor_set(x_64, 4, x_51);
lean_ctor_set(x_64, 5, x_52);
lean_ctor_set(x_64, 6, x_53);
lean_ctor_set(x_64, 7, x_54);
lean_ctor_set(x_64, 8, x_56);
lean_ctor_set(x_64, 9, x_57);
lean_ctor_set(x_64, 10, x_58);
lean_ctor_set(x_64, 11, x_59);
lean_ctor_set(x_64, 12, x_60);
lean_ctor_set(x_64, 13, x_61);
lean_ctor_set(x_64, 14, x_62);
lean_ctor_set(x_64, 15, x_63);
lean_ctor_set_uint8(x_64, sizeof(void*)*16, x_55);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_64);
lean_ctor_set(x_41, 0, x_13);
lean_ctor_set(x_45, 0, x_41);
return x_45;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_65 = lean_ctor_get(x_45, 0);
x_66 = lean_ctor_get(x_45, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_45);
x_67 = lean_ctor_get(x_65, 1);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 2);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 3);
lean_inc(x_69);
x_70 = lean_ctor_get(x_65, 4);
lean_inc(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc(x_73);
x_74 = lean_ctor_get_uint8(x_65, sizeof(void*)*16);
x_75 = lean_ctor_get(x_65, 8);
lean_inc(x_75);
x_76 = lean_ctor_get(x_65, 9);
lean_inc(x_76);
x_77 = lean_ctor_get(x_65, 10);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 11);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 12);
lean_inc(x_79);
x_80 = lean_ctor_get(x_65, 13);
lean_inc(x_80);
x_81 = lean_ctor_get(x_65, 14);
lean_inc(x_81);
x_82 = lean_ctor_get(x_65, 15);
lean_inc(x_82);
lean_dec(x_65);
x_83 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_83, 0, x_12);
lean_ctor_set(x_83, 1, x_67);
lean_ctor_set(x_83, 2, x_68);
lean_ctor_set(x_83, 3, x_69);
lean_ctor_set(x_83, 4, x_70);
lean_ctor_set(x_83, 5, x_71);
lean_ctor_set(x_83, 6, x_72);
lean_ctor_set(x_83, 7, x_73);
lean_ctor_set(x_83, 8, x_75);
lean_ctor_set(x_83, 9, x_76);
lean_ctor_set(x_83, 10, x_77);
lean_ctor_set(x_83, 11, x_78);
lean_ctor_set(x_83, 12, x_79);
lean_ctor_set(x_83, 13, x_80);
lean_ctor_set(x_83, 14, x_81);
lean_ctor_set(x_83, 15, x_82);
lean_ctor_set_uint8(x_83, sizeof(void*)*16, x_74);
lean_ctor_set_tag(x_41, 1);
lean_ctor_set(x_41, 1, x_83);
lean_ctor_set(x_41, 0, x_13);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_41);
lean_ctor_set(x_84, 1, x_66);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_85 = lean_ctor_get(x_41, 1);
lean_inc(x_85);
lean_dec(x_41);
x_86 = lean_st_ref_get(x_14, x_85);
x_87 = lean_ctor_get(x_86, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_86)) {
 lean_ctor_release(x_86, 0);
 lean_ctor_release(x_86, 1);
 x_89 = x_86;
} else {
 lean_dec_ref(x_86);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
x_91 = lean_ctor_get(x_87, 2);
lean_inc(x_91);
x_92 = lean_ctor_get(x_87, 3);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 4);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 5);
lean_inc(x_94);
x_95 = lean_ctor_get(x_87, 6);
lean_inc(x_95);
x_96 = lean_ctor_get(x_87, 7);
lean_inc(x_96);
x_97 = lean_ctor_get_uint8(x_87, sizeof(void*)*16);
x_98 = lean_ctor_get(x_87, 8);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 9);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 10);
lean_inc(x_100);
x_101 = lean_ctor_get(x_87, 11);
lean_inc(x_101);
x_102 = lean_ctor_get(x_87, 12);
lean_inc(x_102);
x_103 = lean_ctor_get(x_87, 13);
lean_inc(x_103);
x_104 = lean_ctor_get(x_87, 14);
lean_inc(x_104);
x_105 = lean_ctor_get(x_87, 15);
lean_inc(x_105);
lean_dec(x_87);
x_106 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_106, 0, x_12);
lean_ctor_set(x_106, 1, x_90);
lean_ctor_set(x_106, 2, x_91);
lean_ctor_set(x_106, 3, x_92);
lean_ctor_set(x_106, 4, x_93);
lean_ctor_set(x_106, 5, x_94);
lean_ctor_set(x_106, 6, x_95);
lean_ctor_set(x_106, 7, x_96);
lean_ctor_set(x_106, 8, x_98);
lean_ctor_set(x_106, 9, x_99);
lean_ctor_set(x_106, 10, x_100);
lean_ctor_set(x_106, 11, x_101);
lean_ctor_set(x_106, 12, x_102);
lean_ctor_set(x_106, 13, x_103);
lean_ctor_set(x_106, 14, x_104);
lean_ctor_set(x_106, 15, x_105);
lean_ctor_set_uint8(x_106, sizeof(void*)*16, x_97);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_13);
lean_ctor_set(x_107, 1, x_106);
if (lean_is_scalar(x_89)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_89;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_88);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_109 = !lean_is_exclusive(x_23);
if (x_109 == 0)
{
return x_23;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_23, 0);
x_111 = lean_ctor_get(x_23, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_23);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, uint8_t x_14, lean_object* x_15, lean_object* x_16, lean_object* x_17, lean_object* x_18, lean_object* x_19, lean_object* x_20, lean_object* x_21, lean_object* x_22, lean_object* x_23, lean_object* x_24, lean_object* x_25) {
_start:
{
lean_object* x_26; lean_object* x_43; 
x_43 = lean_ctor_get(x_1, 1);
lean_inc(x_43);
lean_dec(x_1);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
x_44 = l_Lean_Expr_isArrow(x_9);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_expr_instantiate1(x_10, x_4);
lean_dec(x_10);
x_26 = x_45;
goto block_42;
}
else
{
x_26 = x_10;
goto block_42;
}
}
else
{
lean_object* x_46; uint8_t x_47; 
x_46 = lean_ctor_get(x_43, 0);
lean_inc(x_46);
lean_dec(x_43);
x_47 = l_Lean_Expr_isArrow(x_9);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_48 = lean_mk_string_unchecked("Eq", 2, 2);
x_49 = lean_mk_string_unchecked("mpr_prop", 8, 8);
x_50 = l_Lean_Name_mkStr2(x_48, x_49);
x_51 = lean_box(0);
x_52 = l_Lean_Expr_const___override(x_50, x_51);
lean_inc(x_4);
lean_inc(x_46);
lean_inc(x_12);
lean_inc(x_11);
x_53 = l_Lean_mkApp4(x_52, x_11, x_12, x_46, x_4);
x_54 = lean_expr_instantiate1(x_10, x_53);
lean_dec(x_53);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_54);
x_55 = l_Lean_Meta_getLevel(x_54, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_58 = lean_box(2);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_unbox(x_58);
x_61 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_15, x_54, x_60, x_3, x_59, x_21, x_22, x_23, x_24, x_57);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
lean_inc(x_11);
x_64 = l_Lean_Expr_lam___override(x_13, x_11, x_10, x_14);
x_65 = l_Lean_Expr_mvarId_x21(x_62);
x_66 = lean_unsigned_to_nat(1u);
x_67 = lean_mk_empty_array_with_capacity(x_66);
x_68 = lean_array_push(x_67, x_4);
x_69 = lean_box(1);
x_70 = lean_box(x_47);
x_71 = lean_box(x_6);
lean_inc(x_65);
x_72 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed), 23, 14);
lean_closure_set(x_72, 0, x_68);
lean_closure_set(x_72, 1, x_62);
lean_closure_set(x_72, 2, x_70);
lean_closure_set(x_72, 3, x_71);
lean_closure_set(x_72, 4, x_69);
lean_closure_set(x_72, 5, x_56);
lean_closure_set(x_72, 6, x_51);
lean_closure_set(x_72, 7, x_11);
lean_closure_set(x_72, 8, x_12);
lean_closure_set(x_72, 9, x_64);
lean_closure_set(x_72, 10, x_46);
lean_closure_set(x_72, 11, x_7);
lean_closure_set(x_72, 12, x_65);
lean_closure_set(x_72, 13, x_8);
x_73 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(x_65, x_72, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_63);
lean_dec(x_21);
return x_73;
}
else
{
uint8_t x_74; 
lean_dec(x_54);
lean_dec(x_46);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_55);
if (x_74 == 0)
{
return x_55;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_55, 0);
x_76 = lean_ctor_get(x_55, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_55);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_13);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_10);
x_78 = l_Lean_Meta_getLevel(x_10, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_box(2);
x_82 = lean_unsigned_to_nat(0u);
x_83 = lean_unbox(x_81);
lean_inc(x_10);
x_84 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_15, x_10, x_83, x_3, x_82, x_21, x_22, x_23, x_24, x_80);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = l_Lean_Expr_mvarId_x21(x_85);
x_88 = lean_unsigned_to_nat(1u);
x_89 = lean_mk_empty_array_with_capacity(x_88);
x_90 = lean_array_push(x_89, x_4);
x_91 = lean_box(1);
x_92 = lean_box(x_5);
x_93 = lean_box(x_6);
lean_inc(x_87);
x_94 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed), 22, 13);
lean_closure_set(x_94, 0, x_90);
lean_closure_set(x_94, 1, x_85);
lean_closure_set(x_94, 2, x_92);
lean_closure_set(x_94, 3, x_93);
lean_closure_set(x_94, 4, x_91);
lean_closure_set(x_94, 5, x_79);
lean_closure_set(x_94, 6, x_11);
lean_closure_set(x_94, 7, x_12);
lean_closure_set(x_94, 8, x_10);
lean_closure_set(x_94, 9, x_46);
lean_closure_set(x_94, 10, x_7);
lean_closure_set(x_94, 11, x_87);
lean_closure_set(x_94, 12, x_8);
x_95 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(x_87, x_94, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_86);
lean_dec(x_21);
return x_95;
}
else
{
uint8_t x_96; 
lean_dec(x_46);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_96 = !lean_is_exclusive(x_78);
if (x_96 == 0)
{
return x_78;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_78, 0);
x_98 = lean_ctor_get(x_78, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_78);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
}
block_42:
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_27 = lean_box(2);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_unbox(x_27);
x_30 = l_Lean_Meta_mkFreshExprMVarAt(x_2, x_15, x_26, x_29, x_3, x_28, x_21, x_22, x_23, x_24, x_25);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_Expr_mvarId_x21(x_31);
x_34 = lean_unsigned_to_nat(1u);
x_35 = lean_mk_empty_array_with_capacity(x_34);
x_36 = lean_array_push(x_35, x_4);
x_37 = lean_box(1);
x_38 = lean_box(x_5);
x_39 = lean_box(x_6);
lean_inc(x_33);
x_40 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed), 17, 8);
lean_closure_set(x_40, 0, x_36);
lean_closure_set(x_40, 1, x_31);
lean_closure_set(x_40, 2, x_38);
lean_closure_set(x_40, 3, x_39);
lean_closure_set(x_40, 4, x_37);
lean_closure_set(x_40, 5, x_7);
lean_closure_set(x_40, 6, x_33);
lean_closure_set(x_40, 7, x_8);
x_41 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(x_33, x_40, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_32);
lean_dec(x_21);
return x_41;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_26; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_1);
x_11 = lean_st_mk_ref(x_1, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
if (lean_is_exclusive(x_11)) {
 lean_ctor_release(x_11, 0);
 lean_ctor_release(x_11, 1);
 x_14 = x_11;
} else {
 lean_dec_ref(x_11);
 x_14 = lean_box(0);
}
x_34 = lean_st_ref_get(x_12, x_13);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_MVarId_getType(x_37, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; uint8_t x_69; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_69 = l_Lean_Expr_isForall(x_39);
if (x_69 == 0)
{
uint8_t x_70; 
x_70 = l_Lean_Expr_isLet(x_39);
if (x_70 == 0)
{
uint8_t x_71; 
x_71 = l_Lean_Expr_isLetFun(x_39);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_1);
x_15 = x_72;
x_16 = x_40;
goto block_25;
}
else
{
lean_dec(x_1);
goto block_68;
}
}
else
{
lean_dec(x_1);
goto block_68;
}
}
else
{
lean_object* x_73; lean_object* x_74; 
lean_dec(x_2);
lean_dec(x_1);
x_73 = l_Lean_Expr_bindingDomain_x21(x_39);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_73);
x_74 = l_Lean_Meta_isProp(x_73, x_6, x_7, x_8, x_9, x_40);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; uint8_t x_156; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_156 = lean_unbox(x_75);
lean_dec(x_75);
if (x_156 == 0)
{
if (x_69 == 0)
{
x_77 = x_69;
goto block_155;
}
else
{
lean_object* x_157; 
lean_dec(x_73);
lean_dec(x_39);
x_157 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_76);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
if (lean_obj_tag(x_157) == 0)
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = lean_st_ref_get(x_12, x_159);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
lean_ctor_set_tag(x_160, 3);
lean_ctor_set(x_160, 1, x_162);
lean_ctor_set(x_160, 0, x_158);
x_15 = x_160;
x_16 = x_163;
goto block_25;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_160, 0);
x_165 = lean_ctor_get(x_160, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_160);
x_166 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_166, 0, x_158);
lean_ctor_set(x_166, 1, x_164);
x_15 = x_166;
x_16 = x_165;
goto block_25;
}
}
else
{
uint8_t x_167; 
lean_dec(x_14);
lean_dec(x_12);
x_167 = !lean_is_exclusive(x_157);
if (x_167 == 0)
{
return x_157;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_157, 0);
x_169 = lean_ctor_get(x_157, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_157);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_169);
return x_170;
}
}
}
}
else
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_box(0);
x_172 = lean_unbox(x_171);
x_77 = x_172;
goto block_155;
}
block_155:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_st_ref_get(x_12, x_76);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
lean_inc(x_81);
x_82 = l_Lean_MVarId_getTag(x_81, x_6, x_7, x_8, x_9, x_80);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
x_85 = l_Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_84);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_12);
lean_inc(x_73);
x_88 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_preprocessHypothesis(x_73, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_87);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Expr_bindingName_x21(x_39);
x_92 = lean_ctor_get(x_89, 0);
lean_inc(x_92);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_92);
lean_inc(x_91);
x_93 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_mkCleanName(x_91, x_92, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_90);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Meta_getLocalInstances___redArg(x_6, x_95);
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_92);
x_100 = l_Lean_Meta_isClass_x3f(x_92, x_6, x_7, x_8, x_9, x_99);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = lean_ctor_get(x_6, 2);
lean_inc(x_103);
x_104 = lean_box(0);
x_105 = l_Lean_Expr_bindingBody_x21(x_39);
lean_inc(x_86);
x_106 = l_Lean_Expr_fvar___override(x_86);
x_107 = l_Lean_Expr_bindingInfo_x21(x_39);
x_108 = lean_unbox(x_104);
lean_inc(x_92);
lean_inc(x_86);
x_109 = l_Lean_LocalContext_mkLocalDecl(x_103, x_86, x_94, x_92, x_107, x_108);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_110; lean_object* x_111; 
lean_free_object(x_96);
x_110 = lean_box(0);
lean_inc(x_12);
x_111 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(x_89, x_109, x_83, x_106, x_77, x_69, x_81, x_86, x_39, x_105, x_73, x_92, x_91, x_107, x_98, x_110, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_39);
x_26 = x_111;
goto block_33;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_ctor_get(x_101, 0);
lean_inc(x_112);
lean_dec(x_101);
lean_inc(x_106);
lean_ctor_set(x_96, 1, x_106);
lean_ctor_set(x_96, 0, x_112);
x_113 = lean_array_push(x_98, x_96);
x_114 = lean_box(0);
lean_inc(x_12);
x_115 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(x_89, x_109, x_83, x_106, x_77, x_69, x_81, x_86, x_39, x_105, x_73, x_92, x_91, x_107, x_113, x_114, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_102);
lean_dec(x_39);
x_26 = x_115;
goto block_33;
}
}
else
{
uint8_t x_116; 
lean_free_object(x_96);
lean_dec(x_98);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_116 = !lean_is_exclusive(x_100);
if (x_116 == 0)
{
return x_100;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_117 = lean_ctor_get(x_100, 0);
x_118 = lean_ctor_get(x_100, 1);
lean_inc(x_118);
lean_inc(x_117);
lean_dec(x_100);
x_119 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_119, 0, x_117);
lean_ctor_set(x_119, 1, x_118);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_96, 0);
x_121 = lean_ctor_get(x_96, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_96);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_92);
x_122 = l_Lean_Meta_isClass_x3f(x_92, x_6, x_7, x_8, x_9, x_121);
if (lean_obj_tag(x_122) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; uint8_t x_130; lean_object* x_131; 
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
x_125 = lean_ctor_get(x_6, 2);
lean_inc(x_125);
x_126 = lean_box(0);
x_127 = l_Lean_Expr_bindingBody_x21(x_39);
lean_inc(x_86);
x_128 = l_Lean_Expr_fvar___override(x_86);
x_129 = l_Lean_Expr_bindingInfo_x21(x_39);
x_130 = lean_unbox(x_126);
lean_inc(x_92);
lean_inc(x_86);
x_131 = l_Lean_LocalContext_mkLocalDecl(x_125, x_86, x_94, x_92, x_129, x_130);
if (lean_obj_tag(x_123) == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_box(0);
lean_inc(x_12);
x_133 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(x_89, x_131, x_83, x_128, x_77, x_69, x_81, x_86, x_39, x_127, x_73, x_92, x_91, x_129, x_120, x_132, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_124);
lean_dec(x_39);
x_26 = x_133;
goto block_33;
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_134 = lean_ctor_get(x_123, 0);
lean_inc(x_134);
lean_dec(x_123);
lean_inc(x_128);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_128);
x_136 = lean_array_push(x_120, x_135);
x_137 = lean_box(0);
lean_inc(x_12);
x_138 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(x_89, x_131, x_83, x_128, x_77, x_69, x_81, x_86, x_39, x_127, x_73, x_92, x_91, x_129, x_136, x_137, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_124);
lean_dec(x_39);
x_26 = x_138;
goto block_33;
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_120);
lean_dec(x_94);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_139 = lean_ctor_get(x_122, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_122, 1);
lean_inc(x_140);
if (lean_is_exclusive(x_122)) {
 lean_ctor_release(x_122, 0);
 lean_ctor_release(x_122, 1);
 x_141 = x_122;
} else {
 lean_dec_ref(x_122);
 x_141 = lean_box(0);
}
if (lean_is_scalar(x_141)) {
 x_142 = lean_alloc_ctor(1, 2, 0);
} else {
 x_142 = x_141;
}
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_140);
return x_142;
}
}
}
else
{
uint8_t x_143; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_89);
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_143 = !lean_is_exclusive(x_93);
if (x_143 == 0)
{
return x_93;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; 
x_144 = lean_ctor_get(x_93, 0);
x_145 = lean_ctor_get(x_93, 1);
lean_inc(x_145);
lean_inc(x_144);
lean_dec(x_93);
x_146 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
return x_146;
}
}
}
else
{
uint8_t x_147; 
lean_dec(x_86);
lean_dec(x_83);
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_147 = !lean_is_exclusive(x_88);
if (x_147 == 0)
{
return x_88;
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; 
x_148 = lean_ctor_get(x_88, 0);
x_149 = lean_ctor_get(x_88, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_88);
x_150 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_150, 0, x_148);
lean_ctor_set(x_150, 1, x_149);
return x_150;
}
}
}
else
{
uint8_t x_151; 
lean_dec(x_81);
lean_dec(x_73);
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_151 = !lean_is_exclusive(x_82);
if (x_151 == 0)
{
return x_82;
}
else
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_152 = lean_ctor_get(x_82, 0);
x_153 = lean_ctor_get(x_82, 1);
lean_inc(x_153);
lean_inc(x_152);
lean_dec(x_82);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
return x_154;
}
}
}
}
else
{
uint8_t x_173; 
lean_dec(x_73);
lean_dec(x_39);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_173 = !lean_is_exclusive(x_74);
if (x_173 == 0)
{
return x_74;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_74, 0);
x_175 = lean_ctor_get(x_74, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_74);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
block_68:
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_Meta_Grind_getConfig___redArg(x_4, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get_uint8(x_42, sizeof(void*)*7 + 14);
lean_dec(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_39);
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_45 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_intro1(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_st_ref_get(x_12, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__0), 11, 2);
lean_closure_set(x_51, 0, x_46);
lean_closure_set(x_51, 1, x_2);
x_52 = lean_ctor_get(x_49, 0);
lean_inc(x_52);
lean_dec(x_49);
lean_inc(x_12);
x_53 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(x_52, x_51, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_50);
lean_dec(x_6);
x_26 = x_53;
goto block_33;
}
else
{
uint8_t x_54; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_54 = !lean_is_exclusive(x_45);
if (x_54 == 0)
{
return x_45;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_45, 0);
x_56 = lean_ctor_get(x_45, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_45);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_58 = lean_ctor_get(x_41, 1);
lean_inc(x_58);
lean_dec(x_41);
x_59 = lean_st_ref_get(x_12, x_58);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_unsigned_to_nat(0u);
x_63 = lean_mk_empty_array_with_capacity(x_62);
x_64 = l_Lean_Meta_expandLet(x_39, x_63);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
lean_dec(x_60);
lean_inc(x_65);
x_66 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed), 12, 3);
lean_closure_set(x_66, 0, x_65);
lean_closure_set(x_66, 1, x_64);
lean_closure_set(x_66, 2, x_2);
lean_inc(x_12);
x_67 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(x_65, x_66, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_61);
lean_dec(x_6);
x_26 = x_67;
goto block_33;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_38);
if (x_177 == 0)
{
return x_38;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_38, 0);
x_179 = lean_ctor_get(x_38, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_38);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
block_25:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_get(x_12, x_16);
lean_dec(x_12);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
if (lean_is_scalar(x_14)) {
 x_20 = lean_alloc_ctor(0, 2, 0);
} else {
 x_20 = x_14;
}
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_17, 0);
x_22 = lean_ctor_get(x_17, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_17);
if (lean_is_scalar(x_14)) {
 x_23 = lean_alloc_ctor(0, 2, 0);
} else {
 x_23 = x_14;
}
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
block_33:
{
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_15 = x_27;
x_16 = x_28;
goto block_25;
}
else
{
uint8_t x_29; 
lean_dec(x_14);
lean_dec(x_12);
x_29 = !lean_is_exclusive(x_26);
if (x_29 == 0)
{
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 0);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_26);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_1);
x_11 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__6), 10, 2);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_12, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_13, 0);
x_18 = lean_ctor_get(x_13, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_13);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_13);
if (x_21 == 0)
{
return x_13;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_13, 0);
x_23 = lean_ctor_get(x_13, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_13);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshId___at___Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_mkFreshFVarId___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2___boxed(lean_object** _args) {
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
_start:
{
uint8_t x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; 
x_18 = lean_unbox(x_3);
lean_dec(x_3);
x_19 = lean_unbox(x_4);
lean_dec(x_4);
x_20 = lean_unbox(x_5);
lean_dec(x_5);
x_21 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__2(x_1, x_2, x_18, x_19, x_20, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
return x_21;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
_start:
{
uint8_t x_24; uint8_t x_25; uint8_t x_26; lean_object* x_27; 
x_24 = lean_unbox(x_3);
lean_dec(x_3);
x_25 = lean_unbox(x_4);
lean_dec(x_4);
x_26 = lean_unbox(x_5);
lean_dec(x_5);
x_27 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__3(x_1, x_2, x_24, x_25, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_1);
return x_27;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
_start:
{
uint8_t x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; 
x_23 = lean_unbox(x_3);
lean_dec(x_3);
x_24 = lean_unbox(x_4);
lean_dec(x_4);
x_25 = lean_unbox(x_5);
lean_dec(x_5);
x_26 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__4(x_1, x_2, x_23, x_24, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
return x_26;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5___boxed(lean_object** _args) {
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
lean_object* x_22 = _args[21];
lean_object* x_23 = _args[22];
lean_object* x_24 = _args[23];
lean_object* x_25 = _args[24];
_start:
{
uint8_t x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; 
x_26 = lean_unbox(x_5);
lean_dec(x_5);
x_27 = lean_unbox(x_6);
lean_dec(x_6);
x_28 = lean_unbox(x_14);
lean_dec(x_14);
x_29 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___lam__5(x_1, x_2, x_3, x_4, x_26, x_27, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_28, x_15, x_16, x_17, x_18, x_19, x_20, x_21, x_22, x_23, x_24, x_25);
lean_dec(x_16);
lean_dec(x_9);
return x_29;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Expr_getAppFn(x_2);
if (lean_obj_tag(x_3) == 4)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_1, 13);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_Meta_Grind_CasesTypes_isEagerSplit(x_6, x_4);
lean_dec(x_4);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_dec(x_3);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Expr_getAppFn(x_1);
if (lean_obj_tag(x_5) == 4)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_getConstInfo___at_____private_Lean_Compiler_InlineAttrs_0__Lean_Compiler_isValidMacroInline_spec__0(x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 5)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l_Lean_InductiveVal_numCtors(x_11);
lean_dec(x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_dec_le(x_12, x_13);
lean_dec(x_12);
x_15 = lean_box(x_14);
lean_ctor_set(x_7, 0, x_15);
return x_7;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
lean_dec(x_8);
x_18 = l_Lean_InductiveVal_numCtors(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_le(x_18, x_19);
lean_dec(x_18);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
return x_22;
}
}
else
{
uint8_t x_23; 
lean_dec(x_8);
x_23 = !lean_is_exclusive(x_7);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_7, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_7, 0, x_25);
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 1);
lean_inc(x_26);
lean_dec(x_7);
x_27 = lean_box(0);
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
x_29 = !lean_is_exclusive(x_7);
if (x_29 == 0)
{
return x_7;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_7, 0);
x_31 = lean_ctor_get(x_7, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_7);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_dec(x_5);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_4);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; 
x_4 = l_List_reverse___redArg(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_6 = lean_ctor_get(x_2, 0);
x_7 = lean_ctor_get(x_2, 1);
x_8 = lean_ctor_get(x_1, 1);
x_9 = lean_ctor_get(x_1, 2);
x_10 = lean_ctor_get(x_1, 3);
x_11 = lean_ctor_get(x_1, 4);
x_12 = lean_ctor_get(x_1, 5);
x_13 = lean_ctor_get(x_1, 6);
x_14 = lean_ctor_get(x_1, 7);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_16 = lean_ctor_get(x_1, 8);
x_17 = lean_ctor_get(x_1, 9);
x_18 = lean_ctor_get(x_1, 10);
x_19 = lean_ctor_get(x_1, 11);
x_20 = lean_ctor_get(x_1, 12);
x_21 = lean_ctor_get(x_1, 13);
x_22 = lean_ctor_get(x_1, 14);
x_23 = lean_ctor_get(x_1, 15);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_24 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_8);
lean_ctor_set(x_24, 2, x_9);
lean_ctor_set(x_24, 3, x_10);
lean_ctor_set(x_24, 4, x_11);
lean_ctor_set(x_24, 5, x_12);
lean_ctor_set(x_24, 6, x_13);
lean_ctor_set(x_24, 7, x_14);
lean_ctor_set(x_24, 8, x_16);
lean_ctor_set(x_24, 9, x_17);
lean_ctor_set(x_24, 10, x_18);
lean_ctor_set(x_24, 11, x_19);
lean_ctor_set(x_24, 12, x_20);
lean_ctor_set(x_24, 13, x_21);
lean_ctor_set(x_24, 14, x_22);
lean_ctor_set(x_24, 15, x_23);
lean_ctor_set_uint8(x_24, sizeof(void*)*16, x_15);
lean_ctor_set(x_2, 1, x_3);
lean_ctor_set(x_2, 0, x_24);
{
lean_object* _tmp_1 = x_7;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_26 = lean_ctor_get(x_2, 0);
x_27 = lean_ctor_get(x_2, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_2);
x_28 = lean_ctor_get(x_1, 1);
x_29 = lean_ctor_get(x_1, 2);
x_30 = lean_ctor_get(x_1, 3);
x_31 = lean_ctor_get(x_1, 4);
x_32 = lean_ctor_get(x_1, 5);
x_33 = lean_ctor_get(x_1, 6);
x_34 = lean_ctor_get(x_1, 7);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_36 = lean_ctor_get(x_1, 8);
x_37 = lean_ctor_get(x_1, 9);
x_38 = lean_ctor_get(x_1, 10);
x_39 = lean_ctor_get(x_1, 11);
x_40 = lean_ctor_get(x_1, 12);
x_41 = lean_ctor_get(x_1, 13);
x_42 = lean_ctor_get(x_1, 14);
x_43 = lean_ctor_get(x_1, 15);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
x_44 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_28);
lean_ctor_set(x_44, 2, x_29);
lean_ctor_set(x_44, 3, x_30);
lean_ctor_set(x_44, 4, x_31);
lean_ctor_set(x_44, 5, x_32);
lean_ctor_set(x_44, 6, x_33);
lean_ctor_set(x_44, 7, x_34);
lean_ctor_set(x_44, 8, x_36);
lean_ctor_set(x_44, 9, x_37);
lean_ctor_set(x_44, 10, x_38);
lean_ctor_set(x_44, 11, x_39);
lean_ctor_set(x_44, 12, x_40);
lean_ctor_set(x_44, 13, x_41);
lean_ctor_set(x_44, 14, x_42);
lean_ctor_set(x_44, 15, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*16, x_35);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_3);
x_2 = x_27;
x_3 = x_45;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = l_Lean_Meta_Grind_cases(x_2, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_box(0);
x_18 = l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f_spec__0(x_3, x_16, x_17);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_20 = lean_ctor_get(x_14, 0);
x_21 = lean_ctor_get(x_14, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_14);
x_22 = lean_box(0);
x_23 = l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f_spec__0(x_3, x_20, x_22);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
return x_14;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_14);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_8);
x_13 = l_Lean_FVarId_getType___redArg(x_1, x_8, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = lean_whnf(x_14, x_8, x_9, x_10, x_11, x_15);
if (lean_obj_tag(x_16) == 0)
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_2, x_18);
if (x_20 == 0)
{
lean_object* x_83; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_83 = lean_box(0);
lean_ctor_set(x_16, 0, x_83);
return x_16;
}
else
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_free_object(x_16);
x_84 = l_Lean_Meta_Grind_cheapCasesOnly(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_19);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_unbox(x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_84, 1);
lean_inc(x_87);
lean_dec(x_84);
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = x_11;
x_28 = x_87;
goto block_82;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_84, 1);
lean_inc(x_88);
lean_dec(x_84);
x_89 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(x_18, x_10, x_11, x_88);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; uint8_t x_91; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_unbox(x_90);
lean_dec(x_90);
if (x_91 == 0)
{
uint8_t x_92; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_92 = !lean_is_exclusive(x_89);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_ctor_get(x_89, 0);
lean_dec(x_93);
x_94 = lean_box(0);
lean_ctor_set(x_89, 0, x_94);
return x_89;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_89, 1);
lean_inc(x_95);
lean_dec(x_89);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_95);
return x_97;
}
}
else
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_89, 1);
lean_inc(x_98);
lean_dec(x_89);
x_21 = x_5;
x_22 = x_6;
x_23 = x_7;
x_24 = x_8;
x_25 = x_9;
x_26 = x_10;
x_27 = x_11;
x_28 = x_98;
goto block_82;
}
}
else
{
uint8_t x_99; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_99 = !lean_is_exclusive(x_89);
if (x_99 == 0)
{
return x_89;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_89, 0);
x_101 = lean_ctor_get(x_89, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_89);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
}
}
block_82:
{
lean_object* x_29; 
x_29 = l_Lean_Expr_getAppFn(x_18);
lean_dec(x_18);
switch (lean_obj_tag(x_29)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_4);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
lean_dec(x_29);
x_31 = l_Lean_Expr_bvar___override(x_30);
x_32 = lean_apply_9(x_3, x_31, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_32;
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_4);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Expr_fvar___override(x_33);
x_35 = lean_apply_9(x_3, x_34, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_35;
}
case 2:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_4);
x_36 = lean_ctor_get(x_29, 0);
lean_inc(x_36);
lean_dec(x_29);
x_37 = l_Lean_Expr_mvar___override(x_36);
x_38 = lean_apply_9(x_3, x_37, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_38;
}
case 3:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_4);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = l_Lean_Expr_sort___override(x_39);
x_41 = lean_apply_9(x_3, x_40, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_41;
}
case 4:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_3);
x_42 = lean_ctor_get(x_29, 0);
lean_inc(x_42);
lean_dec(x_29);
x_43 = l_Lean_Meta_Grind_saveCases(x_42, x_20, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_45 = lean_box(0);
x_46 = lean_apply_9(x_4, x_45, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_44);
return x_46;
}
case 5:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
x_47 = lean_ctor_get(x_29, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_29, 1);
lean_inc(x_48);
lean_dec(x_29);
x_49 = l_Lean_Expr_app___override(x_47, x_48);
x_50 = lean_apply_9(x_3, x_49, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_50;
}
case 6:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_4);
x_51 = lean_ctor_get(x_29, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_29, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_29, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_29, sizeof(void*)*3 + 8);
lean_dec(x_29);
x_55 = l_Lean_Expr_lam___override(x_51, x_52, x_53, x_54);
x_56 = lean_apply_9(x_3, x_55, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_56;
}
case 7:
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_4);
x_57 = lean_ctor_get(x_29, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_29, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_29, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_29, sizeof(void*)*3 + 8);
lean_dec(x_29);
x_61 = l_Lean_Expr_forallE___override(x_57, x_58, x_59, x_60);
x_62 = lean_apply_9(x_3, x_61, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_62;
}
case 8:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_4);
x_63 = lean_ctor_get(x_29, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_29, 1);
lean_inc(x_64);
x_65 = lean_ctor_get(x_29, 2);
lean_inc(x_65);
x_66 = lean_ctor_get(x_29, 3);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_29, sizeof(void*)*4 + 8);
lean_dec(x_29);
x_68 = l_Lean_Expr_letE___override(x_63, x_64, x_65, x_66, x_67);
x_69 = lean_apply_9(x_3, x_68, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_69;
}
case 9:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_4);
x_70 = lean_ctor_get(x_29, 0);
lean_inc(x_70);
lean_dec(x_29);
x_71 = l_Lean_Expr_lit___override(x_70);
x_72 = lean_apply_9(x_3, x_71, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_72;
}
case 10:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_4);
x_73 = lean_ctor_get(x_29, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_29, 1);
lean_inc(x_74);
lean_dec(x_29);
x_75 = l_Lean_Expr_mdata___override(x_73, x_74);
x_76 = lean_apply_9(x_3, x_75, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_76;
}
default: 
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
lean_dec(x_4);
x_77 = lean_ctor_get(x_29, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_29, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_29, 2);
lean_inc(x_79);
lean_dec(x_29);
x_80 = l_Lean_Expr_proj___override(x_77, x_78, x_79);
x_81 = lean_apply_9(x_3, x_80, x_21, x_22, x_23, x_24, x_25, x_26, x_27, x_28);
return x_81;
}
}
}
}
else
{
lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_103 = lean_ctor_get(x_16, 0);
x_104 = lean_ctor_get(x_16, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_16);
x_105 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_2, x_103);
if (x_105 == 0)
{
lean_object* x_168; lean_object* x_169; 
lean_dec(x_103);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_168 = lean_box(0);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_168);
lean_ctor_set(x_169, 1, x_104);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; uint8_t x_172; 
x_170 = l_Lean_Meta_Grind_cheapCasesOnly(x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_104);
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
lean_object* x_173; 
x_173 = lean_ctor_get(x_170, 1);
lean_inc(x_173);
lean_dec(x_170);
x_106 = x_5;
x_107 = x_6;
x_108 = x_7;
x_109 = x_8;
x_110 = x_9;
x_111 = x_10;
x_112 = x_11;
x_113 = x_173;
goto block_167;
}
else
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_170, 1);
lean_inc(x_174);
lean_dec(x_170);
x_175 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isCheapInductive(x_103, x_10, x_11, x_174);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; uint8_t x_177; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_unbox(x_176);
lean_dec(x_176);
if (x_177 == 0)
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_103);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_178 = lean_ctor_get(x_175, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_179 = x_175;
} else {
 lean_dec_ref(x_175);
 x_179 = lean_box(0);
}
x_180 = lean_box(0);
if (lean_is_scalar(x_179)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_179;
}
lean_ctor_set(x_181, 0, x_180);
lean_ctor_set(x_181, 1, x_178);
return x_181;
}
else
{
lean_object* x_182; 
x_182 = lean_ctor_get(x_175, 1);
lean_inc(x_182);
lean_dec(x_175);
x_106 = x_5;
x_107 = x_6;
x_108 = x_7;
x_109 = x_8;
x_110 = x_9;
x_111 = x_10;
x_112 = x_11;
x_113 = x_182;
goto block_167;
}
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_103);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_183 = lean_ctor_get(x_175, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_175, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_175)) {
 lean_ctor_release(x_175, 0);
 lean_ctor_release(x_175, 1);
 x_185 = x_175;
} else {
 lean_dec_ref(x_175);
 x_185 = lean_box(0);
}
if (lean_is_scalar(x_185)) {
 x_186 = lean_alloc_ctor(1, 2, 0);
} else {
 x_186 = x_185;
}
lean_ctor_set(x_186, 0, x_183);
lean_ctor_set(x_186, 1, x_184);
return x_186;
}
}
}
block_167:
{
lean_object* x_114; 
x_114 = l_Lean_Expr_getAppFn(x_103);
lean_dec(x_103);
switch (lean_obj_tag(x_114)) {
case 0:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_4);
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
lean_dec(x_114);
x_116 = l_Lean_Expr_bvar___override(x_115);
x_117 = lean_apply_9(x_3, x_116, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_117;
}
case 1:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_4);
x_118 = lean_ctor_get(x_114, 0);
lean_inc(x_118);
lean_dec(x_114);
x_119 = l_Lean_Expr_fvar___override(x_118);
x_120 = lean_apply_9(x_3, x_119, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_120;
}
case 2:
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_4);
x_121 = lean_ctor_get(x_114, 0);
lean_inc(x_121);
lean_dec(x_114);
x_122 = l_Lean_Expr_mvar___override(x_121);
x_123 = lean_apply_9(x_3, x_122, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_123;
}
case 3:
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_4);
x_124 = lean_ctor_get(x_114, 0);
lean_inc(x_124);
lean_dec(x_114);
x_125 = l_Lean_Expr_sort___override(x_124);
x_126 = lean_apply_9(x_3, x_125, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_126;
}
case 4:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
lean_dec(x_3);
x_127 = lean_ctor_get(x_114, 0);
lean_inc(x_127);
lean_dec(x_114);
x_128 = l_Lean_Meta_Grind_saveCases(x_127, x_105, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
x_129 = lean_ctor_get(x_128, 1);
lean_inc(x_129);
lean_dec(x_128);
x_130 = lean_box(0);
x_131 = lean_apply_9(x_4, x_130, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_129);
return x_131;
}
case 5:
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
lean_dec(x_4);
x_132 = lean_ctor_get(x_114, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_114, 1);
lean_inc(x_133);
lean_dec(x_114);
x_134 = l_Lean_Expr_app___override(x_132, x_133);
x_135 = lean_apply_9(x_3, x_134, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_135;
}
case 6:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; lean_object* x_140; lean_object* x_141; 
lean_dec(x_4);
x_136 = lean_ctor_get(x_114, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_114, 1);
lean_inc(x_137);
x_138 = lean_ctor_get(x_114, 2);
lean_inc(x_138);
x_139 = lean_ctor_get_uint8(x_114, sizeof(void*)*3 + 8);
lean_dec(x_114);
x_140 = l_Lean_Expr_lam___override(x_136, x_137, x_138, x_139);
x_141 = lean_apply_9(x_3, x_140, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_141;
}
case 7:
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_4);
x_142 = lean_ctor_get(x_114, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_114, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_114, 2);
lean_inc(x_144);
x_145 = lean_ctor_get_uint8(x_114, sizeof(void*)*3 + 8);
lean_dec(x_114);
x_146 = l_Lean_Expr_forallE___override(x_142, x_143, x_144, x_145);
x_147 = lean_apply_9(x_3, x_146, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_147;
}
case 8:
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; uint8_t x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_4);
x_148 = lean_ctor_get(x_114, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_114, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_114, 2);
lean_inc(x_150);
x_151 = lean_ctor_get(x_114, 3);
lean_inc(x_151);
x_152 = lean_ctor_get_uint8(x_114, sizeof(void*)*4 + 8);
lean_dec(x_114);
x_153 = l_Lean_Expr_letE___override(x_148, x_149, x_150, x_151, x_152);
x_154 = lean_apply_9(x_3, x_153, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_154;
}
case 9:
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_4);
x_155 = lean_ctor_get(x_114, 0);
lean_inc(x_155);
lean_dec(x_114);
x_156 = l_Lean_Expr_lit___override(x_155);
x_157 = lean_apply_9(x_3, x_156, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_157;
}
case 10:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_4);
x_158 = lean_ctor_get(x_114, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_114, 1);
lean_inc(x_159);
lean_dec(x_114);
x_160 = l_Lean_Expr_mdata___override(x_158, x_159);
x_161 = lean_apply_9(x_3, x_160, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_161;
}
default: 
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
lean_dec(x_4);
x_162 = lean_ctor_get(x_114, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_114, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_114, 2);
lean_inc(x_164);
lean_dec(x_114);
x_165 = l_Lean_Expr_proj___override(x_162, x_163, x_164);
x_166 = lean_apply_9(x_3, x_165, x_106, x_107, x_108, x_109, x_110, x_111, x_112, x_113);
return x_166;
}
}
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_187 = !lean_is_exclusive(x_16);
if (x_187 == 0)
{
return x_16;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_16, 0);
x_189 = lean_ctor_get(x_16, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_16);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_191 = !lean_is_exclusive(x_13);
if (x_191 == 0)
{
return x_13;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_13, 0);
x_193 = lean_ctor_get(x_13, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_13);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_inc(x_1);
lean_inc(x_11);
lean_inc(x_2);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__0___boxed), 12, 3);
lean_closure_set(x_12, 0, x_2);
lean_closure_set(x_12, 1, x_11);
lean_closure_set(x_12, 2, x_1);
lean_inc(x_12);
x_13 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__1___boxed), 10, 1);
lean_closure_set(x_13, 0, x_12);
x_14 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__2), 12, 4);
lean_closure_set(x_14, 0, x_2);
lean_closure_set(x_14, 1, x_1);
lean_closure_set(x_14, 2, x_13);
lean_closure_set(x_14, 3, x_12);
x_15 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_11, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_Meta_Grind_injection_x3f(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_20 = lean_ctor_get(x_10, 0);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 4);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 7);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_29 = lean_ctor_get(x_1, 8);
lean_inc(x_29);
x_30 = lean_ctor_get(x_1, 9);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 10);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 11);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 12);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 13);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 14);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 15);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_37, 0, x_20);
lean_ctor_set(x_37, 1, x_21);
lean_ctor_set(x_37, 2, x_22);
lean_ctor_set(x_37, 3, x_23);
lean_ctor_set(x_37, 4, x_24);
lean_ctor_set(x_37, 5, x_25);
lean_ctor_set(x_37, 6, x_26);
lean_ctor_set(x_37, 7, x_27);
lean_ctor_set(x_37, 8, x_29);
lean_ctor_set(x_37, 9, x_30);
lean_ctor_set(x_37, 10, x_31);
lean_ctor_set(x_37, 11, x_32);
lean_ctor_set(x_37, 12, x_33);
lean_ctor_set(x_37, 13, x_34);
lean_ctor_set(x_37, 14, x_35);
lean_ctor_set(x_37, 15, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*16, x_28);
lean_ctor_set(x_10, 0, x_37);
return x_9;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_38 = lean_ctor_get(x_10, 0);
lean_inc(x_38);
lean_dec(x_10);
x_39 = lean_ctor_get(x_1, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_1, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_1, 3);
lean_inc(x_41);
x_42 = lean_ctor_get(x_1, 4);
lean_inc(x_42);
x_43 = lean_ctor_get(x_1, 5);
lean_inc(x_43);
x_44 = lean_ctor_get(x_1, 6);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 7);
lean_inc(x_45);
x_46 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_47 = lean_ctor_get(x_1, 8);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 9);
lean_inc(x_48);
x_49 = lean_ctor_get(x_1, 10);
lean_inc(x_49);
x_50 = lean_ctor_get(x_1, 11);
lean_inc(x_50);
x_51 = lean_ctor_get(x_1, 12);
lean_inc(x_51);
x_52 = lean_ctor_get(x_1, 13);
lean_inc(x_52);
x_53 = lean_ctor_get(x_1, 14);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 15);
lean_inc(x_54);
lean_dec(x_1);
x_55 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_55, 0, x_38);
lean_ctor_set(x_55, 1, x_39);
lean_ctor_set(x_55, 2, x_40);
lean_ctor_set(x_55, 3, x_41);
lean_ctor_set(x_55, 4, x_42);
lean_ctor_set(x_55, 5, x_43);
lean_ctor_set(x_55, 6, x_44);
lean_ctor_set(x_55, 7, x_45);
lean_ctor_set(x_55, 8, x_47);
lean_ctor_set(x_55, 9, x_48);
lean_ctor_set(x_55, 10, x_49);
lean_ctor_set(x_55, 11, x_50);
lean_ctor_set(x_55, 12, x_51);
lean_ctor_set(x_55, 13, x_52);
lean_ctor_set(x_55, 14, x_53);
lean_ctor_set(x_55, 15, x_54);
lean_ctor_set_uint8(x_55, sizeof(void*)*16, x_46);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_9, 0, x_56);
return x_9;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_57 = lean_ctor_get(x_9, 1);
lean_inc(x_57);
lean_dec(x_9);
x_58 = lean_ctor_get(x_10, 0);
lean_inc(x_58);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 x_59 = x_10;
} else {
 lean_dec_ref(x_10);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_1, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 2);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 3);
lean_inc(x_62);
x_63 = lean_ctor_get(x_1, 4);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 5);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 6);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 7);
lean_inc(x_66);
x_67 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_68 = lean_ctor_get(x_1, 8);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 9);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 10);
lean_inc(x_70);
x_71 = lean_ctor_get(x_1, 11);
lean_inc(x_71);
x_72 = lean_ctor_get(x_1, 12);
lean_inc(x_72);
x_73 = lean_ctor_get(x_1, 13);
lean_inc(x_73);
x_74 = lean_ctor_get(x_1, 14);
lean_inc(x_74);
x_75 = lean_ctor_get(x_1, 15);
lean_inc(x_75);
lean_dec(x_1);
x_76 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_76, 0, x_58);
lean_ctor_set(x_76, 1, x_60);
lean_ctor_set(x_76, 2, x_61);
lean_ctor_set(x_76, 3, x_62);
lean_ctor_set(x_76, 4, x_63);
lean_ctor_set(x_76, 5, x_64);
lean_ctor_set(x_76, 6, x_65);
lean_ctor_set(x_76, 7, x_66);
lean_ctor_set(x_76, 8, x_68);
lean_ctor_set(x_76, 9, x_69);
lean_ctor_set(x_76, 10, x_70);
lean_ctor_set(x_76, 11, x_71);
lean_ctor_set(x_76, 12, x_72);
lean_ctor_set(x_76, 13, x_73);
lean_ctor_set(x_76, 14, x_74);
lean_ctor_set(x_76, 15, x_75);
lean_ctor_set_uint8(x_76, sizeof(void*)*16, x_67);
if (lean_is_scalar(x_59)) {
 x_77 = lean_alloc_ctor(1, 1, 0);
} else {
 x_77 = x_59;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_57);
return x_78;
}
}
}
else
{
uint8_t x_79; 
lean_dec(x_1);
x_79 = !lean_is_exclusive(x_9);
if (x_79 == 0)
{
return x_9;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_9, 0);
x_81 = lean_ctor_get(x_9, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_9);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_1);
x_8 = l_Lean_MVarId_getType(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_11 = l_Lean_Meta_isProp(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_MVarId_exfalso(x_1, x_3, x_4, x_5, x_6, x_14);
lean_dec(x_3);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_2, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_2, 4);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 5);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 6);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 7);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*16);
x_26 = lean_ctor_get(x_2, 8);
lean_inc(x_26);
x_27 = lean_ctor_get(x_2, 9);
lean_inc(x_27);
x_28 = lean_ctor_get(x_2, 10);
lean_inc(x_28);
x_29 = lean_ctor_get(x_2, 11);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 12);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 13);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 14);
lean_inc(x_32);
x_33 = lean_ctor_get(x_2, 15);
lean_inc(x_33);
lean_dec(x_2);
x_34 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_34, 0, x_17);
lean_ctor_set(x_34, 1, x_18);
lean_ctor_set(x_34, 2, x_19);
lean_ctor_set(x_34, 3, x_20);
lean_ctor_set(x_34, 4, x_21);
lean_ctor_set(x_34, 5, x_22);
lean_ctor_set(x_34, 6, x_23);
lean_ctor_set(x_34, 7, x_24);
lean_ctor_set(x_34, 8, x_26);
lean_ctor_set(x_34, 9, x_27);
lean_ctor_set(x_34, 10, x_28);
lean_ctor_set(x_34, 11, x_29);
lean_ctor_set(x_34, 12, x_30);
lean_ctor_set(x_34, 13, x_31);
lean_ctor_set(x_34, 14, x_32);
lean_ctor_set(x_34, 15, x_33);
lean_ctor_set_uint8(x_34, sizeof(void*)*16, x_25);
lean_ctor_set(x_15, 0, x_34);
return x_15;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_35 = lean_ctor_get(x_15, 0);
x_36 = lean_ctor_get(x_15, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_15);
x_37 = lean_ctor_get(x_2, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_2, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_2, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_2, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_2, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_2, 7);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_2, sizeof(void*)*16);
x_45 = lean_ctor_get(x_2, 8);
lean_inc(x_45);
x_46 = lean_ctor_get(x_2, 9);
lean_inc(x_46);
x_47 = lean_ctor_get(x_2, 10);
lean_inc(x_47);
x_48 = lean_ctor_get(x_2, 11);
lean_inc(x_48);
x_49 = lean_ctor_get(x_2, 12);
lean_inc(x_49);
x_50 = lean_ctor_get(x_2, 13);
lean_inc(x_50);
x_51 = lean_ctor_get(x_2, 14);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 15);
lean_inc(x_52);
lean_dec(x_2);
x_53 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_53, 0, x_35);
lean_ctor_set(x_53, 1, x_37);
lean_ctor_set(x_53, 2, x_38);
lean_ctor_set(x_53, 3, x_39);
lean_ctor_set(x_53, 4, x_40);
lean_ctor_set(x_53, 5, x_41);
lean_ctor_set(x_53, 6, x_42);
lean_ctor_set(x_53, 7, x_43);
lean_ctor_set(x_53, 8, x_45);
lean_ctor_set(x_53, 9, x_46);
lean_ctor_set(x_53, 10, x_47);
lean_ctor_set(x_53, 11, x_48);
lean_ctor_set(x_53, 12, x_49);
lean_ctor_set(x_53, 13, x_50);
lean_ctor_set(x_53, 14, x_51);
lean_ctor_set(x_53, 15, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*16, x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_36);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_15);
if (x_55 == 0)
{
return x_15;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_15, 0);
x_57 = lean_ctor_get(x_15, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_15);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_11);
if (x_59 == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_11, 0);
lean_dec(x_60);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_11, 1);
lean_inc(x_61);
lean_dec(x_11);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_2);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = !lean_is_exclusive(x_11);
if (x_63 == 0)
{
return x_11;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_11, 0);
x_65 = lean_ctor_get(x_11, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_11);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_8);
if (x_67 == 0)
{
return x_8;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_8, 0);
x_69 = lean_ctor_get(x_8, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_8);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_inc(x_7);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___lam__0), 7, 2);
lean_closure_set(x_8, 0, x_7);
lean_closure_set(x_8, 1, x_1);
x_9 = l_Lean_MVarId_withContext___at_____private_Lean_Meta_SynthInstance_0__Lean_Meta_synthPendingImp_spec__1___redArg(x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Meta_Grind_intros_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_intros_go(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_2 = x_15;
x_11 = x_17;
goto _start;
}
else
{
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_st_mk_ref(x_1, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_13);
x_15 = l_Lean_Meta_Grind_addHypothesis(x_2, x_3, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_13, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_13, x_19);
lean_dec(x_13);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_18);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_18);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_13);
x_25 = !lean_is_exclusive(x_15);
if (x_25 == 0)
{
return x_15;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
x_27 = lean_ctor_get(x_15, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_15);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*16);
if (x_12 == 0)
{
lean_object* x_13; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_introNext(x_2, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_exfalsoIfNotProp(x_16, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_21 = l_Lean_MVarId_byContra_x3f(x_20, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_st_ref_take(x_3, x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_push(x_25, x_18);
x_28 = lean_st_ref_set(x_3, x_27, x_26);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = lean_ctor_get(x_28, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_28, 0, x_31);
return x_28;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_35 = lean_ctor_get(x_21, 1);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_ctor_get(x_22, 0);
lean_inc(x_36);
lean_dec(x_22);
x_37 = lean_ctor_get(x_18, 1);
lean_inc(x_37);
x_38 = lean_ctor_get(x_18, 2);
lean_inc(x_38);
x_39 = lean_ctor_get(x_18, 3);
lean_inc(x_39);
x_40 = lean_ctor_get(x_18, 4);
lean_inc(x_40);
x_41 = lean_ctor_get(x_18, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_18, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_18, 7);
lean_inc(x_43);
x_44 = lean_ctor_get_uint8(x_18, sizeof(void*)*16);
x_45 = lean_ctor_get(x_18, 8);
lean_inc(x_45);
x_46 = lean_ctor_get(x_18, 9);
lean_inc(x_46);
x_47 = lean_ctor_get(x_18, 10);
lean_inc(x_47);
x_48 = lean_ctor_get(x_18, 11);
lean_inc(x_48);
x_49 = lean_ctor_get(x_18, 12);
lean_inc(x_49);
x_50 = lean_ctor_get(x_18, 13);
lean_inc(x_50);
x_51 = lean_ctor_get(x_18, 14);
lean_inc(x_51);
x_52 = lean_ctor_get(x_18, 15);
lean_inc(x_52);
lean_dec(x_18);
x_53 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_53, 0, x_36);
lean_ctor_set(x_53, 1, x_37);
lean_ctor_set(x_53, 2, x_38);
lean_ctor_set(x_53, 3, x_39);
lean_ctor_set(x_53, 4, x_40);
lean_ctor_set(x_53, 5, x_41);
lean_ctor_set(x_53, 6, x_42);
lean_ctor_set(x_53, 7, x_43);
lean_ctor_set(x_53, 8, x_45);
lean_ctor_set(x_53, 9, x_46);
lean_ctor_set(x_53, 10, x_47);
lean_ctor_set(x_53, 11, x_48);
lean_ctor_set(x_53, 12, x_49);
lean_ctor_set(x_53, 13, x_50);
lean_ctor_set(x_53, 14, x_51);
lean_ctor_set(x_53, 15, x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*16, x_44);
x_2 = x_53;
x_11 = x_35;
goto _start;
}
}
else
{
uint8_t x_55; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_21);
if (x_55 == 0)
{
return x_21;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_21, 0);
x_57 = lean_ctor_get(x_21, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_21);
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
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_17);
if (x_59 == 0)
{
return x_17;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_17, 0);
x_61 = lean_ctor_get(x_17, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_17);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
case 1:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_13, 1);
lean_inc(x_63);
lean_dec(x_13);
x_64 = lean_ctor_get(x_14, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_14, 1);
lean_inc(x_65);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_64);
lean_inc(x_65);
x_66 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_65, x_64, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_64);
lean_inc(x_65);
x_69 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyInjection_x3f(x_65, x_64, x_7, x_8, x_9, x_10, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_1);
lean_inc(x_65);
x_72 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_intros_go___lam__0), 11, 3);
lean_closure_set(x_72, 0, x_65);
lean_closure_set(x_72, 1, x_64);
lean_closure_set(x_72, 2, x_1);
x_73 = lean_ctor_get(x_65, 0);
lean_inc(x_73);
lean_dec(x_65);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_74 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_73, x_72, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_71);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_2 = x_75;
x_11 = x_76;
goto _start;
}
else
{
uint8_t x_78; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_78 = !lean_is_exclusive(x_74);
if (x_78 == 0)
{
return x_74;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_74, 0);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_74);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
lean_dec(x_65);
lean_dec(x_64);
x_82 = lean_ctor_get(x_69, 1);
lean_inc(x_82);
lean_dec(x_69);
x_83 = lean_ctor_get(x_70, 0);
lean_inc(x_83);
lean_dec(x_70);
x_2 = x_83;
x_11 = x_82;
goto _start;
}
}
else
{
uint8_t x_85; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_69);
if (x_85 == 0)
{
return x_69;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_69, 0);
x_87 = lean_ctor_get(x_69, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_69);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_65);
lean_dec(x_64);
x_89 = lean_ctor_get(x_66, 1);
lean_inc(x_89);
lean_dec(x_66);
x_90 = lean_ctor_get(x_67, 0);
lean_inc(x_90);
lean_dec(x_67);
x_91 = l_List_forM___at___Lean_Meta_Grind_intros_go_spec__0(x_1, x_90, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_66);
if (x_92 == 0)
{
return x_66;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_66, 0);
x_94 = lean_ctor_get(x_66, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_66);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
case 2:
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_13, 1);
lean_inc(x_96);
lean_dec(x_13);
x_97 = lean_ctor_get(x_14, 0);
lean_inc(x_97);
lean_dec(x_14);
x_2 = x_97;
x_11 = x_96;
goto _start;
}
default: 
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_ctor_get(x_13, 1);
lean_inc(x_99);
lean_dec(x_13);
x_100 = lean_ctor_get(x_14, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_14, 1);
lean_inc(x_101);
lean_dec(x_14);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_101);
x_102 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_applyCases_x3f(x_101, x_100, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_99);
if (lean_obj_tag(x_102) == 0)
{
lean_object* x_103; 
x_103 = lean_ctor_get(x_102, 0);
lean_inc(x_103);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_102, 1);
lean_inc(x_104);
lean_dec(x_102);
x_2 = x_101;
x_11 = x_104;
goto _start;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_101);
x_106 = lean_ctor_get(x_102, 1);
lean_inc(x_106);
lean_dec(x_102);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
lean_dec(x_103);
x_108 = l_List_forM___at___Lean_Meta_Grind_intros_go_spec__0(x_1, x_107, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_106);
return x_108;
}
}
else
{
uint8_t x_109; 
lean_dec(x_101);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_109 = !lean_is_exclusive(x_102);
if (x_109 == 0)
{
return x_102;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_102, 0);
x_111 = lean_ctor_get(x_102, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_102);
x_112 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
}
}
}
else
{
uint8_t x_113; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_113 = !lean_is_exclusive(x_13);
if (x_113 == 0)
{
return x_13;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_13, 0);
x_115 = lean_ctor_get(x_13, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_13);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
else
{
lean_object* x_117; lean_object* x_118; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_box(0);
x_118 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_11);
return x_118;
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___Lean_Meta_Grind_intros_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forM___at___Lean_Meta_Grind_intros_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_Grind_intros_go(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_mk_empty_array_with_capacity(x_11);
x_13 = lean_st_mk_ref(x_12, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_Meta_Grind_intros_go(x_1, x_2, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_st_ref_get(x_14, x_17);
lean_dec(x_14);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_array_to_list(x_20);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_18, 0);
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_18);
x_24 = lean_array_to_list(x_22);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
lean_dec(x_14);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_intros___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Grind_intros(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_st_mk_ref(x_1, x_12);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_15);
lean_inc(x_2);
x_17 = l_Lean_Meta_Grind_preprocess(x_2, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_18);
x_20 = l_Lean_Meta_Simp_Result_getProof(x_18, x_8, x_9, x_10, x_11, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_18, 0);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_mk_string_unchecked("Eq", 2, 2);
x_25 = lean_mk_string_unchecked("mp", 2, 2);
x_26 = l_Lean_Name_mkStr2(x_24, x_25);
x_27 = lean_box(0);
x_28 = lean_box(0);
lean_ctor_set_tag(x_13, 1);
lean_ctor_set(x_13, 1, x_28);
lean_ctor_set(x_13, 0, x_27);
x_29 = l_Lean_Expr_const___override(x_26, x_13);
lean_inc(x_23);
x_30 = l_Lean_mkApp4(x_29, x_2, x_23, x_21, x_3);
lean_inc(x_15);
x_31 = l_Lean_Meta_Grind_add(x_23, x_30, x_4, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_22);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_15, x_32);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_get(x_15, x_35);
lean_dec(x_15);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_36, 0);
lean_dec(x_38);
lean_ctor_set(x_36, 0, x_34);
return x_36;
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_15);
x_41 = !lean_is_exclusive(x_31);
if (x_41 == 0)
{
return x_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_31, 0);
x_43 = lean_ctor_get(x_31, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_31);
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
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_free_object(x_13);
lean_dec(x_15);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_49 = !lean_is_exclusive(x_17);
if (x_49 == 0)
{
return x_17;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_17, 0);
x_51 = lean_ctor_get(x_17, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_17);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_53 = lean_ctor_get(x_13, 0);
x_54 = lean_ctor_get(x_13, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_13);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_53);
lean_inc(x_2);
x_55 = l_Lean_Meta_Grind_preprocess(x_2, x_53, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_54);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_56);
x_58 = l_Lean_Meta_Simp_Result_getProof(x_56, x_8, x_9, x_10, x_11, x_57);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_56, 0);
lean_inc(x_61);
lean_dec(x_56);
x_62 = lean_mk_string_unchecked("Eq", 2, 2);
x_63 = lean_mk_string_unchecked("mp", 2, 2);
x_64 = l_Lean_Name_mkStr2(x_62, x_63);
x_65 = lean_box(0);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
x_68 = l_Lean_Expr_const___override(x_64, x_67);
lean_inc(x_61);
x_69 = l_Lean_mkApp4(x_68, x_2, x_61, x_59, x_3);
lean_inc(x_53);
x_70 = l_Lean_Meta_Grind_add(x_61, x_69, x_4, x_53, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_60);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_71 = lean_ctor_get(x_70, 1);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_st_ref_get(x_53, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
x_75 = lean_st_ref_get(x_53, x_74);
lean_dec(x_53);
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_77 = x_75;
} else {
 lean_dec_ref(x_75);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_73);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_53);
x_79 = lean_ctor_get(x_70, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_81 = x_70;
} else {
 lean_dec_ref(x_70);
 x_81 = lean_box(0);
}
if (lean_is_scalar(x_81)) {
 x_82 = lean_alloc_ctor(1, 2, 0);
} else {
 x_82 = x_81;
}
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_80);
return x_82;
}
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_56);
lean_dec(x_53);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_83 = lean_ctor_get(x_58, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_58, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_85 = x_58;
} else {
 lean_dec_ref(x_58);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
}
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_53);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_87 = lean_ctor_get(x_55, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_55, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_89 = x_55;
} else {
 lean_dec_ref(x_55);
 x_89 = lean_box(0);
}
if (lean_is_scalar(x_89)) {
 x_90 = lean_alloc_ctor(1, 2, 0);
} else {
 x_90 = x_89;
}
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_88);
return x_90;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
lean_inc(x_4);
x_13 = l___private_Lean_Meta_Tactic_Grind_Intro_0__Lean_Meta_Grind_isEagerCasesCandidate(x_4, x_2);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_4);
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertAt___lam__0), 12, 4);
lean_closure_set(x_14, 0, x_4);
lean_closure_set(x_14, 1, x_2);
lean_closure_set(x_14, 2, x_1);
lean_closure_set(x_14, 3, x_3);
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l_Lean_MVarId_withContext___at___Lean_Meta_Grind_toGrindTactic_spec__0___redArg(x_15, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get_uint8(x_17, sizeof(void*)*16);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
lean_dec(x_20);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
lean_ctor_set(x_16, 0, x_22);
return x_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_16, 1);
lean_inc(x_23);
lean_dec(x_16);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_17);
x_27 = !lean_is_exclusive(x_16);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_16, 0);
lean_dec(x_28);
x_29 = lean_box(0);
lean_ctor_set(x_16, 0, x_29);
return x_16;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_16, 1);
lean_inc(x_30);
lean_dec(x_16);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_16);
if (x_33 == 0)
{
return x_16;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_16, 0);
x_35 = lean_ctor_get(x_16, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_16);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_mk_string_unchecked("h", 1, 1);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_38, x_10, x_11, x_12);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_4, 0);
lean_inc(x_42);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_43 = l_Lean_MVarId_assert(x_42, x_40, x_2, x_1, x_8, x_9, x_10, x_11, x_41);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
x_47 = lean_ctor_get(x_4, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_4, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_4, 4);
lean_inc(x_49);
x_50 = lean_ctor_get(x_4, 5);
lean_inc(x_50);
x_51 = lean_ctor_get(x_4, 6);
lean_inc(x_51);
x_52 = lean_ctor_get(x_4, 7);
lean_inc(x_52);
x_53 = lean_ctor_get_uint8(x_4, sizeof(void*)*16);
x_54 = lean_ctor_get(x_4, 8);
lean_inc(x_54);
x_55 = lean_ctor_get(x_4, 9);
lean_inc(x_55);
x_56 = lean_ctor_get(x_4, 10);
lean_inc(x_56);
x_57 = lean_ctor_get(x_4, 11);
lean_inc(x_57);
x_58 = lean_ctor_get(x_4, 12);
lean_inc(x_58);
x_59 = lean_ctor_get(x_4, 13);
lean_inc(x_59);
x_60 = lean_ctor_get(x_4, 14);
lean_inc(x_60);
x_61 = lean_ctor_get(x_4, 15);
lean_inc(x_61);
lean_dec(x_4);
x_62 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_62, 0, x_44);
lean_ctor_set(x_62, 1, x_46);
lean_ctor_set(x_62, 2, x_47);
lean_ctor_set(x_62, 3, x_48);
lean_ctor_set(x_62, 4, x_49);
lean_ctor_set(x_62, 5, x_50);
lean_ctor_set(x_62, 6, x_51);
lean_ctor_set(x_62, 7, x_52);
lean_ctor_set(x_62, 8, x_54);
lean_ctor_set(x_62, 9, x_55);
lean_ctor_set(x_62, 10, x_56);
lean_ctor_set(x_62, 11, x_57);
lean_ctor_set(x_62, 12, x_58);
lean_ctor_set(x_62, 13, x_59);
lean_ctor_set(x_62, 14, x_60);
lean_ctor_set(x_62, 15, x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*16, x_53);
x_63 = l_Lean_Meta_Grind_intros(x_3, x_62, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_45);
return x_63;
}
else
{
uint8_t x_64; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_64 = !lean_is_exclusive(x_43);
if (x_64 == 0)
{
return x_43;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_43, 0);
x_66 = lean_ctor_get(x_43, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_43);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Meta_Grind_assertAt(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 9);
lean_inc(x_10);
x_11 = l_Std_Queue_dequeue_x3f___redArg(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_15 = lean_ctor_get(x_11, 0);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_16, 2);
lean_inc(x_20);
lean_dec(x_16);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_1, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 3);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 4);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 5);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 6);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 7);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_30 = lean_ctor_get(x_1, 8);
lean_inc(x_30);
x_31 = lean_ctor_get(x_1, 10);
lean_inc(x_31);
x_32 = lean_ctor_get(x_1, 11);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 12);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 13);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 14);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 15);
lean_inc(x_36);
lean_dec(x_1);
x_37 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_37, 0, x_21);
lean_ctor_set(x_37, 1, x_22);
lean_ctor_set(x_37, 2, x_23);
lean_ctor_set(x_37, 3, x_24);
lean_ctor_set(x_37, 4, x_25);
lean_ctor_set(x_37, 5, x_26);
lean_ctor_set(x_37, 6, x_27);
lean_ctor_set(x_37, 7, x_28);
lean_ctor_set(x_37, 8, x_30);
lean_ctor_set(x_37, 9, x_17);
lean_ctor_set(x_37, 10, x_31);
lean_ctor_set(x_37, 11, x_32);
lean_ctor_set(x_37, 12, x_33);
lean_ctor_set(x_37, 13, x_34);
lean_ctor_set(x_37, 14, x_35);
lean_ctor_set(x_37, 15, x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*16, x_29);
x_38 = l_Lean_Meta_Grind_assertAt(x_18, x_19, x_20, x_37, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_11, 0, x_40);
lean_ctor_set(x_38, 0, x_11);
return x_38;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_38, 0);
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_38);
lean_ctor_set(x_11, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_11);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_11);
x_44 = !lean_is_exclusive(x_38);
if (x_44 == 0)
{
return x_38;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_38, 0);
x_46 = lean_ctor_get(x_38, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_38);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_48 = lean_ctor_get(x_11, 0);
lean_inc(x_48);
lean_dec(x_11);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_49, 2);
lean_inc(x_53);
lean_dec(x_49);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_1, 2);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 3);
lean_inc(x_57);
x_58 = lean_ctor_get(x_1, 4);
lean_inc(x_58);
x_59 = lean_ctor_get(x_1, 5);
lean_inc(x_59);
x_60 = lean_ctor_get(x_1, 6);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 7);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_1, sizeof(void*)*16);
x_63 = lean_ctor_get(x_1, 8);
lean_inc(x_63);
x_64 = lean_ctor_get(x_1, 10);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 11);
lean_inc(x_65);
x_66 = lean_ctor_get(x_1, 12);
lean_inc(x_66);
x_67 = lean_ctor_get(x_1, 13);
lean_inc(x_67);
x_68 = lean_ctor_get(x_1, 14);
lean_inc(x_68);
x_69 = lean_ctor_get(x_1, 15);
lean_inc(x_69);
lean_dec(x_1);
x_70 = lean_alloc_ctor(0, 16, 1);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_55);
lean_ctor_set(x_70, 2, x_56);
lean_ctor_set(x_70, 3, x_57);
lean_ctor_set(x_70, 4, x_58);
lean_ctor_set(x_70, 5, x_59);
lean_ctor_set(x_70, 6, x_60);
lean_ctor_set(x_70, 7, x_61);
lean_ctor_set(x_70, 8, x_63);
lean_ctor_set(x_70, 9, x_50);
lean_ctor_set(x_70, 10, x_64);
lean_ctor_set(x_70, 11, x_65);
lean_ctor_set(x_70, 12, x_66);
lean_ctor_set(x_70, 13, x_67);
lean_ctor_set(x_70, 14, x_68);
lean_ctor_set(x_70, 15, x_69);
lean_ctor_set_uint8(x_70, sizeof(void*)*16, x_62);
x_71 = l_Lean_Meta_Grind_assertAt(x_51, x_52, x_53, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_71, 1);
lean_inc(x_73);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_74 = x_71;
} else {
 lean_dec_ref(x_71);
 x_74 = lean_box(0);
}
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_72);
if (lean_is_scalar(x_74)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_74;
}
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_73);
return x_76;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_77 = lean_ctor_get(x_71, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_71, 1);
lean_inc(x_78);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_79 = x_71;
} else {
 lean_dec_ref(x_71);
 x_79 = lean_box(0);
}
if (lean_is_scalar(x_79)) {
 x_80 = lean_alloc_ctor(1, 2, 0);
} else {
 x_80 = x_79;
}
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertNext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_Grind_assertNext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_assertAll(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_assertNext___boxed), 9, 0);
x_11 = l_Lean_Meta_Grind_GrindTactic_iterate(x_10, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
lean_object* initialize_Init_Grind_Lemmas(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Assert(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Cases(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_CasesMatch(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Injection(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Core(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Combinators(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Intro(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Lemmas(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Assert(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Cases(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_CasesMatch(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Injection(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Core(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Combinators(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Grind_instInhabitedIntroResult = _init_l_Lean_Meta_Grind_instInhabitedIntroResult();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedIntroResult);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
