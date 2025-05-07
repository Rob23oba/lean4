// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.EMatchTheorem
// Imports: Init.Grind.Util Init.Grind.Tactics Lean.HeadIndex Lean.PrettyPrinter Lean.Util.FoldConsts Lean.Util.CollectFVars Lean.Meta.Basic Lean.Meta.InferType Lean.Meta.Eqns Lean.Meta.Tactic.Grind.Util
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
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__11(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_paren(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_explainFailure___boxed(lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
lean_object* l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_ppPattern_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_contains___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorem_getProofWithFreshMVarLevels___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__11___boxed(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchTheorem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_levelParams(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPatternDontCare(lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr___lam__0(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_mkAppB(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isOffset_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedOrigin;
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2026_(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
uint8_t l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1379_(uint8_t, lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig;
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570_(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableEMatchTheoremKind;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isAxiom(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_817_(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_ppPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppPattern_ppArg(lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOf(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getProofFor(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprOrigin;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff___boxed(lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instInhabitedEMatchTheorem;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Exception_toMessageData(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(uint8_t);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchAttr(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_EMatchTheorems_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPatternDontCare___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion(lean_object*, uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isBVar(lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorem_getProofWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEqBwdPattern_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_insert(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_explainFailure(uint8_t);
lean_object* l_Lean_mkConstWithLevelParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessPattern(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_transform___at___Lean_Elab_Term_exposeLevelMVars_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getRevArg_x21(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_find(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isAtomicPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems___redArg___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_goArg(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_groundPattern_x3f(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_ConstantInfo_isCtor(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheorem(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitWhileForbidden(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isForbidden(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___redArg(uint8_t, uint8_t);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_instDecidableRelSubsetOfDecidableEq___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin;
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Expr_toHeadIndex(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isOffsetPattern_x3f(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1014_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_reprPatternArgKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_3551____boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*, lean_object*);
lean_object* lean_grind_normalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAnnotation(lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isArrow(lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEqBwdPattern___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__0(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars_go___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_forbiddenDeclNames;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toCtorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheorem(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_instReprPatternArgKind;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_main(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__2(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_reprPatternArgKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_3551_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570_(lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hashEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1719_(uint8_t);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqBwdPattern(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_isErased___boxed(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isForbidden___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1014____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_goArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGroundPattern(lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constLevels_x21(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__1(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isAtomicPattern(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Name_getString_x21_spec__0(lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isEqBwdPattern(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_normalizePattern(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_NormalizePattern_main_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__12(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_EMatchTheorems_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkRawNatLit(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1379____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppPattern(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instReprEMatchTheoremKind;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_find___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_annotation_x3f(lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isTypeFormer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_toCtorIdx(uint8_t);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars(lean_object*);
lean_object* l_Lean_RBMap_size___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_binderInfo(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___lam__0(lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getFunInfoNArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars_go(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
uint8_t l_Lean_Syntax_structEq(lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqEMatchTheoremKind;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t l_Lean_isInductiveCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_unfoldReducible(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isGroundPattern(lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instDecidableEqNat___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin__1;
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_erase(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__0(lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkOffsetPattern(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key(lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isGroundPattern___boxed(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_foldProjs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hashEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1719____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchEqTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_817____boxed(lean_object*, lean_object*);
uint64_t l_Lean_HeadIndex_hash(lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
lean_object* l_Lean_Meta_mkConstWithFreshMVarLevels(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(uint8_t, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_groundPattern_x3f___boxed(lean_object*);
uint8_t l_Lean_wasOriginallyTheorem(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__2___redArg(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqOrigin__1___lam__0(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute(uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toCtorIdx(uint8_t);
lean_object* l_Lean_Meta_isProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__1(lean_object*, uint8_t, lean_object*, size_t, size_t);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkOffsetPattern(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_mk_string_unchecked("Lean", 4, 4);
x_4 = lean_mk_string_unchecked("Grind", 5, 5);
x_5 = lean_mk_string_unchecked("offset", 6, 6);
x_6 = l_Lean_Name_mkStr3(x_3, x_4, x_5);
x_7 = lean_box(0);
x_8 = l_Lean_Expr_const___override(x_6, x_7);
x_9 = l_Lean_mkRawNatLit(x_2);
x_10 = l_Lean_mkAppB(x_8, x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_expr_eqv(x_2, x_1);
if (x_8 == 0)
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 2);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__0(x_2, x_9, x_10, x_11, x_12, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_13;
}
case 7:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 2);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_18 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__0(x_2, x_14, x_15, x_16, x_17, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
return x_18;
}
case 8:
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
default: 
{
lean_object* x_21; 
lean_inc(x_2);
x_21 = l_Lean_Meta_isOffset_x3f(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_21);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
lean_dec(x_24);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_2);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_28, 0, x_2);
x_29 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
else
{
uint8_t x_31; 
lean_dec(x_2);
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_21);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_33 = lean_ctor_get(x_22, 0);
x_34 = lean_ctor_get(x_21, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_nat_dec_eq(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = l_Lean_Meta_Grind_mkOffsetPattern(x_35, x_36);
lean_ctor_set(x_22, 0, x_39);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_21, 0, x_40);
return x_21;
}
else
{
lean_object* x_41; 
lean_dec(x_36);
lean_ctor_set(x_22, 0, x_35);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_22);
lean_ctor_set(x_21, 0, x_41);
return x_21;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_42 = lean_ctor_get(x_22, 0);
x_43 = lean_ctor_get(x_21, 1);
lean_inc(x_43);
lean_dec(x_21);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_nat_dec_eq(x_45, x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Lean_Meta_Grind_mkOffsetPattern(x_44, x_45);
lean_ctor_set(x_22, 0, x_48);
x_49 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_49, 0, x_22);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_45);
lean_ctor_set(x_22, 0, x_44);
x_51 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_51, 0, x_22);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
x_53 = lean_ctor_get(x_22, 0);
lean_inc(x_53);
lean_dec(x_22);
x_54 = lean_ctor_get(x_21, 1);
lean_inc(x_54);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_55 = x_21;
} else {
 lean_dec_ref(x_21);
 x_55 = lean_box(0);
}
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_nat_dec_eq(x_57, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = l_Lean_Meta_Grind_mkOffsetPattern(x_56, x_57);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_62, 0, x_61);
if (lean_is_scalar(x_55)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_55;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_54);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_57);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_56);
x_65 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_65, 0, x_64);
if (lean_is_scalar(x_55)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_55;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_54);
return x_66;
}
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_2);
x_67 = !lean_is_exclusive(x_21);
if (x_67 == 0)
{
return x_21;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_21, 0);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_21);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_71 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_71, 0, x_2);
x_72 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_7);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__1___boxed), 7, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__2___boxed), 6, 0);
x_9 = l_Lean_Core_transform___at___Lean_Elab_Term_exposeLevelMVars_spec__0(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__0(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isOffsetPattern_x3f(lean_object* x_1) {
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
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
lean_inc(x_5);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = lean_mk_string_unchecked("Lean", 4, 4);
x_10 = lean_mk_string_unchecked("Grind", 5, 5);
x_11 = lean_mk_string_unchecked("offset", 6, 6);
x_12 = l_Lean_Name_mkStr3(x_9, x_10, x_11);
x_13 = l_Lean_Expr_isConstOf(x_8, x_12);
lean_dec(x_12);
lean_dec(x_8);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_5);
lean_dec(x_2);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_dec(x_2);
if (lean_obj_tag(x_15) == 9)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_5, 1);
lean_inc(x_17);
lean_dec(x_5);
x_18 = !lean_is_exclusive(x_16);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 0);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_tag(x_16, 1);
lean_ctor_set(x_16, 0, x_20);
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
else
{
lean_object* x_24; 
lean_dec(x_16);
lean_dec(x_5);
x_24 = lean_box(0);
return x_24;
}
}
else
{
lean_object* x_25; 
lean_dec(x_15);
lean_dec(x_5);
x_25 = lean_box(0);
return x_25;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEqBwdPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_5 = lean_mk_string_unchecked("Lean", 4, 4);
x_6 = lean_mk_string_unchecked("Grind", 5, 5);
x_7 = lean_mk_string_unchecked("eqBwdPattern", 12, 12);
x_8 = l_Lean_Name_mkStr3(x_5, x_6, x_7);
x_9 = l_Lean_Expr_const___override(x_8, x_1);
x_10 = l_Lean_mkApp3(x_9, x_2, x_3, x_4);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isEqBwdPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Grind", 5, 5);
x_4 = lean_mk_string_unchecked("eqBwdPattern", 12, 12);
x_5 = l_Lean_Name_mkStr3(x_2, x_3, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = l_Lean_Expr_isAppOfArity(x_1, x_5, x_6);
lean_dec(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEqBwdPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isEqBwdPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEqBwdPattern_x3f(lean_object* x_1) {
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
lean_object* x_5; uint8_t x_6; 
lean_inc(x_2);
x_5 = l_Lean_Expr_appFnCleanup___redArg(x_2);
x_6 = l_Lean_Expr_isApp(x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
x_7 = lean_box(0);
return x_7;
}
else
{
lean_object* x_8; uint8_t x_9; 
lean_inc(x_5);
x_8 = l_Lean_Expr_appFnCleanup___redArg(x_5);
x_9 = l_Lean_Expr_isApp(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
x_10 = lean_box(0);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Expr_appFnCleanup___redArg(x_8);
x_12 = lean_mk_string_unchecked("Lean", 4, 4);
x_13 = lean_mk_string_unchecked("Grind", 5, 5);
x_14 = lean_mk_string_unchecked("eqBwdPattern", 12, 12);
x_15 = l_Lean_Name_mkStr3(x_12, x_13, x_14);
x_16 = l_Lean_Expr_isConstOf(x_11, x_15);
lean_dec(x_15);
lean_dec(x_11);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_5);
lean_dec(x_2);
x_17 = lean_box(0);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_2, 1);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_ctor_get(x_5, 1);
lean_inc(x_19);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
}
}
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; 
x_1 = lean_box(0);
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(5u);
x_4 = lean_unsigned_to_nat(1000u);
x_5 = lean_box(1);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_unsigned_to_nat(10000u);
x_8 = lean_alloc_ctor(0, 7, 18);
lean_ctor_set(x_8, 0, x_2);
lean_ctor_set(x_8, 1, x_3);
lean_ctor_set(x_8, 2, x_3);
lean_ctor_set(x_8, 3, x_4);
lean_ctor_set(x_8, 4, x_6);
lean_ctor_set(x_8, 5, x_4);
lean_ctor_set(x_8, 6, x_7);
x_9 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7, x_9);
x_10 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 1, x_10);
x_11 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 2, x_11);
x_12 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 3, x_12);
x_13 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 4, x_13);
x_14 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 5, x_14);
x_15 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 6, x_15);
x_16 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 7, x_16);
x_17 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 8, x_17);
x_18 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 9, x_18);
x_19 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 10, x_19);
x_20 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 11, x_20);
x_21 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 12, x_21);
x_22 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 13, x_22);
x_23 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 14, x_23);
x_24 = lean_unbox(x_5);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 15, x_24);
x_25 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 16, x_25);
x_26 = lean_unbox(x_1);
lean_ctor_set_uint8(x_8, sizeof(void*)*7 + 17, x_26);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessPattern(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_1, x_4, x_7);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_22 = l_Lean_Meta_Grind_unfoldReducible(x_20, x_3, x_4, x_5, x_6, x_21);
if (lean_obj_tag(x_22) == 0)
{
if (x_2 == 0)
{
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_8 = x_23;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_24;
goto block_18;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig;
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = lean_grind_normalize(x_25, x_27, x_3, x_4, x_5, x_6, x_26);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_8 = x_29;
x_9 = x_3;
x_10 = x_4;
x_11 = x_5;
x_12 = x_6;
x_13 = x_30;
goto block_18;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_28;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_22;
}
block_18:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_14 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_detectOffsets(x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = l_Lean_Meta_Grind_foldProjs(x_15, x_9, x_10, x_11, x_12, x_16);
return x_17;
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_preprocessPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_Grind_preprocessPattern(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedOrigin() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_817_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_19; uint8_t x_20; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_4 = x_1;
} else {
 lean_dec_ref(x_1);
 x_4 = lean_box(0);
}
x_19 = lean_unsigned_to_nat(1024u);
x_20 = lean_nat_dec_le(x_19, x_2);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_to_int(x_21);
x_5 = x_22;
goto block_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_to_int(x_23);
x_5 = x_24;
goto block_18;
}
block_18:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_6 = lean_mk_string_unchecked("Lean.Meta.Grind.Origin.decl", 27, 27);
if (lean_is_scalar(x_4)) {
 x_7 = lean_alloc_ctor(3, 1, 0);
} else {
 x_7 = x_4;
 lean_ctor_set_tag(x_7, 3);
}
lean_ctor_set(x_7, 0, x_6);
x_8 = lean_box(1);
x_9 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
x_10 = lean_unsigned_to_nat(1024u);
x_11 = l_Lean_Name_reprPrec(x_3, x_10);
x_12 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_12, 0, x_9);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_15, 0, x_13);
x_16 = lean_unbox(x_14);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_16);
x_17 = l_Repr_addAppParen(x_15, x_2);
return x_17;
}
}
case 1:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_41; uint8_t x_42; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_26 = x_1;
} else {
 lean_dec_ref(x_1);
 x_26 = lean_box(0);
}
x_41 = lean_unsigned_to_nat(1024u);
x_42 = lean_nat_dec_le(x_41, x_2);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_to_int(x_43);
x_27 = x_44;
goto block_40;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_to_int(x_45);
x_27 = x_46;
goto block_40;
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_28 = lean_mk_string_unchecked("Lean.Meta.Grind.Origin.fvar", 27, 27);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(3, 1, 0);
} else {
 x_29 = x_26;
 lean_ctor_set_tag(x_29, 3);
}
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(1024u);
x_33 = l_Lean_Name_reprPrec(x_25, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_35, 0, x_27);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_37, 0, x_35);
x_38 = lean_unbox(x_36);
lean_ctor_set_uint8(x_37, sizeof(void*)*1, x_38);
x_39 = l_Repr_addAppParen(x_37, x_2);
return x_39;
}
}
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_67; uint8_t x_68; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_1, 1);
lean_inc(x_48);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_49 = x_1;
} else {
 lean_dec_ref(x_1);
 x_49 = lean_box(0);
}
x_67 = lean_unsigned_to_nat(1024u);
x_68 = lean_nat_dec_le(x_67, x_2);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_to_int(x_69);
x_50 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_nat_to_int(x_71);
x_50 = x_72;
goto block_66;
}
block_66:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; lean_object* x_65; 
x_51 = lean_mk_string_unchecked("Lean.Meta.Grind.Origin.stx", 26, 26);
x_52 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = lean_box(1);
if (lean_is_scalar(x_49)) {
 x_54 = lean_alloc_ctor(5, 2, 0);
} else {
 x_54 = x_49;
 lean_ctor_set_tag(x_54, 5);
}
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_unsigned_to_nat(1024u);
x_56 = l_Lean_Name_reprPrec(x_47, x_55);
x_57 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_53);
x_59 = l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2026_(x_48, x_55);
x_60 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_61, 0, x_50);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_63, 0, x_61);
x_64 = lean_unbox(x_62);
lean_ctor_set_uint8(x_63, sizeof(void*)*1, x_64);
x_65 = l_Repr_addAppParen(x_63, x_2);
return x_65;
}
}
default: 
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_89; uint8_t x_90; 
x_73 = lean_ctor_get(x_1, 0);
lean_inc(x_73);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_74 = x_1;
} else {
 lean_dec_ref(x_1);
 x_74 = lean_box(0);
}
x_89 = lean_unsigned_to_nat(1024u);
x_90 = lean_nat_dec_le(x_89, x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_to_int(x_91);
x_75 = x_92;
goto block_88;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_to_int(x_93);
x_75 = x_94;
goto block_88;
}
block_88:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_76 = lean_mk_string_unchecked("Lean.Meta.Grind.Origin.local", 28, 28);
if (lean_is_scalar(x_74)) {
 x_77 = lean_alloc_ctor(3, 1, 0);
} else {
 x_77 = x_74;
}
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_box(1);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_unsigned_to_nat(1024u);
x_81 = l_Lean_Name_reprPrec(x_73, x_80);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_85, 0, x_83);
x_86 = lean_unbox(x_84);
lean_ctor_set_uint8(x_85, sizeof(void*)*1, x_86);
x_87 = l_Repr_addAppParen(x_85, x_2);
return x_87;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_817____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_817_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_817____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1014_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_name_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
return x_10;
}
else
{
lean_object* x_11; uint8_t x_12; 
lean_dec(x_2);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
return x_12;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
x_17 = lean_name_eq(x_13, x_15);
lean_dec(x_15);
lean_dec(x_13);
if (x_17 == 0)
{
lean_dec(x_16);
lean_dec(x_14);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = l_Lean_Syntax_structEq(x_14, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_2);
lean_dec(x_1);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_name_eq(x_21, x_22);
lean_dec(x_22);
lean_dec(x_21);
return x_23;
}
else
{
lean_object* x_24; uint8_t x_25; 
lean_dec(x_2);
lean_dec(x_1);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1014____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1014_(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqOrigin____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1014____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_key___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_Origin_key(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_MessageData_ofConst(x_2);
x_4 = lean_apply_2(x_1, lean_box(0), x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
switch (lean_obj_tag(x_4)) {
case 0:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_Origin_pp___redArg___lam__0), 2, 1);
lean_closure_set(x_9, 0, x_7);
x_10 = l_Lean_mkConstWithLevelParams___redArg(x_1, x_2, x_3, x_8);
x_11 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_10, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_3);
lean_dec(x_2);
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
lean_dec(x_4);
x_15 = l_Lean_Expr_fvar___override(x_14);
x_16 = l_Lean_MessageData_ofExpr(x_15);
x_17 = lean_apply_2(x_13, lean_box(0), x_16);
return x_17;
}
case 2:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_2);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_4, 1);
lean_inc(x_20);
lean_dec(x_4);
x_21 = l_Lean_MessageData_ofSyntax(x_20);
x_22 = lean_apply_2(x_19, lean_box(0), x_21);
return x_22;
}
default: 
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
lean_dec(x_1);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = l_Lean_MessageData_ofName(x_25);
x_27 = lean_apply_2(x_24, lean_box(0), x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Grind_Origin_pp___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_instBEqOrigin__1___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 0);
x_3 = x_7;
goto block_6;
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqOrigin__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqOrigin__1___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instBEqOrigin__1___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_instBEqOrigin__1___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_Grind_instHashableOrigin___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = l_Lean_Name_hash___override(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instHashableOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_instHashableOrigin___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
case 3:
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
case 4:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(4u);
return x_6;
}
case 5:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(5u);
return x_7;
}
case 6:
{
lean_object* x_8; 
x_8 = lean_unsigned_to_nat(6u);
return x_8;
}
case 7:
{
lean_object* x_9; 
x_9 = lean_unsigned_to_nat(7u);
return x_9;
}
case 8:
{
lean_object* x_10; 
x_10 = lean_unsigned_to_nat(8u);
return x_10;
}
default: 
{
lean_object* x_11; 
x_11 = lean_unsigned_to_nat(9u);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Grind_EMatchTheoremKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
static uint8_t _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind() {
_start:
{
lean_object* x_1; uint8_t x_2; 
x_1 = lean_box(0);
x_2 = lean_unbox(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Grind_EMatchTheoremKind_toCtorIdx(x_1);
x_4 = l_Lean_Meta_Grind_EMatchTheoremKind_toCtorIdx(x_2);
x_5 = lean_nat_dec_eq(x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_4);
x_6 = lean_box(x_5);
return x_6;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instBEqEMatchTheoremKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1379_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; lean_object* x_30; lean_object* x_39; lean_object* x_48; lean_object* x_57; lean_object* x_66; lean_object* x_75; lean_object* x_84; 
switch (x_1) {
case 0:
{
lean_object* x_93; uint8_t x_94; 
x_93 = lean_unsigned_to_nat(1024u);
x_94 = lean_nat_dec_le(x_93, x_2);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_unsigned_to_nat(2u);
x_96 = lean_nat_to_int(x_95);
x_3 = x_96;
goto block_11;
}
else
{
lean_object* x_97; lean_object* x_98; 
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_nat_to_int(x_97);
x_3 = x_98;
goto block_11;
}
}
case 1:
{
lean_object* x_99; uint8_t x_100; 
x_99 = lean_unsigned_to_nat(1024u);
x_100 = lean_nat_dec_le(x_99, x_2);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; 
x_101 = lean_unsigned_to_nat(2u);
x_102 = lean_nat_to_int(x_101);
x_12 = x_102;
goto block_20;
}
else
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_unsigned_to_nat(1u);
x_104 = lean_nat_to_int(x_103);
x_12 = x_104;
goto block_20;
}
}
case 2:
{
lean_object* x_105; uint8_t x_106; 
x_105 = lean_unsigned_to_nat(1024u);
x_106 = lean_nat_dec_le(x_105, x_2);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; 
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_nat_to_int(x_107);
x_21 = x_108;
goto block_29;
}
else
{
lean_object* x_109; lean_object* x_110; 
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_nat_to_int(x_109);
x_21 = x_110;
goto block_29;
}
}
case 3:
{
lean_object* x_111; uint8_t x_112; 
x_111 = lean_unsigned_to_nat(1024u);
x_112 = lean_nat_dec_le(x_111, x_2);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_unsigned_to_nat(2u);
x_114 = lean_nat_to_int(x_113);
x_30 = x_114;
goto block_38;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_to_int(x_115);
x_30 = x_116;
goto block_38;
}
}
case 4:
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_unsigned_to_nat(1024u);
x_118 = lean_nat_dec_le(x_117, x_2);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_unsigned_to_nat(2u);
x_120 = lean_nat_to_int(x_119);
x_39 = x_120;
goto block_47;
}
else
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_nat_to_int(x_121);
x_39 = x_122;
goto block_47;
}
}
case 5:
{
lean_object* x_123; uint8_t x_124; 
x_123 = lean_unsigned_to_nat(1024u);
x_124 = lean_nat_dec_le(x_123, x_2);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_unsigned_to_nat(2u);
x_126 = lean_nat_to_int(x_125);
x_48 = x_126;
goto block_56;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_unsigned_to_nat(1u);
x_128 = lean_nat_to_int(x_127);
x_48 = x_128;
goto block_56;
}
}
case 6:
{
lean_object* x_129; uint8_t x_130; 
x_129 = lean_unsigned_to_nat(1024u);
x_130 = lean_nat_dec_le(x_129, x_2);
if (x_130 == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_unsigned_to_nat(2u);
x_132 = lean_nat_to_int(x_131);
x_57 = x_132;
goto block_65;
}
else
{
lean_object* x_133; lean_object* x_134; 
x_133 = lean_unsigned_to_nat(1u);
x_134 = lean_nat_to_int(x_133);
x_57 = x_134;
goto block_65;
}
}
case 7:
{
lean_object* x_135; uint8_t x_136; 
x_135 = lean_unsigned_to_nat(1024u);
x_136 = lean_nat_dec_le(x_135, x_2);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; 
x_137 = lean_unsigned_to_nat(2u);
x_138 = lean_nat_to_int(x_137);
x_66 = x_138;
goto block_74;
}
else
{
lean_object* x_139; lean_object* x_140; 
x_139 = lean_unsigned_to_nat(1u);
x_140 = lean_nat_to_int(x_139);
x_66 = x_140;
goto block_74;
}
}
case 8:
{
lean_object* x_141; uint8_t x_142; 
x_141 = lean_unsigned_to_nat(1024u);
x_142 = lean_nat_dec_le(x_141, x_2);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_unsigned_to_nat(2u);
x_144 = lean_nat_to_int(x_143);
x_75 = x_144;
goto block_83;
}
else
{
lean_object* x_145; lean_object* x_146; 
x_145 = lean_unsigned_to_nat(1u);
x_146 = lean_nat_to_int(x_145);
x_75 = x_146;
goto block_83;
}
}
default: 
{
lean_object* x_147; uint8_t x_148; 
x_147 = lean_unsigned_to_nat(1024u);
x_148 = lean_nat_dec_le(x_147, x_2);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_unsigned_to_nat(2u);
x_150 = lean_nat_to_int(x_149);
x_84 = x_150;
goto block_92;
}
else
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_unsigned_to_nat(1u);
x_152 = lean_nat_to_int(x_151);
x_84 = x_152;
goto block_92;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.eqLhs", 39, 39);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.eqRhs", 39, 39);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.eqBoth", 40, 40);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.eqBwd", 39, 39);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = l_Repr_addAppParen(x_35, x_2);
return x_37;
}
block_47:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_40 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.fwd", 37, 37);
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_box(0);
x_44 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_44, 0, x_42);
x_45 = lean_unbox(x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*1, x_45);
x_46 = l_Repr_addAppParen(x_44, x_2);
return x_46;
}
block_56:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_49 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.bwd", 37, 37);
x_50 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_50);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_53, 0, x_51);
x_54 = lean_unbox(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*1, x_54);
x_55 = l_Repr_addAppParen(x_53, x_2);
return x_55;
}
block_65:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; lean_object* x_64; 
x_58 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.leftRight", 43, 43);
x_59 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_59, 0, x_58);
x_60 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_62, 0, x_60);
x_63 = lean_unbox(x_61);
lean_ctor_set_uint8(x_62, sizeof(void*)*1, x_63);
x_64 = l_Repr_addAppParen(x_62, x_2);
return x_64;
}
block_74:
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; 
x_67 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.rightLeft", 43, 43);
x_68 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_68, 0, x_67);
x_69 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_69, 0, x_66);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_box(0);
x_71 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_71, 0, x_69);
x_72 = lean_unbox(x_70);
lean_ctor_set_uint8(x_71, sizeof(void*)*1, x_72);
x_73 = l_Repr_addAppParen(x_71, x_2);
return x_73;
}
block_83:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; lean_object* x_82; 
x_76 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.default", 41, 41);
x_77 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_77, 0, x_76);
x_78 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_80, 0, x_78);
x_81 = lean_unbox(x_79);
lean_ctor_set_uint8(x_80, sizeof(void*)*1, x_81);
x_82 = l_Repr_addAppParen(x_80, x_2);
return x_82;
}
block_92:
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; lean_object* x_91; 
x_85 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheoremKind.user", 38, 38);
x_86 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_86, 0, x_85);
x_87 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_89, 0, x_87);
x_90 = lean_unbox(x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*1, x_90);
x_91 = l_Repr_addAppParen(x_89, x_2);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1379____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1379_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_reprEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1379____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint64_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hashEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1719_(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; uint64_t x_3; 
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_uint64_of_nat(x_2);
return x_3;
}
case 1:
{
lean_object* x_4; uint64_t x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_uint64_of_nat(x_4);
return x_5;
}
case 2:
{
lean_object* x_6; uint64_t x_7; 
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_uint64_of_nat(x_6);
return x_7;
}
case 3:
{
lean_object* x_8; uint64_t x_9; 
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_uint64_of_nat(x_8);
return x_9;
}
case 4:
{
lean_object* x_10; uint64_t x_11; 
x_10 = lean_unsigned_to_nat(4u);
x_11 = lean_uint64_of_nat(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; uint64_t x_13; 
x_12 = lean_unsigned_to_nat(5u);
x_13 = lean_uint64_of_nat(x_12);
return x_13;
}
case 6:
{
lean_object* x_14; uint64_t x_15; 
x_14 = lean_unsigned_to_nat(6u);
x_15 = lean_uint64_of_nat(x_14);
return x_15;
}
case 7:
{
lean_object* x_16; uint64_t x_17; 
x_16 = lean_unsigned_to_nat(7u);
x_17 = lean_uint64_of_nat(x_16);
return x_17;
}
case 8:
{
lean_object* x_18; uint64_t x_19; 
x_18 = lean_unsigned_to_nat(8u);
x_19 = lean_uint64_of_nat(x_18);
return x_19;
}
default: 
{
lean_object* x_20; uint64_t x_21; 
x_20 = lean_unsigned_to_nat(9u);
x_21 = lean_uint64_of_nat(x_20);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hashEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1719____boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint64_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hashEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1719_(x_2);
x_4 = lean_box_uint64(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hashEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1719____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("[grind =]", 9, 9);
return x_3;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_mk_string_unchecked("[grind =_]", 10, 10);
return x_4;
}
case 2:
{
lean_object* x_5; 
x_5 = lean_mk_string_unchecked("[grind _=_]", 11, 11);
return x_5;
}
case 3:
{
lean_object* x_6; 
x_6 = lean_mk_string_unchecked("[grind ←=]", 12, 10);
return x_6;
}
case 4:
{
lean_object* x_7; 
x_7 = lean_mk_string_unchecked("[grind →]", 11, 9);
return x_7;
}
case 5:
{
lean_object* x_8; 
x_8 = lean_mk_string_unchecked("[grind ←]", 11, 9);
return x_8;
}
case 6:
{
lean_object* x_9; 
x_9 = lean_mk_string_unchecked("[grind =>]", 10, 10);
return x_9;
}
case 7:
{
lean_object* x_10; 
x_10 = lean_mk_string_unchecked("[grind <=]", 10, 10);
return x_10;
}
default: 
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_mk_string_unchecked("[grind]", 7, 7);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_explainFailure(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_mk_string_unchecked("failed to find pattern in the left-hand side of the theorem's conclusion", 72, 72);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_mk_string_unchecked("failed to find pattern in the right-hand side of the theorem's conclusion", 73, 73);
return x_3;
}
case 2:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.EMatchTheorem", 36, 36);
x_5 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.EMatchTheorem.0.Lean.Meta.Grind.EMatchTheoremKind.explainFailure", 96, 96);
x_6 = lean_unsigned_to_nat(119u);
x_7 = lean_unsigned_to_nat(18u);
x_8 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = l_panic___at___Lean_Name_getString_x21_spec__0(x_9);
return x_10;
}
case 3:
{
lean_object* x_11; 
x_11 = lean_mk_string_unchecked("failed to use theorem's conclusion as a pattern", 47, 47);
return x_11;
}
case 4:
{
lean_object* x_12; 
x_12 = lean_mk_string_unchecked("failed to find patterns in the antecedents of the theorem", 57, 57);
return x_12;
}
case 5:
{
lean_object* x_13; 
x_13 = lean_mk_string_unchecked("failed to find patterns in the theorem's conclusion", 51, 51);
return x_13;
}
case 6:
{
lean_object* x_14; 
x_14 = lean_mk_string_unchecked("failed to find patterns searching from left to right", 52, 52);
return x_14;
}
case 7:
{
lean_object* x_15; 
x_15 = lean_mk_string_unchecked("failed to find patterns searching from right to left", 52, 52);
return x_15;
}
case 8:
{
lean_object* x_16; 
x_16 = lean_mk_string_unchecked("failed to find patterns", 23, 23);
return x_16;
}
default: 
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.EMatchTheorem", 36, 36);
x_18 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.EMatchTheorem.0.Lean.Meta.Grind.EMatchTheoremKind.explainFailure", 96, 96);
x_19 = lean_unsigned_to_nat(126u);
x_20 = lean_unsigned_to_nat(18u);
x_21 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_22 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_17, x_18, x_19, x_20, x_21);
lean_dec(x_21);
lean_dec(x_18);
lean_dec(x_17);
x_23 = l_panic___at___Lean_Name_getString_x21_spec__0(x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_explainFailure___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_explainFailure(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_1 = l_Array_empty(lean_box(0));
x_2 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_5);
lean_ctor_set(x_12, 2, x_6);
lean_ctor_set(x_12, 3, x_7);
lean_ctor_set(x_12, 4, x_8);
lean_ctor_set(x_12, 5, x_10);
x_13 = lean_unbox(x_11);
lean_ctor_set_uint8(x_12, sizeof(void*)*6, x_13);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorems() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqOrigin__1___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed), 1, 0);
x_3 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_3);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
x_5 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_3);
lean_inc(x_5);
x_7 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_5);
lean_ctor_set(x_7, 3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_2 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_3 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_4 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_6 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_5);
lean_ctor_set(x_10, 3, x_6);
lean_ctor_set(x_10, 4, x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
x_12 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_13 = l_instInhabitedOfMonad___redArg(x_11, x_12);
x_14 = lean_panic_fn(x_13, x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_13; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqOrigin__1___lam__0___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instHashableOrigin___lam__0___boxed), 1, 0);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_6 = x_13;
goto block_12;
block_12:
{
uint64_t x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; 
x_7 = l_Lean_Name_hash___override(x_6);
lean_dec(x_6);
x_8 = lean_uint64_to_usize(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_8, x_10, x_2, x_3);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__2___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_9; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_instBEqOrigin__1___lam__0___boxed), 2, 0);
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_4 = x_9;
goto block_8;
block_8:
{
uint64_t x_5; size_t x_6; lean_object* x_7; 
x_5 = l_Lean_Name_hash___override(x_4);
lean_dec(x_4);
x_6 = lean_uint64_to_usize(x_5);
x_7 = l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(x_3, x_1, x_6, x_2);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__2___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_1);
x_15 = lean_nat_dec_lt(x_3, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_3);
x_16 = lean_box(0);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_21; 
x_17 = lean_array_fget(x_1, x_3);
x_21 = lean_ctor_get(x_4, 0);
x_18 = x_21;
goto block_20;
block_20:
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_5 = x_18;
x_6 = x_19;
goto block_13;
}
}
block_13:
{
uint8_t x_7; 
x_7 = lean_name_eq(x_5, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_3, x_8);
lean_dec(x_3);
x_3 = x_9;
goto _start;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_fget(x_2, x_3);
lean_dec(x_3);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___redArg(x_2, x_3, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; size_t x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
x_6 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_7 = lean_unsigned_to_nat(5u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_shift_left(x_10, x_8);
x_12 = lean_usize_sub(x_11, x_10);
x_13 = lean_usize_land(x_2, x_12);
x_14 = lean_usize_to_nat(x_13);
x_15 = lean_array_get(x_6, x_4, x_14);
lean_dec(x_14);
lean_dec(x_4);
switch (lean_obj_tag(x_15)) {
case 0:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_24; lean_object* x_27; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_27 = lean_ctor_get(x_3, 0);
x_24 = x_27;
goto block_26;
block_23:
{
uint8_t x_20; 
x_20 = lean_name_eq(x_18, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_17);
lean_dec(x_5);
x_21 = lean_box(0);
return x_21;
}
else
{
lean_object* x_22; 
if (lean_is_scalar(x_5)) {
 x_22 = lean_alloc_ctor(1, 1, 0);
} else {
 x_22 = x_5;
 lean_ctor_set_tag(x_22, 1);
}
lean_ctor_set(x_22, 0, x_17);
return x_22;
}
}
block_26:
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_16, 0);
lean_inc(x_25);
lean_dec(x_16);
x_18 = x_24;
x_19 = x_25;
goto block_23;
}
}
case 1:
{
lean_object* x_28; size_t x_29; 
lean_dec(x_5);
x_28 = lean_ctor_get(x_15, 0);
lean_inc(x_28);
lean_dec(x_15);
x_29 = lean_usize_shift_right(x_2, x_8);
x_1 = x_28;
x_2 = x_29;
goto _start;
}
default: 
{
lean_object* x_31; 
lean_dec(x_5);
x_31 = lean_box(0);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_unsigned_to_nat(0u);
x_35 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___redArg(x_32, x_33, x_34, x_3);
lean_dec(x_33);
lean_dec(x_32);
return x_35;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
x_3 = x_8;
goto block_7;
block_7:
{
uint64_t x_4; size_t x_5; lean_object* x_6; 
x_4 = l_Lean_Name_hash___override(x_3);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___redArg(x_1, x_5, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_insert(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_2, 4);
lean_inc(x_11);
if (lean_obj_tag(x_11) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
goto block_10;
}
else
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 2)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; 
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
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 lean_ctor_release(x_1, 2);
 lean_ctor_release(x_1, 3);
 x_20 = x_1;
} else {
 lean_dec_ref(x_1);
 x_20 = lean_box(0);
}
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 3);
lean_inc(x_24);
x_25 = lean_ctor_get_uint8(x_2, sizeof(void*)*6);
x_26 = lean_ctor_get(x_2, 5);
lean_inc(x_26);
lean_dec(x_2);
lean_inc(x_26);
x_27 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_27, 0, x_21);
lean_ctor_set(x_27, 1, x_22);
lean_ctor_set(x_27, 2, x_23);
lean_ctor_set(x_27, 3, x_24);
lean_ctor_set(x_27, 4, x_13);
lean_ctor_set(x_27, 5, x_26);
lean_ctor_set_uint8(x_27, sizeof(void*)*6, x_25);
x_28 = lean_box(0);
lean_inc(x_26);
x_29 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1___redArg(x_17, x_26, x_28);
lean_inc(x_26);
x_30 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__2___redArg(x_18, x_26);
lean_inc(x_16);
x_42 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_box(0), x_16, x_15);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_box(0);
lean_inc(x_27);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_27);
lean_ctor_set(x_44, 1, x_43);
x_45 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_16, x_15, x_44);
x_31 = x_45;
goto block_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 0);
lean_inc(x_46);
lean_dec(x_42);
lean_inc(x_27);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_27);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_16, x_15, x_47);
x_31 = x_48;
goto block_41;
}
block_41:
{
lean_object* x_32; 
lean_inc(x_19);
x_32 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg(x_19, x_26);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_box(0);
if (lean_is_scalar(x_14)) {
 x_34 = lean_alloc_ctor(1, 2, 0);
} else {
 x_34 = x_14;
}
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1___redArg(x_19, x_26, x_34);
if (lean_is_scalar(x_20)) {
 x_36 = lean_alloc_ctor(0, 4, 0);
} else {
 x_36 = x_20;
}
lean_ctor_set(x_36, 0, x_31);
lean_ctor_set(x_36, 1, x_29);
lean_ctor_set(x_36, 2, x_30);
lean_ctor_set(x_36, 3, x_35);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
if (lean_is_scalar(x_14)) {
 x_38 = lean_alloc_ctor(1, 2, 0);
} else {
 x_38 = x_14;
}
lean_ctor_set(x_38, 0, x_27);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1___redArg(x_19, x_26, x_38);
if (lean_is_scalar(x_20)) {
 x_40 = lean_alloc_ctor(0, 4, 0);
} else {
 x_40 = x_20;
}
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_29);
lean_ctor_set(x_40, 2, x_30);
lean_ctor_set(x_40, 3, x_39);
return x_40;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_2);
lean_dec(x_1);
goto block_10;
}
}
block_10:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.EMatchTheorem", 36, 36);
x_4 = lean_mk_string_unchecked("Lean.Meta.Grind.EMatchTheorems.insert", 37, 37);
x_5 = lean_unsigned_to_nat(168u);
x_6 = lean_unsigned_to_nat(6u);
x_7 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_8 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_panic___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__0(x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_PersistentHashMap_findAtAux___at___Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___redArg(x_1, x_4, x_3);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_findAux___at___Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3_spec__3(x_1, x_2, x_5, x_4);
lean_dec(x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_17; 
x_13 = lean_array_fget(x_1, x_2);
x_17 = lean_ctor_get(x_3, 0);
x_14 = x_17;
goto block_16;
block_16:
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
lean_dec(x_13);
x_6 = x_14;
x_7 = x_15;
goto block_12;
}
}
block_12:
{
uint8_t x_8; 
x_8 = lean_name_eq(x_6, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_2, x_9);
lean_dec(x_2);
x_2 = x_10;
goto _start;
}
else
{
lean_dec(x_2);
return x_5;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; lean_object* x_7; size_t x_8; size_t x_9; size_t x_10; size_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_unsigned_to_nat(5u);
x_6 = lean_usize_of_nat(x_5);
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_shift_left(x_8, x_6);
x_10 = lean_usize_sub(x_9, x_8);
x_11 = lean_usize_land(x_2, x_10);
x_12 = lean_usize_to_nat(x_11);
x_13 = l_Lean_PersistentHashMap_instInhabitedEntry(lean_box(0), lean_box(0), lean_box(0));
x_14 = lean_array_get(x_13, x_4, x_12);
lean_dec(x_12);
lean_dec(x_4);
switch (lean_obj_tag(x_14)) {
case 0:
{
lean_object* x_15; lean_object* x_16; lean_object* x_20; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_20 = lean_ctor_get(x_3, 0);
x_16 = x_20;
goto block_19;
block_19:
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_name_eq(x_16, x_17);
lean_dec(x_17);
return x_18;
}
}
case 1:
{
lean_object* x_21; size_t x_22; 
x_21 = lean_ctor_get(x_14, 0);
lean_inc(x_21);
lean_dec(x_14);
x_22 = lean_usize_shift_right(x_2, x_6);
x_1 = x_21;
x_2 = x_22;
goto _start;
}
default: 
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
lean_dec(x_1);
x_27 = lean_unsigned_to_nat(0u);
x_28 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___redArg(x_26, x_27, x_3);
lean_dec(x_26);
return x_28;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_8; 
x_8 = lean_ctor_get(x_2, 0);
x_3 = x_8;
goto block_7;
block_7:
{
uint64_t x_4; size_t x_5; uint8_t x_6; 
x_4 = l_Lean_Name_hash___override(x_3);
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___redArg(x_1, x_5, x_2);
return x_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_EMatchTheorems_contains(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 1);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_contains___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_EMatchTheorems_contains(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_inc(x_2);
x_5 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__2___redArg(x_4, x_2);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__1___redArg(x_6, x_2, x_7);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_8);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_EMatchTheorems_isErased(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_isErased___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_EMatchTheorems_isErased(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_retrieve_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Name_instBEq;
x_4 = l_Lean_instHashableName;
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_inc(x_2);
lean_inc(x_5);
x_6 = l_Lean_PersistentHashMap_find_x3f___redArg(x_3, x_4, x_5, x_2);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(0);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_6);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_9 = lean_ctor_get(x_6, 0);
x_10 = l_Lean_PersistentHashMap_erase___redArg(x_3, x_4, x_5, x_2);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_12);
lean_ctor_set(x_14, 3, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_16 = lean_ctor_get(x_6, 0);
lean_inc(x_16);
lean_dec(x_6);
x_17 = l_Lean_PersistentHashMap_erase___redArg(x_3, x_4, x_5, x_2);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_21, 0, x_17);
lean_ctor_set(x_21, 1, x_18);
lean_ctor_set(x_21, 2, x_19);
lean_ctor_set(x_21, 3, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_find(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_find_x3f___at___Lean_Meta_Grind_EMatchTheorems_insert_spec__3___redArg(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_inc(x_6);
lean_dec(x_4);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_find___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_EMatchTheorems_find(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorem_getProofWithFreshMVarLevels(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_42; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_42 = l_Lean_Expr_isConst(x_7);
if (x_42 == 0)
{
x_8 = x_42;
goto block_41;
}
else
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_44 = l_Array_isEmpty___redArg(x_43);
lean_dec(x_43);
x_8 = x_44;
goto block_41;
}
block_41:
{
if (x_8 == 0)
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Array_isEmpty___redArg(x_9);
if (x_10 == 0)
{
size_t x_11; lean_object* x_12; size_t x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_array_size(x_9);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_usize_of_nat(x_12);
lean_inc(x_9);
x_14 = l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(x_11, x_13, x_9, x_2, x_3, x_4, x_5, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_9, x_16);
lean_dec(x_7);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_14, 0);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_14);
x_20 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_9, x_18);
lean_dec(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; 
lean_dec(x_9);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_7);
lean_ctor_set(x_22, 1, x_6);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = l_Lean_Expr_constName_x21(x_7);
lean_inc(x_23);
x_24 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_23, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_24) == 0)
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_ConstantInfo_levelParams(x_26);
lean_dec(x_26);
x_29 = l_List_isEmpty___redArg(x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; 
lean_free_object(x_24);
lean_dec(x_7);
x_30 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_23, x_2, x_3, x_4, x_5, x_27);
return x_30;
}
else
{
lean_dec(x_23);
lean_ctor_set(x_24, 0, x_7);
return x_24;
}
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_24, 0);
x_32 = lean_ctor_get(x_24, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_24);
x_33 = l_Lean_ConstantInfo_levelParams(x_31);
lean_dec(x_31);
x_34 = l_List_isEmpty___redArg(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_7);
x_35 = l_Lean_Meta_mkConstWithFreshMVarLevels(x_23, x_2, x_3, x_4, x_5, x_32);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_23);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_7);
lean_ctor_set(x_36, 1, x_32);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_23);
lean_dec(x_7);
x_37 = !lean_is_exclusive(x_24);
if (x_37 == 0)
{
return x_24;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_24, 0);
x_39 = lean_ctor_get(x_24, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_24);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorem_getProofWithFreshMVarLevels___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_EMatchTheorem_getProofWithFreshMVarLevels(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570_(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570____boxed), 1, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("_private", 8, 8);
x_5 = l_Lean_Name_str___override(x_3, x_4);
x_6 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_8);
x_9 = l_Lean_Name_str___override(x_7, x_8);
x_10 = lean_mk_string_unchecked("Tactic", 6, 6);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("Grind", 5, 5);
lean_inc(x_12);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("EMatchTheorem", 13, 13);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = lean_unsigned_to_nat(0u);
x_17 = l_Lean_Name_num___override(x_15, x_16);
x_18 = l_Lean_Name_str___override(x_17, x_6);
x_19 = l_Lean_Name_str___override(x_18, x_8);
x_20 = l_Lean_Name_str___override(x_19, x_12);
x_21 = lean_mk_string_unchecked("ematchTheoremsExt", 17, 17);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_EMatchTheorems_insert), 2, 0);
x_24 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_24);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_26 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_box(0));
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
lean_inc(x_26);
x_28 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_28, 0, x_25);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_26);
lean_ctor_set(x_28, 3, x_27);
x_29 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_23);
lean_ctor_set(x_29, 2, x_28);
lean_ctor_set(x_29, 3, x_2);
x_30 = l_Lean_registerSimpleScopedEnvExtension___redArg(x_29, x_1);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_initFn___lam__0____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec(x_11);
x_13 = l_Lean_ScopedEnvExtension_getState___redArg(x_7, x_9, x_8, x_12);
x_14 = lean_ctor_get(x_13, 3);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_1);
x_16 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(x_14, x_15);
lean_dec(x_15);
x_17 = lean_box(x_16);
lean_ctor_set(x_4, 0, x_17);
return x_4;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
x_18 = lean_ctor_get(x_4, 0);
x_19 = lean_ctor_get(x_4, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_4);
x_20 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get_uint8(x_24, sizeof(void*)*3);
lean_dec(x_24);
x_26 = l_Lean_ScopedEnvExtension_getState___redArg(x_20, x_22, x_21, x_25);
x_27 = lean_ctor_get(x_26, 3);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_1);
x_29 = l_Lean_PersistentHashMap_contains___at___Lean_Meta_Grind_EMatchTheorems_contains_spec__0___redArg(x_27, x_28);
lean_dec(x_28);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_19);
return x_31;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_isEMatchTheorem___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_isEMatchTheorem___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isEMatchTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_isEMatchTheorem(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
x_4 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570__spec__0(lean_box(0));
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_2);
lean_inc(x_4);
x_6 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_4);
lean_ctor_set(x_6, 2, x_4);
lean_ctor_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_take(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___lam__0___boxed), 1, 0);
x_8 = lean_ctor_get(x_5, 0);
lean_inc(x_8);
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_10 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_9, x_8, x_7);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_5, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_5, 3);
lean_inc(x_13);
x_14 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
lean_inc(x_15);
lean_ctor_set(x_3, 1, x_15);
lean_ctor_set(x_3, 0, x_15);
x_16 = lean_ctor_get(x_5, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_5, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_5, 7);
lean_inc(x_18);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_3);
lean_ctor_set(x_19, 5, x_16);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set(x_19, 7, x_18);
x_20 = lean_st_ref_set(x_1, x_19, x_6);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_27 = lean_ctor_get(x_3, 0);
x_28 = lean_ctor_get(x_3, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_3);
x_29 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___lam__0___boxed), 1, 0);
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_32 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_31, x_30, x_29);
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_27, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_27, 3);
lean_inc(x_35);
x_36 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_ctor_get(x_27, 5);
lean_inc(x_39);
x_40 = lean_ctor_get(x_27, 6);
lean_inc(x_40);
x_41 = lean_ctor_get(x_27, 7);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_42, 0, x_32);
lean_ctor_set(x_42, 1, x_33);
lean_ctor_set(x_42, 2, x_34);
lean_ctor_set(x_42, 3, x_35);
lean_ctor_set(x_42, 4, x_38);
lean_ctor_set(x_42, 5, x_39);
lean_ctor_set(x_42, 6, x_40);
lean_ctor_set(x_42, 7, x_41);
x_43 = lean_st_ref_set(x_1, x_42, x_28);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_45 = x_43;
} else {
 lean_dec_ref(x_43);
 x_45 = lean_box(0);
}
x_46 = lean_box(0);
if (lean_is_scalar(x_45)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_45;
}
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_44);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_resetEMatchTheoremsExt___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_resetEMatchTheoremsExt___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_resetEMatchTheoremsExt(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_forbiddenDeclNames() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_1 = lean_mk_string_unchecked("Eq", 2, 2);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_mk_string_unchecked("HEq", 3, 3);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("Iff", 3, 3);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("And", 3, 3);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("Or", 2, 2);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("Not", 3, 3);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(6u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = lean_array_push(x_14, x_2);
x_16 = lean_array_push(x_15, x_4);
x_17 = lean_array_push(x_16, x_6);
x_18 = lean_array_push(x_17, x_8);
x_19 = lean_array_push(x_18, x_10);
x_20 = lean_array_push(x_19, x_12);
return x_20;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isForbidden(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_forbiddenDeclNames;
x_3 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isForbidden___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isForbidden(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_splitWhileForbidden(lean_object* x_1) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_11; uint8_t x_12; 
lean_inc(x_1);
x_11 = l_Lean_Expr_cleanupAnnotations(x_1);
x_12 = l_Lean_Expr_isApp(x_11);
if (x_12 == 0)
{
lean_dec(x_11);
goto block_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
x_14 = l_Lean_Expr_appFnCleanup___redArg(x_11);
x_15 = lean_mk_string_unchecked("Not", 3, 3);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Expr_isConstOf(x_14, x_16);
lean_dec(x_16);
if (x_17 == 0)
{
uint8_t x_18; 
x_18 = l_Lean_Expr_isApp(x_14);
if (x_18 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
goto block_4;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
x_20 = l_Lean_Expr_appFnCleanup___redArg(x_14);
x_21 = lean_mk_string_unchecked("Iff", 3, 3);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Expr_isConstOf(x_20, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_mk_string_unchecked("Or", 2, 2);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Expr_isConstOf(x_20, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_mk_string_unchecked("And", 3, 3);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = l_Lean_Expr_isConstOf(x_20, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = l_Lean_Expr_isApp(x_20);
if (x_30 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_13);
goto block_4;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
lean_inc(x_20);
x_31 = l_Lean_Expr_appFnCleanup___redArg(x_20);
x_32 = lean_mk_string_unchecked("Eq", 2, 2);
x_33 = l_Lean_Name_mkStr1(x_32);
x_34 = l_Lean_Expr_isConstOf(x_31, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
uint8_t x_35; 
lean_dec(x_19);
x_35 = l_Lean_Expr_isApp(x_31);
if (x_35 == 0)
{
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_13);
goto block_4;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_36 = l_Lean_Expr_appFnCleanup___redArg(x_31);
x_37 = lean_mk_string_unchecked("HEq", 3, 3);
x_38 = l_Lean_Name_mkStr1(x_37);
x_39 = l_Lean_Expr_isConstOf(x_36, x_38);
lean_dec(x_38);
lean_dec(x_36);
if (x_39 == 0)
{
lean_dec(x_20);
lean_dec(x_13);
goto block_4;
}
else
{
lean_object* x_40; 
lean_dec(x_1);
x_40 = lean_ctor_get(x_20, 1);
lean_inc(x_40);
lean_dec(x_20);
x_5 = x_40;
x_6 = x_13;
goto block_10;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_20);
lean_dec(x_1);
x_5 = x_19;
x_6 = x_13;
goto block_10;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_1);
x_5 = x_19;
x_6 = x_13;
goto block_10;
}
}
else
{
lean_dec(x_20);
lean_dec(x_1);
x_5 = x_19;
x_6 = x_13;
goto block_10;
}
}
else
{
lean_dec(x_20);
lean_dec(x_1);
x_5 = x_19;
x_6 = x_13;
goto block_10;
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_1);
x_1 = x_13;
goto _start;
}
}
block_4:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l_Lean_Meta_Grind_splitWhileForbidden(x_5);
x_8 = l_Lean_Meta_Grind_splitWhileForbidden(x_6);
x_9 = l_List_appendTR(lean_box(0), x_7, x_8);
return x_9;
}
}
}
static lean_object* _init_l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = lean_mk_string_unchecked("[grind_dontcare]", 16, 16);
x_2 = lean_box(0);
x_3 = l_Lean_Name_str___override(x_2, x_1);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkGroundPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ground_pat", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = l_Lean_mkAnnotation(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_groundPattern_x3f(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_2 = lean_mk_string_unchecked("grind", 5, 5);
x_3 = lean_mk_string_unchecked("ground_pat", 10, 10);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = l_Lean_annotation_x3f(x_4, x_1);
lean_dec(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_groundPattern_x3f___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_groundPattern_x3f(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isGroundPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_groundPattern_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isGroundPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isGroundPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_isPatternDontCare(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_3 = lean_expr_eqv(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_isPatternDontCare___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Grind_isPatternDontCare(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isAtomicPattern(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_5; 
x_5 = l_Lean_Expr_isBVar(x_1);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = l_Lean_Meta_Grind_isPatternDontCare(x_1);
x_2 = x_6;
goto block_4;
}
else
{
x_2 = x_5;
goto block_4;
}
block_4:
{
if (x_2 == 0)
{
uint8_t x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isGroundPattern(x_1);
return x_3;
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isAtomicPattern___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isAtomicPattern(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppPattern_ppArg(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isAtomicPattern(x_1);
if (x_2 == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Grind_ppPattern(x_1);
x_4 = l_Lean_MessageData_paren(x_3);
return x_4;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_ppPattern(x_1);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_ppPattern_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
x_6 = lean_array_uget(x_1, x_3);
x_7 = lean_mk_string_unchecked(" ", 1, 1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_Meta_Grind_ppPattern_ppArg(x_6);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_ppPattern(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Grind_groundPattern_x3f(x_1);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Grind_isPatternDontCare(x_1);
if (x_3 == 0)
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("#", 1, 1);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l___private_Init_Data_Repr_0__Nat_reprFast(x_4);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = l_Lean_MessageData_ofFormat(x_8);
x_10 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_mk_string_unchecked("", 0, 0);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_14 = lean_mk_string_unchecked("Lean", 4, 4);
x_15 = lean_mk_string_unchecked("Grind", 5, 5);
x_16 = lean_mk_string_unchecked("offset", 6, 6);
x_17 = l_Lean_Name_mkStr3(x_14, x_15, x_16);
x_18 = lean_unsigned_to_nat(2u);
x_19 = l_Lean_Expr_isAppOfArity(x_1, x_17, x_18);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; size_t x_33; lean_object* x_34; size_t x_35; lean_object* x_36; 
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = l_Lean_Expr_getAppFn(x_1);
x_23 = l_Lean_MessageData_ofExpr(x_22);
lean_inc(x_21);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_21);
x_26 = lean_box(0);
x_27 = l_Lean_Expr_sort___override(x_26);
x_28 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_28);
x_29 = lean_mk_array(x_28, x_27);
x_30 = lean_unsigned_to_nat(1u);
x_31 = lean_nat_sub(x_28, x_30);
lean_dec(x_28);
x_32 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_29, x_31);
x_33 = lean_array_size(x_32);
x_34 = lean_unsigned_to_nat(0u);
x_35 = lean_usize_of_nat(x_34);
x_36 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_ppPattern_spec__0(x_32, x_33, x_35, x_25);
lean_dec(x_32);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_37 = l_Lean_Expr_getAppNumArgs(x_1);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_sub(x_37, x_38);
lean_dec(x_37);
lean_inc(x_39);
x_40 = l_Lean_Expr_getRevArg_x21(x_1, x_39);
x_41 = l_Lean_Meta_Grind_ppPattern_ppArg(x_40);
x_42 = lean_nat_sub(x_39, x_38);
lean_dec(x_39);
x_43 = l_Lean_Expr_getRevArg_x21(x_1, x_42);
lean_dec(x_1);
x_44 = l_Lean_Meta_Grind_ppPattern(x_43);
x_45 = lean_mk_string_unchecked("", 0, 0);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
lean_inc(x_46);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
x_48 = lean_mk_string_unchecked(" + ", 3, 3);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_44);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_46);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_1);
x_53 = lean_mk_string_unchecked("_", 1, 1);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_dec(x_1);
x_55 = lean_ctor_get(x_2, 0);
lean_inc(x_55);
lean_dec(x_2);
x_56 = lean_mk_string_unchecked("`[", 2, 2);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = l_Lean_MessageData_ofExpr(x_55);
x_59 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_mk_string_unchecked("]", 1, 1);
x_61 = l_Lean_stringToMessageData(x_60);
lean_dec(x_60);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_59);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_ppPattern_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Grind_ppPattern_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = l___private_Lean_HeadIndex_0__Lean_beqHeadIndex____x40_Lean_HeadIndex___hyg_69_(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = l_Lean_HeadIndex_hash(x_4);
x_8 = lean_unsigned_to_nat(32u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = lean_unsigned_to_nat(16u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_sub(x_17, x_19);
x_21 = lean_usize_land(x_16, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = l_Lean_HeadIndex_hash(x_25);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1_spec__1___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; uint8_t x_28; 
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_ctor_get(x_4, 0);
lean_dec(x_9);
x_10 = lean_ctor_get(x_6, 1);
lean_inc(x_10);
lean_dec(x_6);
x_11 = lean_array_get_size(x_10);
x_12 = l_Lean_HeadIndex_hash(x_1);
x_13 = lean_unsigned_to_nat(32u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_shift_right(x_12, x_14);
x_16 = lean_uint64_xor(x_12, x_15);
x_17 = lean_unsigned_to_nat(16u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_shift_right(x_16, x_18);
x_20 = lean_uint64_xor(x_16, x_19);
x_21 = lean_uint64_to_usize(x_20);
x_22 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_usize_of_nat(x_23);
x_25 = lean_usize_sub(x_22, x_24);
x_26 = lean_usize_land(x_21, x_25);
x_27 = lean_array_uget(x_10, x_26);
lean_dec(x_10);
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(x_1, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_4);
x_29 = lean_st_ref_take(x_2, x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_33 = lean_ctor_get(x_30, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_1);
x_36 = lean_array_push(x_33, x_1);
x_37 = lean_box(0);
x_47 = lean_array_get_size(x_35);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = lean_usize_sub(x_48, x_24);
x_50 = lean_usize_land(x_21, x_49);
x_51 = lean_array_uget(x_35, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(x_1, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; uint8_t x_64; 
x_54 = lean_ctor_get(x_31, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_31, 0);
lean_dec(x_55);
x_56 = lean_nat_add(x_34, x_23);
lean_dec(x_34);
x_57 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_37);
lean_ctor_set(x_57, 2, x_51);
x_58 = lean_array_uset(x_35, x_50, x_57);
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_shiftl(x_56, x_59);
x_61 = lean_unsigned_to_nat(3u);
x_62 = lean_nat_div(x_60, x_61);
lean_dec(x_60);
x_63 = lean_array_get_size(x_58);
x_64 = lean_nat_dec_le(x_62, x_63);
lean_dec(x_63);
lean_dec(x_62);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1___redArg(x_58);
lean_ctor_set(x_31, 1, x_65);
lean_ctor_set(x_31, 0, x_56);
x_38 = x_31;
goto block_46;
}
else
{
lean_ctor_set(x_31, 1, x_58);
lean_ctor_set(x_31, 0, x_56);
x_38 = x_31;
goto block_46;
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
lean_dec(x_31);
x_66 = lean_nat_add(x_34, x_23);
lean_dec(x_34);
x_67 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_67, 0, x_1);
lean_ctor_set(x_67, 1, x_37);
lean_ctor_set(x_67, 2, x_51);
x_68 = lean_array_uset(x_35, x_50, x_67);
x_69 = lean_unsigned_to_nat(2u);
x_70 = lean_nat_shiftl(x_66, x_69);
x_71 = lean_unsigned_to_nat(3u);
x_72 = lean_nat_div(x_70, x_71);
lean_dec(x_70);
x_73 = lean_array_get_size(x_68);
x_74 = lean_nat_dec_le(x_72, x_73);
lean_dec(x_73);
lean_dec(x_72);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; 
x_75 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1___redArg(x_68);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_66);
lean_ctor_set(x_76, 1, x_75);
x_38 = x_76;
goto block_46;
}
else
{
lean_object* x_77; 
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_66);
lean_ctor_set(x_77, 1, x_68);
x_38 = x_77;
goto block_46;
}
}
}
else
{
lean_dec(x_51);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_1);
x_38 = x_31;
goto block_46;
}
block_46:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_30, 2);
lean_inc(x_39);
lean_dec(x_30);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_38);
lean_ctor_set(x_40, 2, x_39);
x_41 = lean_st_ref_set(x_2, x_40, x_32);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
lean_ctor_set(x_41, 0, x_37);
return x_41;
}
else
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 1);
lean_inc(x_44);
lean_dec(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_37);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_78; 
lean_dec(x_1);
x_78 = lean_box(0);
lean_ctor_set(x_4, 0, x_78);
return x_4;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint64_t x_82; lean_object* x_83; uint64_t x_84; uint64_t x_85; uint64_t x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; size_t x_91; size_t x_92; lean_object* x_93; size_t x_94; size_t x_95; size_t x_96; lean_object* x_97; uint8_t x_98; 
x_79 = lean_ctor_get(x_4, 1);
lean_inc(x_79);
lean_dec(x_4);
x_80 = lean_ctor_get(x_6, 1);
lean_inc(x_80);
lean_dec(x_6);
x_81 = lean_array_get_size(x_80);
x_82 = l_Lean_HeadIndex_hash(x_1);
x_83 = lean_unsigned_to_nat(32u);
x_84 = lean_uint64_of_nat(x_83);
x_85 = lean_uint64_shift_right(x_82, x_84);
x_86 = lean_uint64_xor(x_82, x_85);
x_87 = lean_unsigned_to_nat(16u);
x_88 = lean_uint64_of_nat(x_87);
x_89 = lean_uint64_shift_right(x_86, x_88);
x_90 = lean_uint64_xor(x_86, x_89);
x_91 = lean_uint64_to_usize(x_90);
x_92 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_usize_of_nat(x_93);
x_95 = lean_usize_sub(x_92, x_94);
x_96 = lean_usize_land(x_91, x_95);
x_97 = lean_array_uget(x_80, x_96);
lean_dec(x_80);
x_98 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(x_1, x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_116; size_t x_117; size_t x_118; size_t x_119; lean_object* x_120; uint8_t x_121; 
x_99 = lean_st_ref_take(x_2, x_79);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_100, 1);
lean_inc(x_101);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
lean_inc(x_1);
x_106 = lean_array_push(x_103, x_1);
x_107 = lean_box(0);
x_116 = lean_array_get_size(x_105);
x_117 = lean_usize_of_nat(x_116);
lean_dec(x_116);
x_118 = lean_usize_sub(x_117, x_94);
x_119 = lean_usize_land(x_91, x_118);
x_120 = lean_array_uget(x_105, x_119);
x_121 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(x_1, x_120);
if (x_121 == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; 
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_122 = x_101;
} else {
 lean_dec_ref(x_101);
 x_122 = lean_box(0);
}
x_123 = lean_nat_add(x_104, x_93);
lean_dec(x_104);
x_124 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_124, 0, x_1);
lean_ctor_set(x_124, 1, x_107);
lean_ctor_set(x_124, 2, x_120);
x_125 = lean_array_uset(x_105, x_119, x_124);
x_126 = lean_unsigned_to_nat(2u);
x_127 = lean_nat_shiftl(x_123, x_126);
x_128 = lean_unsigned_to_nat(3u);
x_129 = lean_nat_div(x_127, x_128);
lean_dec(x_127);
x_130 = lean_array_get_size(x_125);
x_131 = lean_nat_dec_le(x_129, x_130);
lean_dec(x_130);
lean_dec(x_129);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; 
x_132 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__1___redArg(x_125);
if (lean_is_scalar(x_122)) {
 x_133 = lean_alloc_ctor(0, 2, 0);
} else {
 x_133 = x_122;
}
lean_ctor_set(x_133, 0, x_123);
lean_ctor_set(x_133, 1, x_132);
x_108 = x_133;
goto block_115;
}
else
{
lean_object* x_134; 
if (lean_is_scalar(x_122)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_122;
}
lean_ctor_set(x_134, 0, x_123);
lean_ctor_set(x_134, 1, x_125);
x_108 = x_134;
goto block_115;
}
}
else
{
lean_dec(x_120);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_1);
x_108 = x_101;
goto block_115;
}
block_115:
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_100, 2);
lean_inc(x_109);
lean_dec(x_100);
x_110 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_110, 0, x_106);
lean_ctor_set(x_110, 1, x_108);
lean_ctor_set(x_110, 2, x_109);
x_111 = lean_st_ref_set(x_2, x_110, x_102);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
if (lean_is_scalar(x_113)) {
 x_114 = lean_alloc_ctor(0, 2, 0);
} else {
 x_114 = x_113;
}
lean_ctor_set(x_114, 0, x_107);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_1);
x_135 = lean_box(0);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_79);
return x_136;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_nat_dec_eq(x_5, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
return x_7;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
lean_dec(x_5);
x_7 = !lean_is_exclusive(x_4);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; size_t x_20; size_t x_21; lean_object* x_22; size_t x_23; size_t x_24; size_t x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_8 = lean_ctor_get(x_4, 0);
lean_dec(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
lean_dec(x_6);
x_10 = lean_array_get_size(x_9);
x_11 = lean_uint64_of_nat(x_1);
x_12 = lean_unsigned_to_nat(32u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_unsigned_to_nat(16u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_uint64_to_usize(x_19);
x_21 = lean_usize_of_nat(x_10);
lean_dec(x_10);
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_usize_of_nat(x_22);
x_24 = lean_usize_sub(x_21, x_23);
x_25 = lean_usize_land(x_20, x_24);
x_26 = lean_array_uget(x_9, x_25);
lean_dec(x_9);
x_27 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(x_1, x_26);
lean_dec(x_26);
x_28 = lean_box(x_27);
lean_ctor_set(x_4, 0, x_28);
return x_4;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; lean_object* x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; lean_object* x_50; 
x_29 = lean_ctor_get(x_4, 1);
lean_inc(x_29);
lean_dec(x_4);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_dec(x_6);
x_31 = lean_array_get_size(x_30);
x_32 = lean_uint64_of_nat(x_1);
x_33 = lean_unsigned_to_nat(32u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_unsigned_to_nat(16u);
x_38 = lean_uint64_of_nat(x_37);
x_39 = lean_uint64_shift_right(x_36, x_38);
x_40 = lean_uint64_xor(x_36, x_39);
x_41 = lean_uint64_to_usize(x_40);
x_42 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_usize_of_nat(x_43);
x_45 = lean_usize_sub(x_42, x_44);
x_46 = lean_usize_land(x_41, x_45);
x_47 = lean_array_uget(x_30, x_46);
lean_dec(x_30);
x_48 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(x_1, x_47);
lean_dec(x_47);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_29);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; lean_object* x_23; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 2);
x_6 = lean_array_get_size(x_1);
x_7 = lean_uint64_of_nat(x_4);
x_8 = lean_unsigned_to_nat(32u);
x_9 = lean_uint64_of_nat(x_8);
x_10 = lean_uint64_shift_right(x_7, x_9);
x_11 = lean_uint64_xor(x_7, x_10);
x_12 = lean_unsigned_to_nat(16u);
x_13 = lean_uint64_of_nat(x_12);
x_14 = lean_uint64_shift_right(x_11, x_13);
x_15 = lean_uint64_xor(x_11, x_14);
x_16 = lean_uint64_to_usize(x_15);
x_17 = lean_usize_of_nat(x_6);
lean_dec(x_6);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_sub(x_17, x_19);
x_21 = lean_usize_land(x_16, x_20);
x_22 = lean_array_uget(x_1, x_21);
lean_ctor_set(x_2, 2, x_22);
x_23 = lean_array_uset(x_1, x_21, x_2);
x_1 = x_23;
x_2 = x_5;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_25 = lean_ctor_get(x_2, 0);
x_26 = lean_ctor_get(x_2, 1);
x_27 = lean_ctor_get(x_2, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_2);
x_28 = lean_array_get_size(x_1);
x_29 = lean_uint64_of_nat(x_25);
x_30 = lean_unsigned_to_nat(32u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_unsigned_to_nat(16u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_xor(x_33, x_36);
x_38 = lean_uint64_to_usize(x_37);
x_39 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_sub(x_39, x_41);
x_43 = lean_usize_land(x_38, x_42);
x_44 = lean_array_uget(x_1, x_43);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_25);
lean_ctor_set(x_45, 1, x_26);
lean_ctor_set(x_45, 2, x_44);
x_46 = lean_array_uset(x_1, x_43, x_45);
x_1 = x_46;
x_2 = x_27;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_1, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_box(0);
x_8 = lean_array_fset(x_2, x_1, x_7);
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0_spec__0___redArg(x_3, x_6);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_add(x_1, x_10);
lean_dec(x_1);
x_1 = x_11;
x_2 = x_8;
x_3 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_array_get_size(x_1);
x_3 = lean_unsigned_to_nat(1u);
x_4 = lean_nat_shiftl(x_2, x_3);
lean_dec(x_2);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_box(0);
x_7 = lean_mk_array(x_4, x_6);
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0_spec__0___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; lean_object* x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_4 = lean_st_ref_take(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_4, 1);
lean_inc(x_7);
lean_dec(x_4);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_12 = lean_box(0);
x_21 = lean_array_get_size(x_9);
x_22 = lean_uint64_of_nat(x_1);
x_23 = lean_unsigned_to_nat(32u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_unsigned_to_nat(16u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_uint64_to_usize(x_30);
x_32 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_33 = lean_unsigned_to_nat(1u);
x_34 = lean_usize_of_nat(x_33);
x_35 = lean_usize_sub(x_32, x_34);
x_36 = lean_usize_land(x_31, x_35);
x_37 = lean_array_uget(x_9, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(x_1, x_37);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_6);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_40 = lean_ctor_get(x_6, 1);
lean_dec(x_40);
x_41 = lean_ctor_get(x_6, 0);
lean_dec(x_41);
x_42 = lean_nat_add(x_8, x_33);
lean_dec(x_8);
x_43 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_43, 0, x_1);
lean_ctor_set(x_43, 1, x_12);
lean_ctor_set(x_43, 2, x_37);
x_44 = lean_array_uset(x_9, x_36, x_43);
x_45 = lean_unsigned_to_nat(2u);
x_46 = lean_nat_shiftl(x_42, x_45);
x_47 = lean_unsigned_to_nat(3u);
x_48 = lean_nat_div(x_46, x_47);
lean_dec(x_46);
x_49 = lean_array_get_size(x_44);
x_50 = lean_nat_dec_le(x_48, x_49);
lean_dec(x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0___redArg(x_44);
lean_ctor_set(x_6, 1, x_51);
lean_ctor_set(x_6, 0, x_42);
x_13 = x_6;
goto block_20;
}
else
{
lean_ctor_set(x_6, 1, x_44);
lean_ctor_set(x_6, 0, x_42);
x_13 = x_6;
goto block_20;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_6);
x_52 = lean_nat_add(x_8, x_33);
lean_dec(x_8);
x_53 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_53, 0, x_1);
lean_ctor_set(x_53, 1, x_12);
lean_ctor_set(x_53, 2, x_37);
x_54 = lean_array_uset(x_9, x_36, x_53);
x_55 = lean_unsigned_to_nat(2u);
x_56 = lean_nat_shiftl(x_52, x_55);
x_57 = lean_unsigned_to_nat(3u);
x_58 = lean_nat_div(x_56, x_57);
lean_dec(x_56);
x_59 = lean_array_get_size(x_54);
x_60 = lean_nat_dec_le(x_58, x_59);
lean_dec(x_59);
lean_dec(x_58);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = l_Std_DHashMap_Internal_Raw_u2080_expand___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar_spec__0___redArg(x_54);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
x_13 = x_62;
goto block_20;
}
else
{
lean_object* x_63; 
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_52);
lean_ctor_set(x_63, 1, x_54);
x_13 = x_63;
goto block_20;
}
}
}
else
{
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_13 = x_6;
goto block_20;
}
block_20:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_11);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_st_ref_set(x_2, x_14, x_7);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_15, 0);
lean_dec(x_17);
lean_ctor_set(x_15, 0, x_12);
return x_15;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_toCtorIdx(uint8_t x_1) {
_start:
{
switch (x_1) {
case 0:
{
lean_object* x_2; 
x_2 = lean_unsigned_to_nat(0u);
return x_2;
}
case 1:
{
lean_object* x_3; 
x_3 = lean_unsigned_to_nat(1u);
return x_3;
}
case 2:
{
lean_object* x_4; 
x_4 = lean_unsigned_to_nat(2u);
return x_4;
}
default: 
{
lean_object* x_5; 
x_5 = lean_unsigned_to_nat(3u);
return x_5;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_toCtorIdx___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_toCtorIdx(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___redArg(uint8_t x_1, uint8_t x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_EMatchTheoremKind_noConfusion___redArg___lam__0___boxed), 1, 0);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___redArg(x_2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = lean_unbox(x_2);
lean_dec(x_2);
x_5 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___redArg(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_noConfusion(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_reprPatternArgKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_3551_(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; lean_object* x_30; 
switch (x_1) {
case 0:
{
lean_object* x_39; uint8_t x_40; 
x_39 = lean_unsigned_to_nat(1024u);
x_40 = lean_nat_dec_le(x_39, x_2);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_nat_to_int(x_41);
x_3 = x_42;
goto block_11;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_unsigned_to_nat(1u);
x_44 = lean_nat_to_int(x_43);
x_3 = x_44;
goto block_11;
}
}
case 1:
{
lean_object* x_45; uint8_t x_46; 
x_45 = lean_unsigned_to_nat(1024u);
x_46 = lean_nat_dec_le(x_45, x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_to_int(x_47);
x_12 = x_48;
goto block_20;
}
else
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_unsigned_to_nat(1u);
x_50 = lean_nat_to_int(x_49);
x_12 = x_50;
goto block_20;
}
}
case 2:
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_unsigned_to_nat(1024u);
x_52 = lean_nat_dec_le(x_51, x_2);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_to_int(x_53);
x_21 = x_54;
goto block_29;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_unsigned_to_nat(1u);
x_56 = lean_nat_to_int(x_55);
x_21 = x_56;
goto block_29;
}
}
default: 
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_unsigned_to_nat(1024u);
x_58 = lean_nat_dec_le(x_57, x_2);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_unsigned_to_nat(2u);
x_60 = lean_nat_to_int(x_59);
x_30 = x_60;
goto block_38;
}
else
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_nat_to_int(x_61);
x_30 = x_62;
goto block_38;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Meta.Grind.NormalizePattern.PatternArgKind.relevant", 56, 56);
x_5 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_8, 0, x_6);
x_9 = lean_unbox(x_7);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
x_10 = l_Repr_addAppParen(x_8, x_2);
return x_10;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_13 = lean_mk_string_unchecked("Lean.Meta.Grind.NormalizePattern.PatternArgKind.instImplicit", 60, 60);
x_14 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_17, 0, x_15);
x_18 = lean_unbox(x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_18);
x_19 = l_Repr_addAppParen(x_17, x_2);
return x_19;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.Meta.Grind.NormalizePattern.PatternArgKind.proof", 53, 53);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_26, 0, x_24);
x_27 = lean_unbox(x_25);
lean_ctor_set_uint8(x_26, sizeof(void*)*1, x_27);
x_28 = l_Repr_addAppParen(x_26, x_2);
return x_28;
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_31 = lean_mk_string_unchecked("Lean.Meta.Grind.NormalizePattern.PatternArgKind.typeFormer", 58, 58);
x_32 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_35, 0, x_33);
x_36 = lean_unbox(x_34);
lean_ctor_set_uint8(x_35, sizeof(void*)*1, x_36);
x_37 = l_Repr_addAppParen(x_35, x_2);
return x_37;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_reprPatternArgKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_3551____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_reprPatternArgKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_3551_(x_3, x_2);
lean_dec(x_2);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_Grind_NormalizePattern_instReprPatternArgKind() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_reprPatternArgKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_3551____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(uint8_t x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(x_1);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_box(0);
x_4 = lean_unbox(x_3);
return x_4;
}
else
{
lean_object* x_5; uint8_t x_6; 
lean_dec(x_2);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox(x_1);
lean_dec(x_1);
x_3 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
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
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_array_fget(x_2, x_4);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_15);
x_16 = l_Lean_Meta_isProp(x_15, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; uint8_t x_27; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_nat_sub(x_3, x_14);
lean_dec(x_3);
x_27 = lean_unbox(x_17);
lean_dec(x_17);
if (x_27 == 0)
{
lean_object* x_28; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_15);
x_28 = l_Lean_Meta_isProof(x_15, x_6, x_7, x_8, x_9, x_18);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_28, 1);
lean_inc(x_31);
lean_dec(x_28);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_15);
x_32 = l_Lean_Meta_isTypeFormer(x_15, x_6, x_7, x_8, x_9, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_unbox(x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = l_Lean_Expr_fvarId_x21(x_15);
lean_dec(x_15);
lean_inc(x_6);
x_37 = l_Lean_FVarId_getDecl___redArg(x_36, x_6, x_8, x_9, x_35);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_LocalDecl_binderInfo(x_38);
lean_dec(x_38);
x_41 = lean_box(x_40);
if (lean_obj_tag(x_41) == 3)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_box(1);
x_43 = lean_unbox(x_42);
x_20 = x_43;
x_21 = x_39;
goto block_26;
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_dec(x_41);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
x_20 = x_45;
x_21 = x_39;
goto block_26;
}
}
else
{
uint8_t x_46; 
lean_dec(x_19);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_37);
if (x_46 == 0)
{
return x_37;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_37, 0);
x_48 = lean_ctor_get(x_37, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_37);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_15);
x_50 = lean_ctor_get(x_32, 1);
lean_inc(x_50);
lean_dec(x_32);
x_51 = lean_array_get_size(x_1);
x_52 = lean_nat_dec_lt(x_4, x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_box(3);
x_54 = lean_unbox(x_53);
x_20 = x_54;
x_21 = x_50;
goto block_26;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_array_fget(x_1, x_4);
x_56 = lean_ctor_get_uint8(x_55, sizeof(void*)*1 + 1);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_box(0);
x_58 = lean_unbox(x_57);
x_20 = x_58;
x_21 = x_50;
goto block_26;
}
else
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_box(3);
x_60 = lean_unbox(x_59);
x_20 = x_60;
x_21 = x_50;
goto block_26;
}
}
}
}
else
{
uint8_t x_61; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_61 = !lean_is_exclusive(x_32);
if (x_61 == 0)
{
return x_32;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_32, 0);
x_63 = lean_ctor_get(x_32, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_32);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; uint8_t x_67; 
lean_dec(x_15);
x_65 = lean_ctor_get(x_28, 1);
lean_inc(x_65);
lean_dec(x_28);
x_66 = lean_box(2);
x_67 = lean_unbox(x_66);
x_20 = x_67;
x_21 = x_65;
goto block_26;
}
}
else
{
uint8_t x_68; 
lean_dec(x_19);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_68 = !lean_is_exclusive(x_28);
if (x_68 == 0)
{
return x_28;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_28, 0);
x_70 = lean_ctor_get(x_28, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_28);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
else
{
lean_object* x_72; uint8_t x_73; 
lean_dec(x_15);
x_72 = lean_box(0);
x_73 = lean_unbox(x_72);
x_20 = x_73;
x_21 = x_18;
goto block_26;
}
block_26:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_23 = lean_box(x_20);
x_24 = lean_array_push(x_5, x_23);
x_3 = x_19;
x_4 = x_22;
x_5 = x_24;
x_10 = x_21;
goto _start;
}
}
else
{
uint8_t x_74; 
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_74 = !lean_is_exclusive(x_16);
if (x_74 == 0)
{
return x_16;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_16, 0);
x_76 = lean_ctor_get(x_16, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_16);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_mk_empty_array_with_capacity(x_9);
x_12 = l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___redArg(x_1, x_2, x_9, x_10, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_8 = l_Lean_Meta_getFunInfoNArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
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
x_11 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds___lam__0___boxed), 8, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_12, x_16, x_15, x_18, x_3, x_4, x_5, x_6, x_13);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_11);
if (x_20 == 0)
{
return x_11;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_11, 0);
x_22 = lean_ctor_get(x_11, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_11);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_8);
if (x_24 == 0)
{
return x_8;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_8, 0);
x_26 = lean_ctor_get(x_8, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_8);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_mapFinIdxM_map___at___Lean_Meta_Grind_NormalizePattern_getPatternArgKinds_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_isInductiveCore(x_7, x_1);
x_9 = lean_box(x_8);
lean_ctor_set(x_4, 0, x_9);
return x_4;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_4, 0);
x_11 = lean_ctor_get(x_4, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_4);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_isInductiveCore(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___redArg(x_1, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; lean_object* x_14; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_91; 
x_91 = l_Lean_Expr_isApp(x_1);
if (x_91 == 0)
{
uint8_t x_92; 
x_92 = l_Lean_Expr_isConst(x_1);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_box(0);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_8);
return x_94;
}
else
{
goto block_90;
}
}
else
{
goto block_90;
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
block_25:
{
lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_15 = l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___redArg(x_14, x_7, x_8);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_unbox(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_13);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_9 = x_18;
goto block_12;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_15);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_15, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_13);
lean_ctor_set(x_15, 0, x_21);
return x_15;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_15, 1);
lean_inc(x_22);
lean_dec(x_15);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_13);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
block_29:
{
if (x_28 == 0)
{
lean_dec(x_27);
lean_dec(x_26);
x_9 = x_8;
goto block_12;
}
else
{
x_13 = x_26;
x_14 = x_27;
goto block_25;
}
}
block_90:
{
lean_object* x_30; 
x_30 = l_Lean_Expr_getAppFn(x_1);
switch (lean_obj_tag(x_30)) {
case 0:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = l_Lean_Expr_bvar___override(x_31);
x_33 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_32, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_32);
return x_33;
}
case 1:
{
if (x_2 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = l_Lean_Expr_fvar___override(x_34);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_8);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_30);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_8);
return x_39;
}
}
case 2:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 0);
lean_inc(x_40);
lean_dec(x_30);
x_41 = l_Lean_Expr_mvar___override(x_40);
x_42 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_41, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_41);
return x_42;
}
case 3:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_30, 0);
lean_inc(x_43);
lean_dec(x_30);
x_44 = l_Lean_Expr_sort___override(x_43);
x_45 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_44, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_44);
return x_45;
}
case 4:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_30, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_30, 1);
lean_inc(x_47);
lean_dec(x_30);
x_48 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isForbidden(x_46);
if (x_48 == 0)
{
lean_object* x_49; 
lean_inc(x_46);
x_49 = l_Lean_Expr_const___override(x_46, x_47);
if (x_2 == 0)
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_46);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_8);
return x_51;
}
else
{
lean_object* x_52; 
x_52 = lean_box(x_3);
switch (lean_obj_tag(x_52)) {
case 1:
{
x_26 = x_49;
x_27 = x_46;
x_28 = x_48;
goto block_29;
}
case 2:
{
x_26 = x_49;
x_27 = x_46;
x_28 = x_48;
goto block_29;
}
default: 
{
lean_dec(x_52);
x_13 = x_49;
x_14 = x_46;
goto block_25;
}
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_47);
lean_dec(x_46);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_8);
return x_54;
}
}
case 5:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_30, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_30, 1);
lean_inc(x_56);
lean_dec(x_30);
x_57 = l_Lean_Expr_app___override(x_55, x_56);
x_58 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_57, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_57);
return x_58;
}
case 6:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_30, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_30, 1);
lean_inc(x_60);
x_61 = lean_ctor_get(x_30, 2);
lean_inc(x_61);
x_62 = lean_ctor_get_uint8(x_30, sizeof(void*)*3 + 8);
lean_dec(x_30);
x_63 = l_Lean_Expr_lam___override(x_59, x_60, x_61, x_62);
x_64 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_63, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_63);
return x_64;
}
case 7:
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; lean_object* x_70; 
x_65 = lean_ctor_get(x_30, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_30, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_30, 2);
lean_inc(x_67);
x_68 = lean_ctor_get_uint8(x_30, sizeof(void*)*3 + 8);
lean_dec(x_30);
x_69 = l_Lean_Expr_forallE___override(x_65, x_66, x_67, x_68);
x_70 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_69, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_69);
return x_70;
}
case 8:
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_ctor_get(x_30, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_30, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_30, 2);
lean_inc(x_73);
x_74 = lean_ctor_get(x_30, 3);
lean_inc(x_74);
x_75 = lean_ctor_get_uint8(x_30, sizeof(void*)*4 + 8);
lean_dec(x_30);
x_76 = l_Lean_Expr_letE___override(x_71, x_72, x_73, x_74, x_75);
x_77 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_76, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_76);
return x_77;
}
case 9:
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_30, 0);
lean_inc(x_78);
lean_dec(x_30);
x_79 = l_Lean_Expr_lit___override(x_78);
x_80 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_79, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_79);
return x_80;
}
case 10:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_30, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_30, 1);
lean_inc(x_82);
lean_dec(x_30);
x_83 = l_Lean_Expr_mdata___override(x_81, x_82);
x_84 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_83, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_83);
return x_84;
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_85 = lean_ctor_get(x_30, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_30, 1);
lean_inc(x_86);
x_87 = lean_ctor_get(x_30, 2);
lean_inc(x_87);
lean_dec(x_30);
x_88 = l_Lean_Expr_proj___override(x_85, x_86, x_87);
x_89 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_88, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_88);
return x_89;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isInductive___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_goArg(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = l_Lean_Expr_hasLooseBVars(x_1);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_11 = l_Lean_Expr_hasMVar(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_Meta_Grind_mkGroundPattern(x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
}
else
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar___redArg(x_16, x_4, x_9);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
if (x_2 == 0)
{
lean_free_object(x_17);
lean_dec(x_19);
goto block_26;
}
else
{
uint8_t x_27; 
x_27 = lean_unbox(x_19);
lean_dec(x_19);
if (x_27 == 0)
{
lean_free_object(x_17);
goto block_26;
}
else
{
lean_object* x_28; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_28 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
}
block_26:
{
lean_object* x_21; uint8_t x_22; 
x_21 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg(x_16, x_4, x_20);
lean_dec(x_4);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_1);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_1);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
if (x_2 == 0)
{
lean_dec(x_29);
goto block_35;
}
else
{
uint8_t x_36; 
x_36 = lean_unbox(x_29);
lean_dec(x_29);
if (x_36 == 0)
{
goto block_35;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_1);
x_37 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_30);
return x_38;
}
}
block_35:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveBVar___redArg(x_16, x_4, x_30);
lean_dec(x_4);
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_33 = x_31;
} else {
 lean_dec_ref(x_31);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_1);
lean_ctor_set(x_34, 1, x_32);
return x_34;
}
}
}
else
{
lean_object* x_39; lean_object* x_40; 
x_39 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_41 = !lean_is_exclusive(x_39);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_39, 0);
lean_dec(x_42);
x_43 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
lean_ctor_set(x_39, 0, x_43);
return x_39;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_39, 1);
lean_inc(x_44);
lean_dec(x_39);
x_45 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
else
{
lean_object* x_47; lean_object* x_48; 
lean_dec(x_40);
x_47 = lean_ctor_get(x_39, 1);
lean_inc(x_47);
lean_dec(x_39);
x_48 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go(x_1, x_2, x_4, x_5, x_6, x_7, x_8, x_47);
return x_48;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_1, x_2, x_3, x_4, x_5, x_6);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_4, 5);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_7, 0);
x_13 = lean_ctor_get(x_7, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_7);
x_14 = lean_ctor_get(x_4, 5);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg(x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_nat_dec_lt(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; uint8_t x_17; uint8_t x_30; lean_object* x_33; uint8_t x_34; 
x_15 = lean_array_fget(x_4, x_5);
x_33 = lean_array_get_size(x_2);
x_34 = lean_nat_dec_lt(x_5, x_33);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_30 = x_36;
goto block_32;
}
else
{
lean_object* x_37; uint8_t x_38; 
x_37 = lean_array_fget(x_2, x_5);
x_38 = lean_unbox(x_37);
lean_dec(x_37);
x_30 = x_38;
goto block_32;
}
block_29:
{
lean_object* x_18; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_18 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_goArg(x_15, x_17, x_16, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_array_fset(x_4, x_5, x_19);
x_22 = lean_ctor_get(x_3, 2);
x_23 = lean_nat_add(x_5, x_22);
lean_dec(x_5);
x_4 = x_21;
x_5 = x_23;
x_11 = x_20;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_25 = !lean_is_exclusive(x_18);
if (x_25 == 0)
{
return x_18;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_18, 0);
x_27 = lean_ctor_get(x_18, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_18);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
block_32:
{
if (x_1 == 0)
{
uint8_t x_31; 
x_31 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_30);
x_16 = x_30;
x_17 = x_31;
goto block_29;
}
else
{
x_16 = x_30;
x_17 = x_1;
goto block_29;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
x_15 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___redArg(x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_12 = l_instMonadEIO(lean_box(0));
x_13 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_17, 0, x_15);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_20 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_23 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_23, 0, x_22);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_25, 0, lean_box(0));
lean_closure_set(x_25, 1, lean_box(0));
x_26 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
lean_inc(x_27);
lean_inc(x_24);
lean_inc(x_21);
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
x_30 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_29);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
lean_dec(x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
lean_inc(x_32);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_34, 0, x_32);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_36, 0, x_21);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_24);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_38);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_27);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_42, 0, x_35);
lean_ctor_set(x_42, 1, x_8);
lean_ctor_set(x_42, 2, x_37);
lean_ctor_set(x_42, 3, x_39);
lean_ctor_set(x_42, 4, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_9);
x_44 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_43);
x_45 = l_Lean_instInhabitedExpr;
x_46 = l_instInhabitedOfMonad___redArg(x_44, x_45);
x_47 = lean_panic_fn(x_46, x_1);
x_48 = lean_apply_6(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
return x_48;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_Meta_Grind_isOffsetPattern_x3f(x_1);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_getPatternFn_x3f(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_3);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_ctor_get(x_12, 0);
lean_dec(x_16);
x_17 = lean_mk_string_unchecked("invalid pattern, (non-forbidden) application expected", 53, 53);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = l_Lean_indentExpr(x_1);
lean_ctor_set_tag(x_12, 7);
lean_ctor_set(x_12, 1, x_19);
lean_ctor_set(x_12, 0, x_18);
x_20 = lean_mk_string_unchecked("", 0, 0);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_12);
lean_ctor_set(x_22, 1, x_21);
x_23 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg(x_22, x_4, x_5, x_6, x_7, x_15);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
lean_dec(x_12);
x_25 = lean_mk_string_unchecked("invalid pattern, (non-forbidden) application expected", 53, 53);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = l_Lean_indentExpr(x_1);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg(x_31, x_4, x_5, x_6, x_7, x_24);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_71; uint8_t x_88; 
x_33 = lean_ctor_get(x_12, 1);
lean_inc(x_33);
lean_dec(x_12);
x_34 = lean_ctor_get(x_13, 0);
lean_inc(x_34);
lean_dec(x_13);
x_88 = l_Lean_Expr_isConst(x_34);
if (x_88 == 0)
{
uint8_t x_89; 
x_89 = l_Lean_Expr_isFVar(x_34);
x_71 = x_89;
goto block_87;
}
else
{
x_71 = x_88;
goto block_87;
}
block_70:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_41 = lean_box(0);
x_42 = l_Lean_Expr_sort___override(x_41);
x_43 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_43);
x_44 = lean_mk_array(x_43, x_42);
x_45 = lean_unsigned_to_nat(1u);
x_46 = lean_nat_sub(x_43, x_45);
lean_dec(x_43);
x_47 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_44, x_46);
x_48 = lean_array_get_size(x_47);
lean_inc(x_39);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_48);
lean_inc(x_34);
x_49 = l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(x_34, x_48, x_36, x_37, x_38, x_39, x_40);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_48);
lean_ctor_set(x_53, 2, x_45);
x_54 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___redArg(x_2, x_50, x_53, x_47, x_52, x_35, x_36, x_37, x_38, x_39, x_51);
lean_dec(x_53);
lean_dec(x_50);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_54, 0);
x_57 = l_Lean_mkAppN(x_34, x_56);
lean_dec(x_56);
lean_ctor_set(x_54, 0, x_57);
return x_54;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_54, 0);
x_59 = lean_ctor_get(x_54, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_54);
x_60 = l_Lean_mkAppN(x_34, x_58);
lean_dec(x_58);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_34);
x_62 = !lean_is_exclusive(x_54);
if (x_62 == 0)
{
return x_54;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_54, 0);
x_64 = lean_ctor_get(x_54, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_54);
x_65 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
}
else
{
uint8_t x_66; 
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
x_66 = !lean_is_exclusive(x_49);
if (x_66 == 0)
{
return x_49;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_49, 0);
x_68 = lean_ctor_get(x_49, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_49);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
block_87:
{
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_34);
lean_dec(x_1);
x_72 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.EMatchTheorem", 36, 36);
x_73 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.EMatchTheorem.0.Lean.Meta.Grind.NormalizePattern.go", 83, 83);
x_74 = lean_unsigned_to_nat(431u);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_mk_string_unchecked("assertion violation: f.isConst || f.isFVar\n  ", 45, 45);
x_77 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_72, x_73, x_74, x_75, x_76);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
x_78 = l_panic___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__2(x_77, x_3, x_4, x_5, x_6, x_7, x_33);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_79 = lean_mk_string_unchecked("Lean", 4, 4);
x_80 = lean_mk_string_unchecked("Grind", 5, 5);
x_81 = lean_mk_string_unchecked("eqBwdPattern", 12, 12);
x_82 = l_Lean_Name_mkStr3(x_79, x_80, x_81);
x_83 = l_Lean_Expr_isConstOf(x_34, x_82);
lean_dec(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_inc(x_34);
x_84 = l_Lean_Expr_toHeadIndex(x_34);
x_85 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_saveSymbol___redArg(x_84, x_3, x_33);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_35 = x_3;
x_36 = x_4;
x_37 = x_5;
x_38 = x_6;
x_39 = x_7;
x_40 = x_86;
goto block_70;
}
else
{
x_35 = x_3;
x_36 = x_4;
x_37 = x_5;
x_38 = x_6;
x_39 = x_7;
x_40 = x_33;
goto block_70;
}
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
lean_dec(x_1);
x_90 = lean_ctor_get(x_9, 0);
lean_inc(x_90);
lean_dec(x_9);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_box(0);
x_94 = lean_unbox(x_93);
x_95 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_goArg(x_91, x_2, x_94, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_99 = lean_expr_eqv(x_97, x_98);
if (x_99 == 0)
{
lean_object* x_100; 
x_100 = l_Lean_Meta_Grind_mkOffsetPattern(x_97, x_92);
lean_ctor_set(x_95, 0, x_100);
return x_95;
}
else
{
lean_dec(x_97);
lean_dec(x_92);
lean_ctor_set(x_95, 0, x_98);
return x_95;
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; uint8_t x_104; 
x_101 = lean_ctor_get(x_95, 0);
x_102 = lean_ctor_get(x_95, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_95);
x_103 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare;
x_104 = lean_expr_eqv(x_101, x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; 
x_105 = l_Lean_Meta_Grind_mkOffsetPattern(x_101, x_92);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_102);
return x_106;
}
else
{
lean_object* x_107; 
lean_dec(x_101);
lean_dec(x_92);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_103);
lean_ctor_set(x_107, 1, x_102);
return x_107;
}
}
}
else
{
lean_dec(x_92);
return x_95;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_goArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_goArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___redArg(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_2);
lean_dec(x_2);
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go_spec__1(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at___Lean_Meta_Grind_NormalizePattern_main_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_9 = l_List_reverse___redArg(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_1);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go(x_12, x_15, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_17);
{
lean_object* _tmp_0 = x_13;
lean_object* _tmp_1 = x_1;
lean_object* _tmp_7 = x_18;
x_1 = _tmp_0;
x_2 = _tmp_1;
x_8 = _tmp_7;
}
goto _start;
}
else
{
uint8_t x_20; 
lean_free_object(x_1);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_20 = !lean_is_exclusive(x_16);
if (x_20 == 0)
{
return x_16;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_16, 0);
x_22 = lean_ctor_get(x_16, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_16);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_1, 0);
x_25 = lean_ctor_get(x_1, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_1);
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_28 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go(x_24, x_27, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_2);
x_1 = x_25;
x_2 = x_31;
x_8 = x_30;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_25);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_33 = lean_ctor_get(x_28, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
if (lean_is_exclusive(x_28)) {
 lean_ctor_release(x_28, 0);
 lean_ctor_release(x_28, 1);
 x_35 = x_28;
} else {
 lean_dec_ref(x_28);
 x_35 = lean_box(0);
}
if (lean_is_scalar(x_35)) {
 x_36 = lean_alloc_ctor(1, 2, 0);
} else {
 x_36 = x_35;
}
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_unsigned_to_nat(8u);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_nat_shiftl(x_9, x_10);
x_12 = lean_unsigned_to_nat(3u);
x_13 = lean_nat_div(x_11, x_12);
lean_dec(x_11);
x_14 = l_Nat_nextPowerOfTwo(x_13);
lean_dec(x_13);
x_15 = lean_box(0);
lean_inc(x_14);
x_16 = lean_mk_array(x_14, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_7);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_14, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_21, 0, x_8);
lean_ctor_set(x_21, 1, x_17);
lean_ctor_set(x_21, 2, x_20);
x_22 = lean_st_mk_ref(x_21, x_6);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_box(0);
lean_inc(x_24);
x_27 = l_List_mapM_loop___at___Lean_Meta_Grind_NormalizePattern_main_spec__0(x_1, x_26, x_24, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_st_ref_get(x_24, x_29);
lean_dec(x_24);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_30, 0);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_array_to_list(x_33);
x_35 = lean_ctor_get(x_32, 2);
lean_inc(x_35);
lean_dec(x_32);
lean_ctor_set(x_22, 1, x_35);
lean_ctor_set(x_22, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_22);
lean_ctor_set(x_30, 0, x_36);
return x_30;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_30, 0);
x_38 = lean_ctor_get(x_30, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_30);
x_39 = lean_ctor_get(x_37, 0);
lean_inc(x_39);
x_40 = lean_array_to_list(x_39);
x_41 = lean_ctor_get(x_37, 2);
lean_inc(x_41);
lean_dec(x_37);
lean_ctor_set(x_22, 1, x_41);
lean_ctor_set(x_22, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_28);
lean_ctor_set(x_42, 1, x_22);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_38);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_22);
lean_dec(x_24);
x_44 = !lean_is_exclusive(x_27);
if (x_44 == 0)
{
return x_27;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_27, 0);
x_46 = lean_ctor_get(x_27, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_27);
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
x_48 = lean_ctor_get(x_22, 0);
x_49 = lean_ctor_get(x_22, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_22);
x_50 = lean_box(0);
lean_inc(x_48);
x_51 = l_List_mapM_loop___at___Lean_Meta_Grind_NormalizePattern_main_spec__0(x_1, x_50, x_48, x_2, x_3, x_4, x_5, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_ref_get(x_48, x_53);
lean_dec(x_48);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_54, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_57 = x_54;
} else {
 lean_dec_ref(x_54);
 x_57 = lean_box(0);
}
x_58 = lean_ctor_get(x_55, 0);
lean_inc(x_58);
x_59 = lean_array_to_list(x_58);
x_60 = lean_ctor_get(x_55, 2);
lean_inc(x_60);
lean_dec(x_55);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_52);
lean_ctor_set(x_62, 1, x_61);
if (lean_is_scalar(x_57)) {
 x_63 = lean_alloc_ctor(0, 2, 0);
} else {
 x_63 = x_57;
}
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_56);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_dec(x_48);
x_64 = lean_ctor_get(x_51, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_51, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_51)) {
 lean_ctor_release(x_51, 0);
 lean_ctor_release(x_51, 1);
 x_66 = x_51;
} else {
 lean_dec_ref(x_51);
 x_66 = lean_box(0);
}
if (lean_is_scalar(x_66)) {
 x_67 = lean_alloc_ctor(1, 2, 0);
} else {
 x_67 = x_66;
}
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_65);
return x_67;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_NormalizePattern_normalizePattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_go(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_15; lean_object* x_16; 
x_7 = lean_box(1);
x_15 = lean_array_uget(x_3, x_4);
x_16 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_15);
x_8 = x_6;
goto block_14;
}
else
{
lean_object* x_17; 
lean_dec(x_16);
x_17 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_2, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = lean_unbox(x_7);
return x_18;
}
else
{
lean_dec(x_17);
x_8 = x_6;
goto block_14;
}
}
block_14:
{
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_4, x_10);
x_4 = x_11;
goto _start;
}
else
{
uint8_t x_13; 
x_13 = lean_unbox(x_7);
return x_13;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
return x_20;
}
}
}
LEAN_EXPORT uint8_t l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_4 = lean_unsigned_to_nat(8u);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_unsigned_to_nat(2u);
x_7 = lean_nat_shiftl(x_4, x_6);
x_8 = lean_unsigned_to_nat(3u);
x_9 = lean_nat_div(x_7, x_8);
lean_dec(x_7);
x_10 = l_Nat_nextPowerOfTwo(x_9);
lean_dec(x_9);
x_11 = lean_box(0);
x_12 = lean_mk_array(x_10, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_5);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_box(0);
x_15 = lean_mk_empty_array_with_capacity(x_5);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_14);
lean_ctor_set(x_16, 2, x_15);
x_17 = l_Lean_CollectFVars_main(x_3, x_16);
x_18 = lean_ctor_get(x_17, 2);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_array_get_size(x_18);
x_20 = lean_nat_dec_lt(x_5, x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_19);
lean_dec(x_18);
x_21 = lean_box(1);
x_22 = lean_unbox(x_21);
return x_22;
}
else
{
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_18);
return x_20;
}
else
{
size_t x_23; size_t x_24; uint8_t x_25; 
x_23 = lean_usize_of_nat(x_5);
x_24 = lean_usize_of_nat(x_19);
lean_dec(x_19);
x_25 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars_spec__0(x_1, x_2, x_18, x_23, x_24);
lean_dec(x_18);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_box(0);
x_27 = lean_unbox(x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; uint8_t x_8; lean_object* x_9; 
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_8 = l_Array_anyMUnsafe_any___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars_spec__0(x_1, x_2, x_3, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_9 = lean_box(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_6, 1);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
x_18 = lean_nat_dec_lt(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_14);
lean_ctor_set(x_19, 1, x_15);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_22 = lean_infer_type(x_21, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_ctor_get(x_15, 0);
lean_inc(x_33);
lean_dec(x_15);
x_34 = lean_nat_add(x_16, x_32);
lean_inc(x_33);
x_35 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
lean_ctor_set(x_35, 2, x_17);
x_38 = lean_mk_string_unchecked("semiOutParam", 12, 12);
x_39 = l_Lean_Name_mkStr1(x_38);
x_40 = l_Lean_Expr_isAppOf(x_24, x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_mk_string_unchecked("outParam", 8, 8);
x_42 = l_Lean_Name_mkStr1(x_41);
x_43 = l_Lean_Expr_isAppOf(x_24, x_42);
lean_dec(x_42);
lean_dec(x_24);
if (x_43 == 0)
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_array_fget(x_33, x_16);
lean_dec(x_16);
lean_dec(x_33);
x_45 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(x_1, x_2, x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_35);
lean_ctor_set(x_22, 0, x_48);
return x_22;
}
else
{
lean_object* x_49; 
lean_free_object(x_22);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_14);
lean_ctor_set(x_49, 1, x_35);
x_26 = x_49;
goto block_31;
}
}
else
{
lean_dec(x_33);
lean_free_object(x_22);
lean_dec(x_16);
goto block_37;
}
}
else
{
lean_dec(x_33);
lean_free_object(x_22);
lean_dec(x_24);
lean_dec(x_16);
goto block_37;
}
block_31:
{
lean_object* x_27; size_t x_28; size_t x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_add(x_5, x_28);
x_5 = x_29;
x_6 = x_26;
x_11 = x_25;
goto _start;
}
block_37:
{
lean_object* x_36; 
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_14);
lean_ctor_set(x_36, 1, x_35);
x_26 = x_36;
goto block_31;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_50 = lean_ctor_get(x_22, 0);
x_51 = lean_ctor_get(x_22, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_22);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_ctor_get(x_15, 0);
lean_inc(x_59);
lean_dec(x_15);
x_60 = lean_nat_add(x_16, x_58);
lean_inc(x_59);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
lean_ctor_set(x_61, 2, x_17);
x_64 = lean_mk_string_unchecked("semiOutParam", 12, 12);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = l_Lean_Expr_isAppOf(x_50, x_65);
lean_dec(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; uint8_t x_69; 
x_67 = lean_mk_string_unchecked("outParam", 8, 8);
x_68 = l_Lean_Name_mkStr1(x_67);
x_69 = l_Lean_Expr_isAppOf(x_50, x_68);
lean_dec(x_68);
lean_dec(x_50);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_array_fget(x_59, x_16);
lean_dec(x_16);
lean_dec(x_59);
x_71 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(x_1, x_2, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_72 = lean_box(x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_61);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_51);
return x_75;
}
else
{
lean_object* x_76; 
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_14);
lean_ctor_set(x_76, 1, x_61);
x_52 = x_76;
goto block_57;
}
}
else
{
lean_dec(x_59);
lean_dec(x_16);
goto block_63;
}
}
else
{
lean_dec(x_59);
lean_dec(x_50);
lean_dec(x_16);
goto block_63;
}
block_57:
{
lean_object* x_53; size_t x_54; size_t x_55; 
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_usize_of_nat(x_53);
x_55 = lean_usize_add(x_5, x_54);
x_5 = x_55;
x_6 = x_52;
x_11 = x_51;
goto _start;
}
block_63:
{
lean_object* x_62; 
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_61);
x_52 = x_62;
goto block_57;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_77 = !lean_is_exclusive(x_22);
if (x_77 == 0)
{
return x_22;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_22, 0);
x_79 = lean_ctor_get(x_22, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_22);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_5, x_4);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_6);
x_14 = lean_array_uget(x_3, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_15 = lean_infer_type(x_14, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = lean_box(0);
x_20 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(x_1, x_2, x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = lean_box(x_20);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_15, 0, x_23);
return x_15;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_free_object(x_15);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_19);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_5, x_27);
x_5 = x_28;
x_6 = x_25;
x_11 = x_18;
goto _start;
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = lean_box(0);
x_33 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(x_1, x_2, x_30);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_34 = lean_box(x_33);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_34);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_32);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_31);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; 
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_32);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_usize_of_nat(x_40);
x_42 = lean_usize_add(x_5, x_41);
x_5 = x_42;
x_6 = x_39;
x_11 = x_31;
goto _start;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_1);
x_14 = l_Array_toSubarray___redArg(x_1, x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_size(x_5);
x_17 = lean_usize_of_nat(x_12);
x_18 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__0(x_3, x_4, x_5, x_16, x_17, x_15, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_box(1);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_box(1);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_18);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_18, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_20, 0);
lean_inc(x_29);
lean_dec(x_20);
lean_ctor_set(x_18, 0, x_29);
return x_18;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_dec(x_18);
x_31 = lean_ctor_get(x_20, 0);
lean_inc(x_31);
lean_dec(x_20);
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
x_33 = !lean_is_exclusive(x_18);
if (x_33 == 0)
{
return x_18;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_18, 0);
x_35 = lean_ctor_get(x_18, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_18);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
lean_dec(x_7);
x_5 = x_13;
x_6 = x_15;
x_7 = x_17;
goto _start;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; 
lean_dec(x_7);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_size(x_3);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_25 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__1(x_1, x_2, x_3, x_22, x_24, x_21, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = lean_infer_type(x_5, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___lam__0___boxed), 11, 4);
lean_closure_set(x_32, 0, x_6);
lean_closure_set(x_32, 1, x_19);
lean_closure_set(x_32, 2, x_1);
lean_closure_set(x_32, 3, x_2);
x_33 = l_Lean_Expr_getAppNumArgs(x_4);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_30, x_34, x_32, x_36, x_8, x_9, x_10, x_11, x_31);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_25, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_44);
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_ctor_get(x_27, 0);
lean_inc(x_46);
lean_dec(x_27);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_5) == 5)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_5, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_dec(x_5);
x_15 = lean_array_set(x_6, x_7, x_14);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_sub(x_7, x_16);
x_18 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2(x_1, x_2, x_3, x_4, x_13, x_15, x_17, x_8, x_9, x_10, x_11, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; lean_object* x_23; size_t x_24; lean_object* x_25; 
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_array_size(x_3);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_usize_of_nat(x_23);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_25 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__1(x_1, x_2, x_3, x_22, x_24, x_21, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_29 = lean_infer_type(x_5, x_8, x_9, x_10, x_11, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_29, 1);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_alloc_closure((void*)(l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___lam__0___boxed), 11, 4);
lean_closure_set(x_32, 0, x_6);
lean_closure_set(x_32, 1, x_19);
lean_closure_set(x_32, 2, x_1);
lean_closure_set(x_32, 3, x_2);
x_33 = l_Lean_Expr_getAppNumArgs(x_4);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
x_37 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_30, x_34, x_32, x_36, x_8, x_9, x_10, x_11, x_31);
return x_37;
}
else
{
uint8_t x_38; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_29);
if (x_38 == 0)
{
return x_29;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_29, 0);
x_40 = lean_ctor_get(x_29, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_29);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_25);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_25, 0);
lean_dec(x_43);
x_44 = lean_ctor_get(x_27, 0);
lean_inc(x_44);
lean_dec(x_27);
lean_ctor_set(x_25, 0, x_44);
return x_25;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_ctor_get(x_27, 0);
lean_inc(x_46);
lean_dec(x_27);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_48 = !lean_is_exclusive(x_25);
if (x_48 == 0)
{
return x_25;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_25, 0);
x_50 = lean_ctor_get(x_25, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_25);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_box(0);
x_11 = l_Lean_Expr_sort___override(x_10);
x_12 = l_Lean_Expr_getAppNumArgs(x_4);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc(x_4);
x_16 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2(x_1, x_2, x_3, x_4, x_4, x_13, x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_15);
lean_dec(x_4);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized___lam__0___boxed), 9, 2);
lean_closure_set(x_9, 0, x_1);
lean_closure_set(x_9, 1, x_2);
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_3, x_9, x_11, x_4, x_5, x_6, x_7, x_8);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__0(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__1(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Expr_withAppAux___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
x_5 = l_List_reverse___redArg(x_4);
return x_5;
}
else
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = lean_ctor_get(x_3, 1);
x_9 = l_Lean_instInhabitedExpr;
x_10 = lean_nat_sub(x_1, x_7);
lean_dec(x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_10, x_11);
lean_dec(x_10);
x_13 = lean_array_get(x_9, x_2, x_12);
lean_dec(x_12);
x_14 = l_Lean_Expr_fvarId_x21(x_13);
lean_dec(x_13);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_14);
{
lean_object* _tmp_2 = x_8;
lean_object* _tmp_3 = x_3;
x_3 = _tmp_2;
x_4 = _tmp_3;
}
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_3);
x_18 = l_Lean_instInhabitedExpr;
x_19 = lean_nat_sub(x_1, x_16);
lean_dec(x_16);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_nat_sub(x_19, x_20);
lean_dec(x_19);
x_22 = lean_array_get(x_18, x_2, x_21);
lean_dec(x_21);
x_23 = l_Lean_Expr_fvarId_x21(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_4);
x_3 = x_17;
x_4 = x_24;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Expr_fvarId_x21(x_5);
lean_dec(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Expr_fvarId_x21(x_9);
lean_dec(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_ofList___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__2(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = l_Lean_RBTree_ofList___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__2(x_4);
x_6 = lean_box(0);
x_7 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0(lean_box(0), x_5, x_3, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_5, x_6);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_4, x_5);
x_16 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_2, 0);
x_18 = lean_nat_dec_eq(x_17, x_3);
if (x_18 == 0)
{
lean_dec(x_15);
x_8 = x_7;
goto block_13;
}
else
{
lean_object* x_19; 
x_19 = l_Lean_FVarIdSet_insert(x_7, x_15);
x_8 = x_19;
goto block_13;
}
}
else
{
lean_object* x_20; 
lean_dec(x_16);
x_20 = l_Lean_FVarIdSet_insert(x_7, x_15);
x_8 = x_20;
goto block_13;
}
}
else
{
return x_7;
}
block_13:
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_5, x_10);
x_5 = x_11;
x_7 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_10; 
lean_dec(x_6);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_4, 0);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_14 = l_Lean_FVarId_getType___redArg(x_12, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(8u);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_unsigned_to_nat(2u);
x_20 = lean_nat_shiftl(x_17, x_19);
x_21 = lean_unsigned_to_nat(3u);
x_22 = lean_nat_div(x_20, x_21);
lean_dec(x_20);
x_23 = l_Nat_nextPowerOfTwo(x_22);
lean_dec(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_array(x_23, x_24);
lean_ctor_set_tag(x_4, 0);
lean_ctor_set(x_4, 1, x_25);
lean_ctor_set(x_4, 0, x_18);
x_26 = lean_box(0);
x_27 = lean_mk_empty_array_with_capacity(x_18);
x_28 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_28, 2, x_27);
x_29 = l_Lean_CollectFVars_main(x_15, x_28);
x_30 = lean_ctor_get(x_29, 2);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_array_get_size(x_30);
x_32 = lean_nat_dec_lt(x_18, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
x_4 = x_13;
x_9 = x_16;
goto _start;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_31, x_31);
if (x_34 == 0)
{
lean_dec(x_31);
lean_dec(x_30);
x_4 = x_13;
x_9 = x_16;
goto _start;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_usize_of_nat(x_18);
x_37 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_38 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(x_1, x_2, x_3, x_30, x_36, x_37, x_5);
lean_dec(x_30);
x_4 = x_13;
x_5 = x_38;
x_9 = x_16;
goto _start;
}
}
}
else
{
uint8_t x_40; 
lean_free_object(x_4);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
x_40 = !lean_is_exclusive(x_14);
if (x_40 == 0)
{
return x_14;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_14, 0);
x_42 = lean_ctor_get(x_14, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_14);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_4, 0);
x_45 = lean_ctor_get(x_4, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_4);
lean_inc(x_6);
x_46 = l_Lean_FVarId_getType___redArg(x_44, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_46, 1);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_unsigned_to_nat(8u);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_49, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = l_Nat_nextPowerOfTwo(x_54);
lean_dec(x_54);
x_56 = lean_box(0);
x_57 = lean_mk_array(x_55, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_box(0);
x_60 = lean_mk_empty_array_with_capacity(x_50);
x_61 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
lean_ctor_set(x_61, 2, x_60);
x_62 = l_Lean_CollectFVars_main(x_47, x_61);
x_63 = lean_ctor_get(x_62, 2);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_array_get_size(x_63);
x_65 = lean_nat_dec_lt(x_50, x_64);
if (x_65 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
x_4 = x_45;
x_9 = x_48;
goto _start;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_64, x_64);
if (x_67 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
x_4 = x_45;
x_9 = x_48;
goto _start;
}
else
{
size_t x_69; size_t x_70; lean_object* x_71; 
x_69 = lean_usize_of_nat(x_50);
x_70 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_71 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(x_1, x_2, x_3, x_63, x_69, x_70, x_5);
lean_dec(x_63);
x_4 = x_45;
x_5 = x_71;
x_9 = x_48;
goto _start;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_45);
lean_dec(x_6);
lean_dec(x_5);
x_73 = lean_ctor_get(x_46, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_46, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 lean_ctor_release(x_46, 1);
 x_75 = x_46;
} else {
 lean_dec_ref(x_46);
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
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_5, x_6, x_8, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_12; 
lean_dec(x_7);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_16 = l_Lean_FVarId_getType___redArg(x_14, x_7, x_9, x_10, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(8u);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_unsigned_to_nat(2u);
x_22 = lean_nat_shiftl(x_19, x_21);
x_23 = lean_unsigned_to_nat(3u);
x_24 = lean_nat_div(x_22, x_23);
lean_dec(x_22);
x_25 = l_Nat_nextPowerOfTwo(x_24);
lean_dec(x_24);
x_26 = lean_box(0);
x_27 = lean_mk_array(x_25, x_26);
lean_ctor_set_tag(x_5, 0);
lean_ctor_set(x_5, 1, x_27);
lean_ctor_set(x_5, 0, x_20);
x_28 = lean_box(0);
x_29 = lean_mk_empty_array_with_capacity(x_20);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_5);
lean_ctor_set(x_30, 1, x_28);
lean_ctor_set(x_30, 2, x_29);
x_31 = l_Lean_CollectFVars_main(x_17, x_30);
x_32 = lean_ctor_get(x_31, 2);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_array_get_size(x_32);
x_34 = lean_nat_dec_lt(x_20, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_33);
lean_dec(x_32);
x_35 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_15, x_6, x_7, x_9, x_10, x_18);
return x_35;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
lean_object* x_37; 
lean_dec(x_33);
lean_dec(x_32);
x_37 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_15, x_6, x_7, x_9, x_10, x_18);
return x_37;
}
else
{
size_t x_38; size_t x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_usize_of_nat(x_20);
x_39 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_40 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(x_1, x_2, x_3, x_32, x_38, x_39, x_6);
lean_dec(x_32);
x_41 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_15, x_40, x_7, x_9, x_10, x_18);
return x_41;
}
}
}
else
{
uint8_t x_42; 
lean_free_object(x_5);
lean_dec(x_15);
lean_dec(x_7);
lean_dec(x_6);
x_42 = !lean_is_exclusive(x_16);
if (x_42 == 0)
{
return x_16;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_16, 0);
x_44 = lean_ctor_get(x_16, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_16);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_5, 0);
x_47 = lean_ctor_get(x_5, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_5);
lean_inc(x_7);
x_48 = l_Lean_FVarId_getType___redArg(x_46, x_7, x_9, x_10, x_11);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unsigned_to_nat(8u);
x_52 = lean_unsigned_to_nat(0u);
x_53 = lean_unsigned_to_nat(2u);
x_54 = lean_nat_shiftl(x_51, x_53);
x_55 = lean_unsigned_to_nat(3u);
x_56 = lean_nat_div(x_54, x_55);
lean_dec(x_54);
x_57 = l_Nat_nextPowerOfTwo(x_56);
lean_dec(x_56);
x_58 = lean_box(0);
x_59 = lean_mk_array(x_57, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_52);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_box(0);
x_62 = lean_mk_empty_array_with_capacity(x_52);
x_63 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_61);
lean_ctor_set(x_63, 2, x_62);
x_64 = l_Lean_CollectFVars_main(x_49, x_63);
x_65 = lean_ctor_get(x_64, 2);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_array_get_size(x_65);
x_67 = lean_nat_dec_lt(x_52, x_66);
if (x_67 == 0)
{
lean_object* x_68; 
lean_dec(x_66);
lean_dec(x_65);
x_68 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_47, x_6, x_7, x_9, x_10, x_50);
return x_68;
}
else
{
uint8_t x_69; 
x_69 = lean_nat_dec_le(x_66, x_66);
if (x_69 == 0)
{
lean_object* x_70; 
lean_dec(x_66);
lean_dec(x_65);
x_70 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_47, x_6, x_7, x_9, x_10, x_50);
return x_70;
}
else
{
size_t x_71; size_t x_72; lean_object* x_73; lean_object* x_74; 
x_71 = lean_usize_of_nat(x_52);
x_72 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_73 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(x_1, x_2, x_3, x_65, x_71, x_72, x_6);
lean_dec(x_65);
x_74 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_47, x_73, x_7, x_9, x_10, x_50);
return x_74;
}
}
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
lean_dec(x_47);
lean_dec(x_7);
lean_dec(x_6);
x_75 = lean_ctor_get(x_48, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_48, 1);
lean_inc(x_76);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_77 = x_48;
} else {
 lean_dec_ref(x_48);
 x_77 = lean_box(0);
}
if (lean_is_scalar(x_77)) {
 x_78 = lean_alloc_ctor(1, 2, 0);
} else {
 x_78 = x_77;
}
lean_ctor_set(x_78, 0, x_75);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_6 = lean_unsigned_to_nat(8u);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_unsigned_to_nat(2u);
x_9 = lean_nat_shiftl(x_6, x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = lean_nat_div(x_9, x_10);
lean_dec(x_9);
x_12 = l_Nat_nextPowerOfTwo(x_11);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_mk_array(x_12, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_box(0);
x_17 = lean_mk_empty_array_with_capacity(x_7);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_16);
lean_ctor_set(x_18, 2, x_17);
x_19 = l_Lean_CollectFVars_main(x_5, x_18);
x_20 = lean_ctor_get(x_19, 2);
lean_inc(x_20);
lean_dec(x_19);
x_21 = lean_array_get_size(x_20);
x_22 = lean_nat_dec_lt(x_7, x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_4;
}
else
{
uint8_t x_23; 
x_23 = lean_nat_dec_le(x_21, x_21);
if (x_23 == 0)
{
lean_dec(x_21);
lean_dec(x_20);
return x_4;
}
else
{
size_t x_24; size_t x_25; lean_object* x_26; 
x_24 = lean_usize_of_nat(x_7);
x_25 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_26 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(x_1, x_2, x_3, x_20, x_24, x_25, x_4);
lean_dec(x_20);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_7, x_6);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_87; lean_object* x_99; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_nat_dec_eq(x_23, x_3);
x_25 = lean_array_uget(x_5, x_7);
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_fvarId_x21(x_25);
x_99 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_29, x_30);
if (lean_obj_tag(x_99) == 0)
{
x_87 = x_24;
goto block_98;
}
else
{
lean_dec(x_99);
x_87 = x_4;
goto block_98;
}
block_49:
{
lean_object* x_33; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_32);
lean_inc(x_26);
lean_inc(x_1);
x_33 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized(x_1, x_26, x_32, x_9, x_10, x_11, x_12, x_31);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_30);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
x_14 = x_38;
x_15 = x_36;
goto block_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_28);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
lean_inc(x_30);
x_40 = l_Lean_FVarIdSet_insert(x_26, x_30);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0(x_1, x_2, x_3, x_40, x_32);
x_42 = l_Lean_FVarIdSet_insert(x_29, x_30);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_14 = x_44;
x_15 = x_39;
goto block_20;
}
}
else
{
uint8_t x_45; 
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_86:
{
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_51);
x_53 = l_Lean_Meta_isProp(x_51, x_9, x_10, x_11, x_12, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_inc(x_9);
lean_inc(x_30);
x_57 = l_Lean_FVarId_getDecl___redArg(x_30, x_9, x_11, x_12, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_LocalDecl_binderInfo(x_58);
lean_dec(x_58);
x_61 = lean_box(x_60);
if (lean_obj_tag(x_61) == 3)
{
x_31 = x_59;
x_32 = x_51;
goto block_49;
}
else
{
lean_dec(x_61);
if (x_24 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_30);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_28);
lean_ctor_set(x_62, 1, x_29);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_62);
x_14 = x_63;
x_15 = x_59;
goto block_20;
}
else
{
x_31 = x_59;
x_32 = x_51;
goto block_49;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_51);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_dec(x_53);
x_69 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(x_1, x_26, x_51);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_30);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_28);
lean_ctor_set(x_70, 1, x_29);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_26);
lean_ctor_set(x_71, 1, x_70);
x_14 = x_71;
x_15 = x_68;
goto block_20;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_28);
lean_inc(x_30);
x_72 = l_Lean_FVarIdSet_insert(x_26, x_30);
x_73 = l_Lean_FVarIdSet_insert(x_29, x_30);
x_74 = lean_box(x_69);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_14 = x_76;
x_15 = x_68;
goto block_20;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_51);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_53);
if (x_77 == 0)
{
return x_53;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_53, 0);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_53);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_28);
x_81 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0(x_1, x_2, x_3, x_26, x_51);
x_82 = l_Lean_FVarIdSet_insert(x_29, x_30);
x_83 = lean_box(x_52);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_14 = x_85;
x_15 = x_50;
goto block_20;
}
}
block_98:
{
if (x_87 == 0)
{
lean_object* x_88; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_88 = lean_infer_type(x_25, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_26, x_30);
if (lean_obj_tag(x_91) == 0)
{
x_50 = x_90;
x_51 = x_89;
x_52 = x_24;
goto block_86;
}
else
{
lean_dec(x_91);
x_50 = x_90;
x_51 = x_89;
x_52 = x_4;
goto block_86;
}
}
else
{
uint8_t x_92; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_30);
lean_dec(x_25);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_28);
lean_ctor_set(x_96, 1, x_29);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_26);
lean_ctor_set(x_97, 1, x_96);
x_14 = x_97;
x_15 = x_13;
goto block_20;
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_7, x_17);
x_7 = x_18;
x_8 = x_14;
x_13 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, size_t x_6, size_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_7, x_6);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_8);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_87; lean_object* x_99; 
x_23 = lean_ctor_get(x_2, 0);
x_24 = lean_nat_dec_eq(x_23, x_3);
x_25 = lean_array_uget(x_5, x_7);
x_26 = lean_ctor_get(x_8, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_8, 1);
lean_inc(x_27);
lean_dec(x_8);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = l_Lean_Expr_fvarId_x21(x_25);
x_99 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_29, x_30);
if (lean_obj_tag(x_99) == 0)
{
x_87 = x_24;
goto block_98;
}
else
{
lean_dec(x_99);
x_87 = x_4;
goto block_98;
}
block_49:
{
lean_object* x_33; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_31);
lean_inc(x_26);
lean_inc(x_1);
x_33 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_canBeSynthesized(x_1, x_26, x_31, x_9, x_10, x_11, x_12, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; uint8_t x_35; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_unbox(x_34);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_34);
lean_dec(x_31);
lean_dec(x_30);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_28);
lean_ctor_set(x_37, 1, x_29);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_26);
lean_ctor_set(x_38, 1, x_37);
x_14 = x_38;
x_15 = x_36;
goto block_20;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_28);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
lean_inc(x_30);
x_40 = l_Lean_FVarIdSet_insert(x_26, x_30);
x_41 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0(x_1, x_2, x_3, x_40, x_31);
x_42 = l_Lean_FVarIdSet_insert(x_29, x_30);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_43);
x_14 = x_44;
x_15 = x_39;
goto block_20;
}
}
else
{
uint8_t x_45; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_33);
if (x_45 == 0)
{
return x_33;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_33, 0);
x_47 = lean_ctor_get(x_33, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_33);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
block_86:
{
if (x_52 == 0)
{
lean_object* x_53; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_51);
x_53 = l_Lean_Meta_isProp(x_51, x_9, x_10, x_11, x_12, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_unbox(x_54);
lean_dec(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_53, 1);
lean_inc(x_56);
lean_dec(x_53);
lean_inc(x_9);
lean_inc(x_30);
x_57 = l_Lean_FVarId_getDecl___redArg(x_30, x_9, x_11, x_12, x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = l_Lean_LocalDecl_binderInfo(x_58);
lean_dec(x_58);
x_61 = lean_box(x_60);
if (lean_obj_tag(x_61) == 3)
{
x_31 = x_51;
x_32 = x_59;
goto block_49;
}
else
{
lean_dec(x_61);
if (x_24 == 0)
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_51);
lean_dec(x_30);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_28);
lean_ctor_set(x_62, 1, x_29);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_26);
lean_ctor_set(x_63, 1, x_62);
x_14 = x_63;
x_15 = x_59;
goto block_20;
}
else
{
x_31 = x_51;
x_32 = x_59;
goto block_49;
}
}
}
else
{
uint8_t x_64; 
lean_dec(x_51);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_57);
if (x_64 == 0)
{
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
else
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_ctor_get(x_53, 1);
lean_inc(x_68);
lean_dec(x_53);
x_69 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkTypeFVars(x_1, x_26, x_51);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_30);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_28);
lean_ctor_set(x_70, 1, x_29);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_26);
lean_ctor_set(x_71, 1, x_70);
x_14 = x_71;
x_15 = x_68;
goto block_20;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_28);
lean_inc(x_30);
x_72 = l_Lean_FVarIdSet_insert(x_26, x_30);
x_73 = l_Lean_FVarIdSet_insert(x_29, x_30);
x_74 = lean_box(x_69);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_72);
lean_ctor_set(x_76, 1, x_75);
x_14 = x_76;
x_15 = x_68;
goto block_20;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_51);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_53);
if (x_77 == 0)
{
return x_53;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_53, 0);
x_79 = lean_ctor_get(x_53, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_53);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_28);
x_81 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0(x_1, x_2, x_3, x_26, x_51);
x_82 = l_Lean_FVarIdSet_insert(x_29, x_30);
x_83 = lean_box(x_52);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_81);
lean_ctor_set(x_85, 1, x_84);
x_14 = x_85;
x_15 = x_50;
goto block_20;
}
}
block_98:
{
if (x_87 == 0)
{
lean_object* x_88; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
x_88 = lean_infer_type(x_25, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_88, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_88, 1);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_26, x_30);
if (lean_obj_tag(x_91) == 0)
{
x_50 = x_90;
x_51 = x_89;
x_52 = x_24;
goto block_86;
}
else
{
lean_dec(x_91);
x_50 = x_90;
x_51 = x_89;
x_52 = x_4;
goto block_86;
}
}
else
{
uint8_t x_92; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_88);
if (x_92 == 0)
{
return x_88;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_88, 0);
x_94 = lean_ctor_get(x_88, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_88);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_30);
lean_dec(x_25);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_28);
lean_ctor_set(x_96, 1, x_29);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_26);
lean_ctor_set(x_97, 1, x_96);
x_14 = x_97;
x_15 = x_13;
goto block_20;
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_7, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_18, x_14, x_9, x_10, x_11, x_12, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; size_t x_23; lean_object* x_24; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_nat_dec_eq(x_12, x_2);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
lean_dec(x_6);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_box(x_13);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_array_size(x_3);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_usize_of_nat(x_22);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_24 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6(x_4, x_1, x_2, x_5, x_3, x_21, x_23, x_20, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_24, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_28 = x_24;
} else {
 lean_dec_ref(x_24);
 x_28 = lean_box(0);
}
x_29 = lean_ctor_get(x_25, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_31 = x_26;
} else {
 lean_dec_ref(x_26);
 x_31 = lean_box(0);
}
x_32 = l_Lean_RBMap_size___redArg(x_29);
lean_dec(x_29);
x_33 = lean_nat_dec_eq(x_32, x_2);
lean_dec(x_32);
if (x_33 == 0)
{
lean_object* x_34; uint8_t x_35; uint8_t x_41; 
x_34 = lean_box(0);
x_41 = lean_unbox(x_30);
lean_dec(x_30);
if (x_41 == 0)
{
x_35 = x_5;
goto block_40;
}
else
{
x_35 = x_13;
goto block_40;
}
block_40:
{
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_28);
if (lean_is_scalar(x_31)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_31;
}
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_25);
x_6 = x_36;
x_11 = x_27;
goto _start;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
if (lean_is_scalar(x_31)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_31;
}
lean_ctor_set(x_38, 0, x_34);
lean_ctor_set(x_38, 1, x_25);
if (lean_is_scalar(x_28)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_28;
}
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
return x_39;
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_30);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_42);
if (lean_is_scalar(x_31)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_31;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
if (lean_is_scalar(x_28)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_28;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_27);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_46 = !lean_is_exclusive(x_24);
if (x_46 == 0)
{
return x_24;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_24, 0);
x_48 = lean_ctor_get(x_24, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_24);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_16; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_6, 1);
x_20 = lean_nat_dec_lt(x_8, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_7);
lean_ctor_set(x_21, 1, x_9);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_array_fget(x_1, x_8);
x_23 = l_Lean_Expr_fvarId_x21(x_22);
lean_dec(x_22);
x_24 = l_Lean_RBNode_findCore___at___Lean_Meta_Closure_process_spec__0___redArg(x_2, x_23);
lean_dec(x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_3, 0);
x_26 = lean_nat_dec_eq(x_25, x_4);
x_16 = x_26;
goto block_18;
}
else
{
lean_dec(x_24);
x_16 = x_5;
goto block_18;
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_6, 2);
x_13 = lean_nat_add(x_8, x_12);
lean_dec(x_8);
x_7 = x_10;
x_8 = x_13;
x_9 = x_11;
goto _start;
}
block_18:
{
if (x_16 == 0)
{
lean_object* x_17; 
lean_inc(x_8);
x_17 = lean_array_push(x_7, x_8);
x_10 = x_17;
x_11 = x_9;
goto block_15;
}
else
{
x_10 = x_7;
x_11 = x_9;
goto block_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__11(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_inc(x_1);
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__11(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__12(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_sub(x_2, x_7);
x_9 = lean_array_uget(x_1, x_8);
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__11(x_4, x_9);
lean_dec(x_9);
lean_dec(x_4);
x_2 = x_8;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_array_get_size(x_4);
x_12 = lean_nat_dec_eq(x_1, x_11);
if (x_12 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_11);
lean_dec(x_4);
x_103 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.EMatchTheorem", 36, 36);
x_104 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Grind.EMatchTheorem.0.Lean.Meta.Grind.checkCoverage", 77, 77);
x_105 = lean_unsigned_to_nat(521u);
x_106 = lean_unsigned_to_nat(4u);
x_107 = lean_mk_string_unchecked("assertion violation: numParams == xs.size\n    ", 46, 46);
x_108 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_103, x_104, x_105, x_106, x_107);
lean_dec(x_107);
lean_dec(x_104);
lean_dec(x_103);
x_109 = l_panic___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__10(x_108, x_6, x_7, x_8, x_9, x_10);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
x_110 = lean_box(0);
x_111 = lean_ctor_get(x_2, 1);
x_112 = lean_array_get_size(x_111);
x_113 = lean_unsigned_to_nat(0u);
x_114 = lean_nat_dec_lt(x_113, x_112);
if (x_114 == 0)
{
lean_dec(x_112);
x_13 = x_110;
goto block_102;
}
else
{
size_t x_115; size_t x_116; lean_object* x_117; 
x_115 = lean_usize_of_nat(x_112);
lean_dec(x_112);
x_116 = lean_usize_of_nat(x_113);
x_117 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__12(x_111, x_115, x_116, x_110);
x_13 = x_117;
goto block_102;
}
}
block_102:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_14 = lean_box(0);
x_15 = l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__0(x_1, x_4, x_13, x_14);
lean_inc(x_4);
x_16 = lean_array_to_list(x_4);
x_17 = l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__1(x_16, x_14);
x_18 = l_Lean_RBTree_ofList___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__2(x_17);
lean_inc(x_15);
x_19 = l_Lean_RBTree_ofList___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__2(x_15);
lean_inc(x_6);
lean_inc(x_19);
lean_inc(x_15);
x_20 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___redArg(x_18, x_2, x_1, x_15, x_15, x_19, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_15);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = l_Lean_RBMap_size___redArg(x_22);
x_25 = lean_nat_dec_eq(x_24, x_1);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_free_object(x_20);
x_26 = lean_box(0);
x_27 = lean_box(x_3);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_19);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_22);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_29);
x_31 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__8(x_2, x_1, x_4, x_18, x_12, x_30, x_6, x_7, x_8, x_9, x_23);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 0);
lean_inc(x_34);
lean_dec(x_32);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_ctor_get(x_33, 0);
lean_inc(x_36);
lean_dec(x_33);
x_37 = lean_unsigned_to_nat(0u);
x_38 = lean_mk_empty_array_with_capacity(x_37);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_11);
lean_ctor_set(x_40, 2, x_39);
x_41 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg(x_4, x_36, x_2, x_1, x_12, x_40, x_38, x_37, x_35);
lean_dec(x_40);
lean_dec(x_36);
lean_dec(x_4);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_41, 0);
x_44 = lean_array_to_list(x_43);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_41, 0);
x_47 = lean_ctor_get(x_41, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_41);
x_48 = lean_array_to_list(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
uint8_t x_51; 
lean_dec(x_33);
lean_dec(x_11);
lean_dec(x_4);
x_51 = !lean_is_exclusive(x_31);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_31, 0);
lean_dec(x_52);
x_53 = lean_ctor_get(x_34, 0);
lean_inc(x_53);
lean_dec(x_34);
lean_ctor_set(x_31, 0, x_53);
return x_31;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_31, 1);
lean_inc(x_54);
lean_dec(x_31);
x_55 = lean_ctor_get(x_34, 0);
lean_inc(x_55);
lean_dec(x_34);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_54);
return x_56;
}
}
}
else
{
uint8_t x_57; 
lean_dec(x_11);
lean_dec(x_4);
x_57 = !lean_is_exclusive(x_31);
if (x_57 == 0)
{
return x_31;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_31, 0);
x_59 = lean_ctor_get(x_31, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_31);
x_60 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
return x_60;
}
}
}
else
{
lean_object* x_61; 
lean_dec(x_22);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_61 = lean_box(0);
lean_ctor_set(x_20, 0, x_61);
return x_20;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_20, 0);
x_63 = lean_ctor_get(x_20, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_20);
x_64 = l_Lean_RBMap_size___redArg(x_62);
x_65 = lean_nat_dec_eq(x_64, x_1);
lean_dec(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_66 = lean_box(0);
x_67 = lean_box(x_3);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_19);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_66);
lean_ctor_set(x_70, 1, x_69);
x_71 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__8(x_2, x_1, x_4, x_18, x_12, x_70, x_6, x_7, x_8, x_9, x_63);
if (lean_obj_tag(x_71) == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
if (lean_obj_tag(x_74) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_75 = lean_ctor_get(x_71, 1);
lean_inc(x_75);
lean_dec(x_71);
x_76 = lean_ctor_get(x_73, 0);
lean_inc(x_76);
lean_dec(x_73);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_mk_empty_array_with_capacity(x_77);
x_79 = lean_unsigned_to_nat(1u);
x_80 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_80, 0, x_77);
lean_ctor_set(x_80, 1, x_11);
lean_ctor_set(x_80, 2, x_79);
x_81 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg(x_4, x_76, x_2, x_1, x_12, x_80, x_78, x_77, x_75);
lean_dec(x_80);
lean_dec(x_76);
lean_dec(x_4);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_84 = x_81;
} else {
 lean_dec_ref(x_81);
 x_84 = lean_box(0);
}
x_85 = lean_array_to_list(x_82);
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
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
lean_dec(x_73);
lean_dec(x_11);
lean_dec(x_4);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_89 = x_71;
} else {
 lean_dec_ref(x_71);
 x_89 = lean_box(0);
}
x_90 = lean_ctor_get(x_74, 0);
lean_inc(x_90);
lean_dec(x_74);
if (lean_is_scalar(x_89)) {
 x_91 = lean_alloc_ctor(0, 2, 0);
} else {
 x_91 = x_89;
}
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_88);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_11);
lean_dec(x_4);
x_92 = lean_ctor_get(x_71, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_71, 1);
lean_inc(x_93);
if (lean_is_exclusive(x_71)) {
 lean_ctor_release(x_71, 0);
 lean_ctor_release(x_71, 1);
 x_94 = x_71;
} else {
 lean_dec_ref(x_71);
 x_94 = lean_box(0);
}
if (lean_is_scalar(x_94)) {
 x_95 = lean_alloc_ctor(1, 2, 0);
} else {
 x_95 = x_94;
}
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_93);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; 
lean_dec(x_62);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_96 = lean_box(0);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_63);
return x_97;
}
}
}
else
{
uint8_t x_98; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_98 = !lean_is_exclusive(x_20);
if (x_98 == 0)
{
return x_20;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_20, 0);
x_100 = lean_ctor_get(x_20, 1);
lean_inc(x_100);
lean_inc(x_99);
lean_dec(x_20);
x_101 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
return x_101;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_ctor_get(x_3, 0);
lean_inc(x_9);
x_10 = lean_nat_dec_eq(x_9, x_2);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_11 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(x_10);
lean_inc(x_2);
x_15 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage___lam__0___boxed), 10, 3);
lean_closure_set(x_15, 0, x_2);
lean_closure_set(x_15, 1, x_3);
lean_closure_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_12, x_16, x_15, x_10, x_4, x_5, x_6, x_7, x_13);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_18 = !lean_is_exclusive(x_11);
if (x_18 == 0)
{
return x_11;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_11, 0);
x_20 = lean_ctor_get(x_11, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_11);
x_21 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_8);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_List_mapTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_10 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__3(x_1, x_2, x_3, x_4, x_8, x_9, x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6_spec__6(x_1, x_2, x_3, x_14, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = lean_unbox_usize(x_7);
lean_dec(x_7);
x_17 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__6(x_1, x_2, x_3, x_14, x_5, x_15, x_16, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Loop_forIn_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__8(x_1, x_2, x_3, x_4, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_5);
lean_dec(x_5);
x_11 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___redArg(x_1, x_2, x_3, x_4, x_10, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; lean_object* x_17; 
x_16 = lean_unbox(x_5);
lean_dec(x_5);
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__9(x_1, x_2, x_3, x_4, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__11___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__11(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage_spec__12(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage___lam__0(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_nat_dec_lt(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(x_5, x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
x_11 = x_23;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_53; 
x_24 = lean_mk_string_unchecked("", 0, 0);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_array_fget(x_2, x_5);
x_53 = lean_unbox(x_20);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_mk_string_unchecked("\n", 1, 1);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_unbox(x_20);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_58;
x_28 = x_57;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
goto block_52;
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_20);
x_59 = lean_box(0);
x_60 = lean_unbox(x_59);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_60;
x_28 = x_21;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
goto block_52;
}
block_52:
{
lean_object* x_34; 
lean_inc(x_26);
x_34 = lean_infer_type(x_26, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_MessageData_ofExpr(x_26);
lean_inc(x_25);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked(" : ", 3, 3);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_ofExpr(x_35);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(x_27);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_11 = x_47;
x_12 = x_36;
goto block_16;
}
else
{
uint8_t x_48; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_add(x_5, x_13);
lean_dec(x_5);
x_4 = x_11;
x_5 = x_14;
x_10 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_nat_dec_lt(x_5, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_4);
lean_ctor_set(x_19, 1, x_10);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_4, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_4, 1);
lean_inc(x_21);
lean_dec(x_4);
x_22 = l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(x_5, x_1);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_21);
x_11 = x_23;
x_12 = x_10;
goto block_16;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_53; 
x_24 = lean_mk_string_unchecked("", 0, 0);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_array_fget(x_2, x_5);
x_53 = lean_unbox(x_20);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_54 = lean_mk_string_unchecked("\n", 1, 1);
x_55 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_55, 0, x_54);
x_56 = l_Lean_MessageData_ofFormat(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_21);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_unbox(x_20);
lean_dec(x_20);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_58;
x_28 = x_57;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
goto block_52;
}
else
{
lean_object* x_59; uint8_t x_60; 
lean_dec(x_20);
x_59 = lean_box(0);
x_60 = lean_unbox(x_59);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_27 = x_60;
x_28 = x_21;
x_29 = x_6;
x_30 = x_7;
x_31 = x_8;
x_32 = x_9;
x_33 = x_10;
goto block_52;
}
block_52:
{
lean_object* x_34; 
lean_inc(x_26);
x_34 = lean_infer_type(x_26, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = l_Lean_MessageData_ofExpr(x_26);
lean_inc(x_25);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_25);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_mk_string_unchecked(" : ", 3, 3);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_MessageData_ofExpr(x_35);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_25);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_28);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(x_27);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
x_11 = x_47;
x_12 = x_36;
goto block_16;
}
else
{
uint8_t x_48; 
lean_dec(x_28);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_48 = !lean_is_exclusive(x_34);
if (x_48 == 0)
{
return x_34;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_34, 0);
x_50 = lean_ctor_get(x_34, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_34);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_nat_add(x_5, x_13);
x_15 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___redArg(x_1, x_2, x_3, x_11, x_14, x_6, x_7, x_8, x_9, x_12);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_mk_string_unchecked("", 0, 0);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = lean_box(1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_2);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_11);
lean_ctor_set(x_16, 1, x_10);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_17 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___redArg(x_1, x_2, x_15, x_16, x_12, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_20, x_4, x_5, x_6, x_7, x_19);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_9 = lean_infer_type(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt___lam__0___boxed), 8, 1);
lean_closure_set(x_12, 0, x_3);
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_2);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_Meta_forallBoundedTelescope___at___Lean_Meta_arrowDomainsN_spec__6(lean_box(0), x_10, x_13, x_12, x_15, x_4, x_5, x_6, x_7, x_11);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
return x_9;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 0);
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_9);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_1, 0);
x_6 = lean_ctor_get(x_1, 1);
x_7 = l_Lean_Meta_Grind_ppPattern(x_5);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_7);
{
lean_object* _tmp_0 = x_6;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_1);
x_11 = l_Lean_Meta_Grind_ppPattern(x_9);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_2);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; 
x_3 = l_List_reverse___redArg(x_2);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_ctor_get(x_1, 1);
lean_ctor_set(x_1, 1, x_2);
{
lean_object* _tmp_0 = x_5;
lean_object* _tmp_1 = x_1;
x_1 = _tmp_0;
x_2 = _tmp_1;
}
goto _start;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get(x_1, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_1);
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_2);
x_1 = x_8;
x_2 = x_9;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1(x_7, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = l_Lean_MessageData_ofConst(x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
x_13 = lean_ctor_get(x_8, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_8);
x_14 = l_Lean_MessageData_ofConst(x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_13);
return x_15;
}
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
return x_8;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_8);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
case 1:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
lean_dec(x_1);
x_21 = l_Lean_Expr_fvar___override(x_20);
x_22 = l_Lean_MessageData_ofExpr(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_6);
return x_23;
}
case 2:
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_1);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_1, 1);
x_26 = lean_ctor_get(x_1, 0);
lean_dec(x_26);
x_27 = l_Lean_MessageData_ofSyntax(x_25);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_6);
lean_ctor_set(x_1, 0, x_27);
return x_1;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_1, 1);
lean_inc(x_28);
lean_dec(x_1);
x_29 = l_Lean_MessageData_ofSyntax(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_6);
return x_30;
}
}
default: 
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_1, 0);
lean_inc(x_31);
lean_dec(x_1);
x_32 = l_Lean_MessageData_ofName(x_31);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_6);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_12 = l_Lean_Meta_Grind_NormalizePattern_main(x_5, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_82; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_dec(x_12);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 lean_ctor_release(x_13, 1);
 x_17 = x_13;
} else {
 lean_dec_ref(x_13);
 x_17 = lean_box(0);
}
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_20 = x_14;
} else {
 lean_dec_ref(x_14);
 x_20 = lean_box(0);
}
x_82 = l_List_isEmpty___redArg(x_18);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_83 = lean_mk_string_unchecked("grind", 5, 5);
x_84 = lean_mk_string_unchecked("ematch", 6, 6);
x_85 = lean_mk_string_unchecked("pattern", 7, 7);
x_86 = l_Lean_Name_mkStr3(x_83, x_84, x_85);
lean_inc(x_86);
x_87 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_86, x_7, x_8, x_9, x_10, x_15);
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_unbox(x_88);
lean_dec(x_88);
if (x_89 == 0)
{
lean_object* x_90; 
lean_dec(x_86);
x_90 = lean_ctor_get(x_87, 1);
lean_inc(x_90);
lean_dec(x_87);
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_90;
goto block_81;
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_87);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_92 = lean_ctor_get(x_87, 1);
x_93 = lean_ctor_get(x_87, 0);
lean_dec(x_93);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
lean_inc(x_4);
x_96 = l_Lean_MessageData_ofConst(x_4);
lean_inc(x_95);
lean_ctor_set_tag(x_87, 7);
lean_ctor_set(x_87, 1, x_96);
lean_ctor_set(x_87, 0, x_95);
x_97 = lean_mk_string_unchecked(": ", 2, 2);
x_98 = l_Lean_stringToMessageData(x_97);
lean_dec(x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_87);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_box(0);
lean_inc(x_16);
x_101 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(x_16, x_100);
x_102 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__1(x_101, x_100);
x_103 = l_Lean_MessageData_ofList(x_102);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_99);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_95);
x_106 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_86, x_105, x_7, x_8, x_9, x_10, x_92);
x_107 = lean_ctor_get(x_106, 1);
lean_inc(x_107);
lean_dec(x_106);
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_107;
goto block_81;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
x_108 = lean_ctor_get(x_87, 1);
lean_inc(x_108);
lean_dec(x_87);
x_109 = lean_mk_string_unchecked("", 0, 0);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
lean_inc(x_4);
x_111 = l_Lean_MessageData_ofConst(x_4);
lean_inc(x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_110);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_mk_string_unchecked(": ", 2, 2);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_box(0);
lean_inc(x_16);
x_117 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(x_16, x_116);
x_118 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__1(x_117, x_116);
x_119 = l_Lean_MessageData_ofList(x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_115);
lean_ctor_set(x_120, 1, x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_110);
x_122 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_86, x_121, x_7, x_8, x_9, x_10, x_108);
x_123 = lean_ctor_get(x_122, 1);
lean_inc(x_123);
lean_dec(x_122);
x_21 = x_7;
x_22 = x_8;
x_23 = x_9;
x_24 = x_10;
x_25 = x_123;
goto block_81;
}
}
}
else
{
lean_object* x_124; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_124 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_1, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = lean_mk_string_unchecked("invalid pattern for `", 21, 21);
x_128 = l_Lean_stringToMessageData(x_127);
lean_dec(x_127);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_125);
x_130 = lean_mk_string_unchecked("`", 1, 1);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_box(0);
x_134 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(x_16, x_133);
x_135 = l_Lean_MessageData_ofList(x_134);
x_136 = l_Lean_indentD(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_132);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_mk_string_unchecked("\nthe pattern does not contain constant symbols for indexing", 59, 59);
x_139 = l_Lean_stringToMessageData(x_138);
lean_dec(x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
x_141 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_140, x_7, x_8, x_9, x_10, x_126);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
return x_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_143 = lean_ctor_get(x_141, 0);
x_144 = lean_ctor_get(x_141, 1);
lean_inc(x_144);
lean_inc(x_143);
lean_dec(x_141);
x_145 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
return x_145;
}
}
else
{
uint8_t x_146; 
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_146 = !lean_is_exclusive(x_124);
if (x_146 == 0)
{
return x_124;
}
else
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_147 = lean_ctor_get(x_124, 0);
x_148 = lean_ctor_get(x_124, 1);
lean_inc(x_148);
lean_inc(x_147);
lean_dec(x_124);
x_149 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
return x_149;
}
}
}
block_81:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_3);
lean_inc(x_4);
x_26 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage(x_4, x_3, x_19, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_26, 0);
lean_dec(x_29);
x_30 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_30, 0, x_2);
lean_ctor_set(x_30, 1, x_4);
lean_ctor_set(x_30, 2, x_3);
lean_ctor_set(x_30, 3, x_16);
lean_ctor_set(x_30, 4, x_18);
lean_ctor_set(x_30, 5, x_1);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_6);
lean_ctor_set(x_26, 0, x_30);
return x_26;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec(x_26);
x_32 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_4);
lean_ctor_set(x_32, 2, x_3);
lean_ctor_set(x_32, 3, x_16);
lean_ctor_set(x_32, 4, x_18);
lean_ctor_set(x_32, 5, x_1);
lean_ctor_set_uint8(x_32, sizeof(void*)*6, x_6);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_18);
lean_dec(x_2);
x_34 = lean_ctor_get(x_26, 1);
lean_inc(x_34);
lean_dec(x_26);
x_35 = lean_ctor_get(x_27, 0);
lean_inc(x_35);
lean_dec(x_27);
x_36 = lean_box(0);
x_37 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(x_16, x_36);
x_38 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__1(x_37, x_36);
x_39 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_1, x_21, x_22, x_23, x_24, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_42 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ppParamsAt(x_4, x_3, x_35, x_21, x_22, x_23, x_24, x_41);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_mk_string_unchecked("", 0, 0);
x_46 = l_Lean_MessageData_ofList(x_38);
x_47 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
lean_inc(x_47);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(7, 2, 0);
} else {
 x_48 = x_20;
 lean_ctor_set_tag(x_48, 7);
}
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
lean_inc(x_47);
if (lean_is_scalar(x_17)) {
 x_49 = lean_alloc_ctor(7, 2, 0);
} else {
 x_49 = x_17;
 lean_ctor_set_tag(x_49, 7);
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
x_50 = lean_mk_string_unchecked("invalid pattern(s) for `", 24, 24);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_40);
x_53 = lean_mk_string_unchecked("`", 1, 1);
x_54 = l_Lean_stringToMessageData(x_53);
lean_dec(x_53);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_52);
lean_ctor_set(x_55, 1, x_54);
x_56 = l_Lean_indentD(x_49);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("\nthe following theorem parameters cannot be instantiated:", 57, 57);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_indentD(x_43);
x_62 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_47);
x_64 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_63, x_21, x_22, x_23, x_24, x_44);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_65 = !lean_is_exclusive(x_64);
if (x_65 == 0)
{
return x_64;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_64, 0);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_64);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
x_69 = !lean_is_exclusive(x_42);
if (x_69 == 0)
{
return x_42;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_42, 0);
x_71 = lean_ctor_get(x_42, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_42);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_4);
lean_dec(x_3);
x_73 = !lean_is_exclusive(x_39);
if (x_73 == 0)
{
return x_39;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_39, 0);
x_75 = lean_ctor_get(x_39, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_39);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_26);
if (x_77 == 0)
{
return x_26;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_26, 0);
x_79 = lean_ctor_get(x_26, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_26);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
}
else
{
uint8_t x_150; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_12);
if (x_150 == 0)
{
return x_12;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_12, 0);
x_152 = lean_ctor_get(x_12, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_12);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Meta_Grind_mkEMatchTheoremCore(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getProofFor(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_1);
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_18; uint8_t x_19; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
if (lean_is_exclusive(x_7)) {
 lean_ctor_release(x_7, 0);
 lean_ctor_release(x_7, 1);
 x_10 = x_7;
} else {
 lean_dec_ref(x_7);
 x_10 = lean_box(0);
}
x_18 = lean_st_ref_get(x_5, x_9);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
lean_inc(x_1);
x_23 = l_Lean_wasOriginallyTheorem(x_22, x_1);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = l_Lean_ConstantInfo_type(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_25 = l_Lean_Meta_isProp(x_24, x_2, x_3, x_4, x_5, x_21);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
lean_dec(x_10);
lean_dec(x_8);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_29 = lean_mk_string_unchecked("invalid E-matching theorem `", 28, 28);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_31);
lean_ctor_set(x_18, 0, x_30);
x_32 = lean_mk_string_unchecked("`, type is not a proposition", 28, 28);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_34, x_2, x_3, x_4, x_5, x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
return x_35;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_35);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
else
{
lean_object* x_40; 
lean_free_object(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_dec(x_25);
x_11 = x_40;
goto block_17;
}
}
else
{
uint8_t x_41; 
lean_free_object(x_18);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_free_object(x_18);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_21;
goto block_17;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_45 = lean_ctor_get(x_18, 0);
x_46 = lean_ctor_get(x_18, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_18);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
lean_dec(x_45);
lean_inc(x_1);
x_48 = l_Lean_wasOriginallyTheorem(x_47, x_1);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_ConstantInfo_type(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_50 = l_Lean_Meta_isProp(x_49, x_2, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_unbox(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_10);
lean_dec(x_8);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_dec(x_50);
x_54 = lean_mk_string_unchecked("invalid E-matching theorem `", 28, 28);
x_55 = l_Lean_stringToMessageData(x_54);
lean_dec(x_54);
x_56 = l_Lean_MessageData_ofName(x_1);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_mk_string_unchecked("`, type is not a proposition", 28, 28);
x_59 = l_Lean_stringToMessageData(x_58);
lean_dec(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_59);
x_61 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_60, x_2, x_3, x_4, x_5, x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 lean_ctor_release(x_61, 1);
 x_64 = x_61;
} else {
 lean_dec_ref(x_61);
 x_64 = lean_box(0);
}
if (lean_is_scalar(x_64)) {
 x_65 = lean_alloc_ctor(1, 2, 0);
} else {
 x_65 = x_64;
}
lean_ctor_set(x_65, 0, x_62);
lean_ctor_set(x_65, 1, x_63);
return x_65;
}
else
{
lean_object* x_66; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
lean_dec(x_50);
x_11 = x_66;
goto block_17;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = lean_ctor_get(x_50, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_50, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_69 = x_50;
} else {
 lean_dec_ref(x_50);
 x_69 = lean_box(0);
}
if (lean_is_scalar(x_69)) {
 x_70 = lean_alloc_ctor(1, 2, 0);
} else {
 x_70 = x_69;
}
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_68);
return x_70;
}
}
else
{
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_11 = x_46;
goto block_17;
}
}
block_17:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_ConstantInfo_levelParams(x_8);
lean_dec(x_8);
x_13 = lean_box(0);
x_14 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_mkSimpCongrTheorem_spec__1_spec__2(x_12, x_13);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
if (lean_is_scalar(x_10)) {
 x_16 = lean_alloc_ctor(0, 2, 0);
} else {
 x_16 = x_10;
}
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
else
{
uint8_t x_71; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_7);
if (x_71 == 0)
{
return x_7;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_7, 0);
x_73 = lean_ctor_get(x_7, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_7);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getProofFor(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_1);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_mk_empty_array_with_capacity(x_14);
x_16 = l_Lean_Meta_Grind_mkEMatchTheoremCore(x_13, x_15, x_2, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_Grind_mkEMatchTheorem(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_99; 
if (x_4 == 0)
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_5, 1);
lean_inc(x_153);
lean_dec(x_5);
x_99 = x_153;
goto block_152;
}
else
{
lean_object* x_154; 
x_154 = lean_ctor_get(x_5, 0);
lean_inc(x_154);
lean_dec(x_5);
x_99 = x_154;
goto block_152;
}
block_18:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_expr_abstract(x_11, x_1);
lean_dec(x_11);
x_14 = l_Lean_Meta_Grind_splitWhileForbidden(x_13);
x_15 = lean_array_get_size(x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_12);
return x_17;
}
block_84:
{
lean_object* x_26; 
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_26 = l_Lean_Meta_Grind_preprocessPattern(x_20, x_2, x_21, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_19);
x_29 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_19, x_21, x_22, x_23, x_24, x_28);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
lean_dec(x_29);
x_11 = x_27;
x_12 = x_32;
goto block_18;
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_29);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_29, 1);
x_35 = lean_ctor_get(x_29, 0);
lean_dec(x_35);
x_36 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_27);
x_37 = lean_grind_normalize(x_27, x_36, x_21, x_22, x_23, x_24, x_34);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_mk_string_unchecked("mkEMatchEqTheoremCore: after preprocessing: ", 44, 44);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
lean_inc(x_27);
x_42 = l_Lean_MessageData_ofExpr(x_27);
lean_ctor_set_tag(x_29, 7);
lean_ctor_set(x_29, 1, x_42);
lean_ctor_set(x_29, 0, x_41);
x_43 = lean_mk_string_unchecked(", ", 2, 2);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_29);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_MessageData_ofExpr(x_38);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("", 0, 0);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_19, x_50, x_21, x_22, x_23, x_24, x_39);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_11 = x_27;
x_12 = x_52;
goto block_18;
}
else
{
uint8_t x_53; 
lean_free_object(x_29);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
x_53 = !lean_is_exclusive(x_37);
if (x_53 == 0)
{
return x_37;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_37, 0);
x_55 = lean_ctor_get(x_37, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_37);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_29, 1);
lean_inc(x_57);
lean_dec(x_29);
x_58 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig;
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_27);
x_59 = lean_grind_normalize(x_27, x_58, x_21, x_22, x_23, x_24, x_57);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_mk_string_unchecked("mkEMatchEqTheoremCore: after preprocessing: ", 44, 44);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
lean_inc(x_27);
x_64 = l_Lean_MessageData_ofExpr(x_27);
x_65 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_mk_string_unchecked(", ", 2, 2);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_67);
x_69 = l_Lean_MessageData_ofExpr(x_60);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_mk_string_unchecked("", 0, 0);
x_72 = l_Lean_stringToMessageData(x_71);
lean_dec(x_71);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_70);
lean_ctor_set(x_73, 1, x_72);
x_74 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_19, x_73, x_21, x_22, x_23, x_24, x_61);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
lean_dec(x_74);
x_11 = x_27;
x_12 = x_75;
goto block_18;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
x_76 = lean_ctor_get(x_59, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_59, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_78 = x_59;
} else {
 lean_dec_ref(x_59);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(1, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_19);
x_80 = !lean_is_exclusive(x_26);
if (x_80 == 0)
{
return x_26;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_26, 0);
x_82 = lean_ctor_get(x_26, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_26);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
block_98:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_90 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_90, 0, x_89);
x_91 = l_Lean_MessageData_ofFormat(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_87);
lean_ctor_set(x_92, 1, x_91);
x_93 = lean_mk_string_unchecked("", 0, 0);
x_94 = l_Lean_stringToMessageData(x_93);
lean_dec(x_93);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
lean_inc(x_86);
x_96 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_86, x_95, x_6, x_7, x_8, x_9, x_85);
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_19 = x_86;
x_20 = x_88;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_97;
goto block_84;
}
block_152:
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint8_t x_107; 
x_100 = lean_mk_string_unchecked("grind", 5, 5);
x_101 = lean_mk_string_unchecked("debug", 5, 5);
x_102 = lean_mk_string_unchecked("ematch", 6, 6);
x_103 = lean_mk_string_unchecked("pattern", 7, 7);
x_104 = l_Lean_Name_mkStr4(x_100, x_101, x_102, x_103);
lean_inc(x_104);
x_105 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_104, x_6, x_7, x_8, x_9, x_10);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_unbox(x_106);
lean_dec(x_106);
if (x_107 == 0)
{
lean_object* x_108; 
lean_dec(x_3);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
lean_dec(x_105);
x_19 = x_104;
x_20 = x_99;
x_21 = x_6;
x_22 = x_7;
x_23 = x_8;
x_24 = x_9;
x_25 = x_108;
goto block_84;
}
else
{
uint8_t x_109; 
x_109 = !lean_is_exclusive(x_105);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_105, 1);
x_111 = lean_ctor_get(x_105, 0);
lean_dec(x_111);
x_112 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_3, x_6, x_7, x_8, x_9, x_110);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_113 = lean_ctor_get(x_112, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_112, 1);
lean_inc(x_114);
lean_dec(x_112);
x_115 = lean_mk_string_unchecked("mkEMatchEqTheoremCore: origin: ", 31, 31);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
lean_ctor_set_tag(x_105, 7);
lean_ctor_set(x_105, 1, x_113);
lean_ctor_set(x_105, 0, x_116);
x_117 = lean_mk_string_unchecked(", pat: ", 7, 7);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_105);
lean_ctor_set(x_119, 1, x_118);
lean_inc(x_99);
x_120 = l_Lean_MessageData_ofExpr(x_99);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked(", useLhs: ", 10, 10);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
if (x_4 == 0)
{
lean_object* x_125; 
x_125 = lean_mk_string_unchecked("false", 5, 5);
x_85 = x_114;
x_86 = x_104;
x_87 = x_124;
x_88 = x_99;
x_89 = x_125;
goto block_98;
}
else
{
lean_object* x_126; 
x_126 = lean_mk_string_unchecked("true", 4, 4);
x_85 = x_114;
x_86 = x_104;
x_87 = x_124;
x_88 = x_99;
x_89 = x_126;
goto block_98;
}
}
else
{
uint8_t x_127; 
lean_free_object(x_105);
lean_dec(x_104);
lean_dec(x_99);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_127 = !lean_is_exclusive(x_112);
if (x_127 == 0)
{
return x_112;
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_112, 0);
x_129 = lean_ctor_get(x_112, 1);
lean_inc(x_129);
lean_inc(x_128);
lean_dec(x_112);
x_130 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_130, 0, x_128);
lean_ctor_set(x_130, 1, x_129);
return x_130;
}
}
}
else
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_105, 1);
lean_inc(x_131);
lean_dec(x_105);
x_132 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_3, x_6, x_7, x_8, x_9, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_mk_string_unchecked("mkEMatchEqTheoremCore: origin: ", 31, 31);
x_136 = l_Lean_stringToMessageData(x_135);
lean_dec(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_133);
x_138 = lean_mk_string_unchecked(", pat: ", 7, 7);
x_139 = l_Lean_stringToMessageData(x_138);
lean_dec(x_138);
x_140 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_139);
lean_inc(x_99);
x_141 = l_Lean_MessageData_ofExpr(x_99);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_mk_string_unchecked(", useLhs: ", 10, 10);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
x_145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_145, 0, x_142);
lean_ctor_set(x_145, 1, x_144);
if (x_4 == 0)
{
lean_object* x_146; 
x_146 = lean_mk_string_unchecked("false", 5, 5);
x_85 = x_134;
x_86 = x_104;
x_87 = x_145;
x_88 = x_99;
x_89 = x_146;
goto block_98;
}
else
{
lean_object* x_147; 
x_147 = lean_mk_string_unchecked("true", 4, 4);
x_85 = x_134;
x_86 = x_104;
x_87 = x_145;
x_88 = x_99;
x_89 = x_147;
goto block_98;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_104);
lean_dec(x_99);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_148 = lean_ctor_get(x_132, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_132, 1);
lean_inc(x_149);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_150 = x_132;
} else {
 lean_dec_ref(x_132);
 x_150 = lean_box(0);
}
if (lean_is_scalar(x_150)) {
 x_151 = lean_alloc_ctor(1, 2, 0);
} else {
 x_151 = x_150;
}
lean_ctor_set(x_151, 0, x_148);
lean_ctor_set(x_151, 1, x_149);
return x_151;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__1(uint8_t x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_42; uint8_t x_43; 
lean_inc(x_5);
x_11 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_5, x_7, x_10);
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
x_42 = l_Lean_Expr_cleanupAnnotations(x_12);
x_43 = l_Lean_Expr_isApp(x_42);
if (x_43 == 0)
{
lean_dec(x_42);
lean_dec(x_2);
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
goto block_31;
}
else
{
lean_object* x_44; uint8_t x_45; 
lean_inc(x_42);
x_44 = l_Lean_Expr_appFnCleanup___redArg(x_42);
x_45 = l_Lean_Expr_isApp(x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_42);
lean_dec(x_2);
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
goto block_31;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_ctor_get(x_44, 1);
lean_inc(x_47);
x_48 = l_Lean_Expr_appFnCleanup___redArg(x_44);
x_49 = lean_mk_string_unchecked("Iff", 3, 3);
x_50 = l_Lean_Name_mkStr1(x_49);
x_51 = l_Lean_Expr_isConstOf(x_48, x_50);
lean_dec(x_50);
if (x_51 == 0)
{
uint8_t x_52; 
x_52 = l_Lean_Expr_isApp(x_48);
if (x_52 == 0)
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_2);
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
goto block_31;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_48);
x_53 = l_Lean_Expr_appFnCleanup___redArg(x_48);
x_54 = lean_mk_string_unchecked("Eq", 2, 2);
x_55 = l_Lean_Name_mkStr1(x_54);
x_56 = l_Lean_Expr_isConstOf(x_53, x_55);
lean_dec(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
lean_dec(x_47);
x_57 = l_Lean_Expr_isApp(x_53);
if (x_57 == 0)
{
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_2);
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
goto block_31;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = l_Lean_Expr_appFnCleanup___redArg(x_53);
x_59 = lean_mk_string_unchecked("HEq", 3, 3);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = l_Lean_Expr_isConstOf(x_58, x_60);
lean_dec(x_60);
lean_dec(x_58);
if (x_61 == 0)
{
lean_dec(x_48);
lean_dec(x_46);
lean_dec(x_2);
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_9;
goto block_31;
}
else
{
lean_object* x_62; 
lean_dec(x_14);
lean_dec(x_5);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_dec(x_48);
x_32 = x_62;
x_33 = x_46;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_13;
goto block_41;
}
}
}
else
{
lean_dec(x_53);
lean_dec(x_48);
lean_dec(x_14);
lean_dec(x_5);
x_32 = x_47;
x_33 = x_46;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_13;
goto block_41;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_14);
lean_dec(x_5);
x_32 = x_47;
x_33 = x_46;
x_34 = x_6;
x_35 = x_7;
x_36 = x_8;
x_37 = x_9;
x_38 = x_13;
goto block_41;
}
}
}
block_31:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_19 = lean_mk_string_unchecked("invalid E-matching equality theorem, conclusion must be an equality", 67, 67);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = l_Lean_indentExpr(x_5);
if (lean_is_scalar(x_14)) {
 x_22 = lean_alloc_ctor(7, 2, 0);
} else {
 x_22 = x_14;
 lean_ctor_set_tag(x_22, 7);
}
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_mk_string_unchecked("", 0, 0);
x_24 = l_Lean_stringToMessageData(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_24);
x_26 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_25, x_15, x_16, x_17, x_18, x_13);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
return x_26;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_26);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
block_41:
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_32);
lean_ctor_set(x_39, 1, x_33);
x_40 = l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__0(x_4, x_1, x_2, x_3, x_39, x_34, x_35, x_36, x_37, x_38);
return x_40;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_11 = lean_infer_type(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(x_4);
x_15 = lean_box(x_5);
lean_inc(x_1);
x_16 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__1___boxed), 10, 3);
lean_closure_set(x_16, 0, x_14);
lean_closure_set(x_16, 1, x_1);
lean_closure_set(x_16, 2, x_15);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_19 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_12, x_16, x_18, x_6, x_7, x_8, x_9, x_13);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (x_5 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_box(1);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_Grind_mkEMatchTheoremCore(x_1, x_2, x_22, x_3, x_23, x_25, x_6, x_7, x_8, x_9, x_21);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_19, 1);
lean_inc(x_27);
lean_dec(x_19);
x_28 = lean_ctor_get(x_20, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_20, 1);
lean_inc(x_29);
lean_dec(x_20);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
x_32 = l_Lean_Meta_Grind_mkEMatchTheoremCore(x_1, x_2, x_28, x_3, x_29, x_31, x_6, x_7, x_8, x_9, x_27);
return x_32;
}
}
else
{
uint8_t x_33; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
return x_19;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_19, 0);
x_35 = lean_ctor_get(x_19, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_19);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
else
{
uint8_t x_37; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_11);
if (x_37 == 0)
{
return x_11;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_11, 0);
x_39 = lean_ctor_get(x_11, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_11);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__0(x_1, x_11, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = l_Lean_Meta_Grind_mkEMatchEqTheoremCore___lam__1(x_11, x_2, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_Grind_mkEMatchEqTheoremCore(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_17; uint8_t x_18; 
lean_inc(x_2);
x_17 = l_Lean_Expr_cleanupAnnotations(x_2);
x_18 = l_Lean_Expr_isApp(x_17);
if (x_18 == 0)
{
lean_dec(x_17);
goto block_16;
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_inc(x_17);
x_19 = l_Lean_Expr_appFnCleanup___redArg(x_17);
x_20 = l_Lean_Expr_isApp(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
goto block_16;
}
else
{
lean_object* x_21; uint8_t x_22; 
lean_inc(x_19);
x_21 = l_Lean_Expr_appFnCleanup___redArg(x_19);
x_22 = l_Lean_Expr_isApp(x_21);
if (x_22 == 0)
{
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
goto block_16;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
lean_inc(x_21);
x_23 = l_Lean_Expr_appFnCleanup___redArg(x_21);
x_24 = lean_mk_string_unchecked("Eq", 2, 2);
x_25 = l_Lean_Name_mkStr1(x_24);
x_26 = l_Lean_Expr_isConstOf(x_23, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
goto block_16;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_dec(x_21);
x_30 = l_Lean_Expr_constLevels_x21(x_23);
lean_dec(x_23);
x_31 = l_Lean_Meta_Grind_mkEqBwdPattern(x_30, x_29, x_28, x_27);
x_32 = l_Lean_Meta_Grind_preprocessPattern(x_31, x_26, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_array_get_size(x_1);
x_36 = lean_expr_abstract(x_34, x_1);
lean_dec(x_34);
x_37 = lean_box(0);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_35);
lean_ctor_set(x_39, 1, x_38);
lean_ctor_set(x_32, 0, x_39);
return x_32;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_ctor_get(x_32, 0);
x_41 = lean_ctor_get(x_32, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_32);
x_42 = lean_array_get_size(x_1);
x_43 = lean_expr_abstract(x_40, x_1);
lean_dec(x_40);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_41);
return x_47;
}
}
else
{
uint8_t x_48; 
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
}
}
}
block_16:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("invalid E-matching `←=` theorem, conclusion must be an equality", 65, 63);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_indentExpr(x_2);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_14, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_9 = lean_infer_type(x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore___lam__0___boxed), 7, 0);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_15 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_10, x_12, x_14, x_4, x_5, x_6, x_7, x_11);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_box(3);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_Meta_Grind_mkEMatchTheoremCore(x_1, x_2, x_18, x_3, x_19, x_21, x_4, x_5, x_6, x_7, x_17);
return x_22;
}
else
{
uint8_t x_23; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_27; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_9);
if (x_27 == 0)
{
return x_9;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_9, 0);
x_29 = lean_ctor_get(x_9, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_9);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheorem(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getProofFor(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_1);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_mk_empty_array_with_capacity(x_13);
x_15 = l_Lean_Meta_Grind_mkEMatchEqTheoremCore(x_12, x_14, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_11);
return x_15;
}
else
{
uint8_t x_16; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_9);
if (x_16 == 0)
{
return x_9;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_9, 0);
x_18 = lean_ctor_get(x_9, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_9);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Grind_mkEMatchEqTheorem(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = l_Lean_Meta_Grind_mkEMatchTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_13, x_11, x_15, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_4);
lean_dec(x_4);
x_11 = l_Lean_Meta_Grind_addEMatchTheorem(x_1, x_2, x_3, x_10, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchEqTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
x_9 = lean_unbox(x_7);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_10 = l_Lean_Meta_Grind_mkEMatchEqTheorem(x_1, x_8, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
x_16 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_13, x_11, x_15, x_2, x_3, x_4, x_5, x_12);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_16;
}
else
{
uint8_t x_17; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_17 = !lean_is_exclusive(x_10);
if (x_17 == 0)
{
return x_10;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_10, 0);
x_19 = lean_ctor_get(x_10, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_10);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
lean_dec(x_10);
x_12 = l_Lean_ScopedEnvExtension_getState___redArg(x_6, x_8, x_7, x_11);
lean_ctor_set(x_3, 0, x_12);
return x_3;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_3);
x_15 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get_uint8(x_19, sizeof(void*)*3);
lean_dec(x_19);
x_21 = l_Lean_ScopedEnvExtension_getState___redArg(x_15, x_17, x_16, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_14);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_getEMatchTheorems___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_getEMatchTheorems___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_getEMatchTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Grind_getEMatchTheorems(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_12 = lean_infer_type(x_11, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_13);
x_15 = l_Lean_Meta_isProp(x_13, x_5, x_6, x_7, x_8, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_24; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_24 = lean_unbox(x_16);
lean_dec(x_16);
if (x_24 == 0)
{
lean_dec(x_13);
x_18 = x_4;
goto block_23;
}
else
{
lean_object* x_25; 
x_25 = lean_array_push(x_4, x_13);
x_18 = x_25;
goto block_23;
}
block_23:
{
lean_object* x_19; size_t x_20; size_t x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_2 = x_21;
x_4 = x_18;
x_9 = x_17;
goto _start;
}
}
else
{
uint8_t x_26; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_15);
if (x_26 == 0)
{
return x_15;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_15, 0);
x_28 = lean_ctor_get(x_15, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_15);
x_29 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
else
{
uint8_t x_30; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_12);
if (x_30 == 0)
{
return x_12;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_12, 0);
x_32 = lean_ctor_get(x_12, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_12);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_9);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_unsigned_to_nat(0u);
x_10 = lean_mk_empty_array_with_capacity(x_9);
x_11 = lean_nat_dec_lt(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_8);
return x_12;
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_le(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_8);
return x_15;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
x_16 = lean_usize_of_nat(x_2);
x_17 = lean_usize_of_nat(x_3);
x_18 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0_spec__0(x_1, x_16, x_17, x_10, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_1);
x_9 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0(x_1, x_7, x_8, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Array_filterMapM___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 1);
x_5 = l_Array_contains___at___Lean_Meta_arrowDomainsN_spec__0(x_4, x_1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_3);
return x_9;
}
}
case 4:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_1, 0);
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isForbidden(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_3);
return x_15;
}
}
default: 
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg(x_1, x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 12);
x_5 = lean_ctor_get(x_2, 2);
x_6 = l_Lean_checkTraceOption(x_4, x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_1, x_7, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(x_2, x_3, x_4, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_take(x_6, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint64_t x_20; lean_object* x_21; lean_object* x_22; double x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_11, 1);
x_15 = lean_ctor_get(x_5, 5);
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_13, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_13, 3);
lean_inc(x_19);
x_20 = lean_ctor_get_uint64(x_19, sizeof(void*)*1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_float_of_nat(x_22);
x_24 = lean_box(0);
x_25 = lean_mk_string_unchecked("", 0, 0);
x_26 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set_float(x_26, sizeof(void*)*2, x_23);
lean_ctor_set_float(x_26, sizeof(void*)*2 + 8, x_23);
x_27 = lean_unbox(x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*2 + 16, x_27);
x_28 = lean_mk_empty_array_with_capacity(x_22);
x_29 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_9);
lean_ctor_set(x_29, 2, x_28);
lean_inc(x_15);
lean_ctor_set(x_11, 1, x_29);
lean_ctor_set(x_11, 0, x_15);
x_30 = l_Lean_PersistentArray_push___redArg(x_21, x_11);
x_31 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set_uint64(x_31, sizeof(void*)*1, x_20);
x_32 = lean_ctor_get(x_13, 4);
lean_inc(x_32);
x_33 = lean_ctor_get(x_13, 5);
lean_inc(x_33);
x_34 = lean_ctor_get(x_13, 6);
lean_inc(x_34);
x_35 = lean_ctor_get(x_13, 7);
lean_inc(x_35);
lean_dec(x_13);
x_36 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_36, 0, x_16);
lean_ctor_set(x_36, 1, x_17);
lean_ctor_set(x_36, 2, x_18);
lean_ctor_set(x_36, 3, x_31);
lean_ctor_set(x_36, 4, x_32);
lean_ctor_set(x_36, 5, x_33);
lean_ctor_set(x_36, 6, x_34);
lean_ctor_set(x_36, 7, x_35);
x_37 = lean_st_ref_set(x_6, x_36, x_14);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
x_40 = lean_box(0);
lean_ctor_set(x_37, 0, x_40);
return x_37;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_37, 1);
lean_inc(x_41);
lean_dec(x_37);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_41);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint64_t x_51; lean_object* x_52; lean_object* x_53; double x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_44 = lean_ctor_get(x_11, 0);
x_45 = lean_ctor_get(x_11, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_11);
x_46 = lean_ctor_get(x_5, 5);
x_47 = lean_ctor_get(x_44, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_44, 2);
lean_inc(x_49);
x_50 = lean_ctor_get(x_44, 3);
lean_inc(x_50);
x_51 = lean_ctor_get_uint64(x_50, sizeof(void*)*1);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_float_of_nat(x_53);
x_55 = lean_box(0);
x_56 = lean_mk_string_unchecked("", 0, 0);
x_57 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_57, 0, x_1);
lean_ctor_set(x_57, 1, x_56);
lean_ctor_set_float(x_57, sizeof(void*)*2, x_54);
lean_ctor_set_float(x_57, sizeof(void*)*2 + 8, x_54);
x_58 = lean_unbox(x_55);
lean_ctor_set_uint8(x_57, sizeof(void*)*2 + 16, x_58);
x_59 = lean_mk_empty_array_with_capacity(x_53);
x_60 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_60, 0, x_57);
lean_ctor_set(x_60, 1, x_9);
lean_ctor_set(x_60, 2, x_59);
lean_inc(x_46);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_46);
lean_ctor_set(x_61, 1, x_60);
x_62 = l_Lean_PersistentArray_push___redArg(x_52, x_61);
x_63 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set_uint64(x_63, sizeof(void*)*1, x_51);
x_64 = lean_ctor_get(x_44, 4);
lean_inc(x_64);
x_65 = lean_ctor_get(x_44, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_44, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_44, 7);
lean_inc(x_67);
lean_dec(x_44);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_68, 1, x_48);
lean_ctor_set(x_68, 2, x_49);
lean_ctor_set(x_68, 3, x_63);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_6, x_68, x_45);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_71 = x_69;
} else {
 lean_dec_ref(x_69);
 x_71 = lean_box(0);
}
x_72 = lean_box(0);
if (lean_is_scalar(x_71)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_71;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_70);
return x_73;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_1, x_2, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_27 = lean_mk_string_unchecked("grind", 5, 5);
x_28 = lean_mk_string_unchecked("debug", 5, 5);
x_29 = lean_mk_string_unchecked("ematch", 6, 6);
x_30 = lean_mk_string_unchecked("pattern", 7, 7);
x_31 = l_Lean_Name_mkStr4(x_27, x_28, x_29, x_30);
lean_inc(x_31);
x_69 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_31, x_7, x_9);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_unbox(x_70);
lean_dec(x_70);
if (x_71 == 0)
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_72;
goto block_68;
}
else
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_69);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_74 = lean_ctor_get(x_69, 1);
x_75 = lean_ctor_get(x_69, 0);
lean_dec(x_75);
x_76 = lean_mk_string_unchecked("found pattern: ", 15, 15);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
lean_inc(x_1);
x_78 = l_Lean_Meta_Grind_ppPattern(x_1);
lean_ctor_set_tag(x_69, 7);
lean_ctor_set(x_69, 1, x_78);
lean_ctor_set(x_69, 0, x_77);
x_79 = lean_mk_string_unchecked("", 0, 0);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_69);
lean_ctor_set(x_81, 1, x_80);
lean_inc(x_31);
x_82 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_31, x_81, x_5, x_6, x_7, x_8, x_74);
x_83 = lean_ctor_get(x_82, 1);
lean_inc(x_83);
lean_dec(x_82);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_83;
goto block_68;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_84 = lean_ctor_get(x_69, 1);
lean_inc(x_84);
lean_dec(x_69);
x_85 = lean_mk_string_unchecked("found pattern: ", 15, 15);
x_86 = l_Lean_stringToMessageData(x_85);
lean_dec(x_85);
lean_inc(x_1);
x_87 = l_Lean_Meta_Grind_ppPattern(x_1);
x_88 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
x_89 = lean_mk_string_unchecked("", 0, 0);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_88);
lean_ctor_set(x_91, 1, x_90);
lean_inc(x_31);
x_92 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_31, x_91, x_5, x_6, x_7, x_8, x_84);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_32 = x_2;
x_33 = x_3;
x_34 = x_4;
x_35 = x_5;
x_36 = x_6;
x_37 = x_7;
x_38 = x_8;
x_39 = x_93;
goto block_68;
}
}
block_26:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_st_ref_take(x_11, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_array_push(x_16, x_1);
x_18 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*1, x_10);
x_19 = lean_st_ref_set(x_11, x_18, x_15);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
block_68:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_st_ref_get(x_34, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_32, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_32, 1);
lean_inc(x_45);
lean_dec(x_32);
x_46 = lean_array_get_size(x_45);
lean_dec(x_45);
lean_inc(x_38);
lean_inc(x_37);
lean_inc(x_36);
lean_inc(x_35);
x_47 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage(x_44, x_46, x_43, x_35, x_36, x_37, x_38, x_42);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_31);
x_50 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_31, x_37, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = lean_box(1);
x_54 = lean_unbox(x_51);
lean_dec(x_51);
if (x_54 == 0)
{
uint8_t x_55; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
x_55 = lean_unbox(x_53);
x_10 = x_55;
x_11 = x_33;
x_12 = x_52;
goto block_26;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_56 = lean_mk_string_unchecked("found full coverage", 19, 19);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_31, x_57, x_35, x_36, x_37, x_38, x_52);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_unbox(x_53);
x_10 = x_60;
x_11 = x_33;
x_12 = x_59;
goto block_26;
}
}
else
{
lean_object* x_61; lean_object* x_62; uint8_t x_63; 
lean_dec(x_48);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
x_61 = lean_ctor_get(x_47, 1);
lean_inc(x_61);
lean_dec(x_47);
x_62 = lean_box(0);
x_63 = lean_unbox(x_62);
x_10 = x_63;
x_11 = x_33;
x_12 = x_61;
goto block_26;
}
}
else
{
uint8_t x_64; 
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_31);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_47);
if (x_64 == 0)
{
return x_47;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_47);
x_67 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_67, 0, x_65);
lean_ctor_set(x_67, 1, x_66);
return x_67;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars_go(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_box(0);
x_5 = l_List_elem___at___Lean_Meta_Occurrences_contains_spec__0(x_3, x_2);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_2);
return x_8;
}
}
case 5:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_ctor_get(x_1, 1);
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars_go(x_9, x_2);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
case 10:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 1);
x_1 = x_14;
goto _start;
}
default: 
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_2);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars_go___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars_go(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = lean_box(0);
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars_go(x_1, x_2);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint64_t x_14; lean_object* x_15; uint64_t x_16; uint64_t x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; size_t x_23; size_t x_24; lean_object* x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_2)) {
 lean_ctor_release(x_2, 0);
 lean_ctor_release(x_2, 1);
 x_7 = x_2;
} else {
 lean_dec_ref(x_2);
 x_7 = lean_box(0);
}
x_11 = lean_ctor_get(x_1, 0);
x_12 = lean_ctor_get(x_1, 1);
x_13 = lean_array_get_size(x_12);
x_14 = lean_uint64_of_nat(x_5);
x_15 = lean_unsigned_to_nat(32u);
x_16 = lean_uint64_of_nat(x_15);
x_17 = lean_uint64_shift_right(x_14, x_16);
x_18 = lean_uint64_xor(x_14, x_17);
x_19 = lean_unsigned_to_nat(16u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_uint64_to_usize(x_22);
x_24 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_sub(x_24, x_26);
x_28 = lean_usize_land(x_23, x_27);
x_29 = lean_array_uget(x_12, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_NormalizePattern_foundBVar_spec__0___redArg(x_5, x_29);
lean_dec(x_29);
if (x_30 == 0)
{
goto block_10;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_nat_dec_eq(x_11, x_31);
if (x_32 == 0)
{
lean_dec(x_7);
lean_dec(x_5);
x_2 = x_6;
goto _start;
}
else
{
goto block_10;
}
}
block_10:
{
lean_object* x_8; 
if (lean_is_scalar(x_7)) {
 x_8 = lean_alloc_ctor(1, 2, 0);
} else {
 x_8 = x_7;
}
lean_ctor_set(x_8, 0, x_5);
lean_ctor_set(x_8, 1, x_3);
x_2 = x_6;
x_3 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff_spec__0(x_2, x_1, x_6);
return x_7;
}
else
{
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_List_filterTR_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff_spec__0(x_1, x_2, x_3);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_5, x_4);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_box(0);
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 2);
lean_inc(x_20);
x_21 = lean_nat_dec_lt(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_17);
lean_ctor_set(x_22, 1, x_18);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_7);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_32; 
x_24 = lean_ctor_get(x_18, 0);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_array_fget(x_24, x_19);
x_26 = lean_unbox(x_25);
lean_dec(x_25);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_19, x_27);
lean_dec(x_19);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_24);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_20);
x_32 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_26);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_array_uget(x_3, x_5);
x_34 = l_Lean_Expr_isBVar(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc(x_33);
x_35 = l_Lean_Meta_Grind_isOffsetPattern_x3f(x_33);
if (lean_obj_tag(x_35) == 0)
{
if (x_34 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_36 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars(x_2);
x_37 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff(x_36, x_1);
x_38 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatternBVars(x_33);
lean_dec(x_33);
x_39 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_diff(x_38, x_1);
x_40 = lean_alloc_closure((void*)(l_instDecidableEqNat___boxed), 2, 0);
x_41 = l_List_instDecidableRelSubsetOfDecidableEq___redArg(x_40, x_37, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_17);
lean_ctor_set(x_42, 1, x_29);
x_8 = x_42;
x_9 = x_7;
goto block_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_box(x_41);
x_44 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_44, 0, x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_29);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_7);
return x_46;
}
}
else
{
lean_dec(x_33);
goto block_31;
}
}
else
{
lean_dec(x_35);
lean_dec(x_33);
goto block_31;
}
}
else
{
lean_object* x_47; 
lean_dec(x_33);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_17);
lean_ctor_set(x_47, 1, x_29);
x_8 = x_47;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_object* x_48; 
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_17);
lean_ctor_set(x_48, 1, x_29);
x_8 = x_48;
x_9 = x_7;
goto block_14;
}
block_31:
{
lean_object* x_30; 
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_17);
lean_ctor_set(x_30, 1, x_29);
x_8 = x_30;
x_9 = x_7;
goto block_14;
}
}
}
block_14:
{
lean_object* x_10; size_t x_11; size_t x_12; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_5, x_11);
x_5 = x_12;
x_6 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_get_size(x_2);
x_9 = l_Array_toSubarray___redArg(x_2, x_7, x_8);
x_10 = lean_box(0);
x_11 = l_Lean_Expr_sort___override(x_10);
x_12 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_12);
x_13 = lean_mk_array(x_12, x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_sub(x_12, x_14);
lean_dec(x_12);
lean_inc(x_1);
x_16 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_13, x_15);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_9);
x_19 = lean_array_size(x_16);
x_20 = lean_usize_of_nat(x_7);
x_21 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___redArg(x_3, x_1, x_16, x_19, x_20, x_18, x_6);
lean_dec(x_16);
lean_dec(x_1);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec(x_22);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_21);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_21, 0);
lean_dec(x_25);
x_26 = lean_box(0);
lean_ctor_set(x_21, 0, x_26);
return x_21;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_27);
return x_29;
}
}
else
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_21);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_21, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_23, 0);
lean_inc(x_32);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_32);
return x_21;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_21, 1);
lean_inc(x_33);
lean_dec(x_21);
x_34 = lean_ctor_get(x_23, 0);
lean_inc(x_34);
lean_dec(x_23);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___redArg(x_1, x_2, x_3, x_8, x_9, x_6, x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_11 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_12 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars_spec__0(x_1, x_2, x_3, x_10, x_11, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_3, x_2);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_mk_string_unchecked("grind", 5, 5);
x_27 = lean_mk_string_unchecked("debug", 5, 5);
x_28 = lean_mk_string_unchecked("ematch", 6, 6);
x_29 = lean_mk_string_unchecked("pattern", 7, 7);
x_30 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_29);
lean_inc(x_30);
x_31 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_30, x_10, x_12);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_58; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_array_uget(x_1, x_3);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_nat_add(x_22, x_35);
x_39 = lean_array_fget(x_37, x_22);
lean_dec(x_22);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_23);
x_58 = lean_unbox(x_33);
lean_dec(x_33);
if (x_58 == 0)
{
lean_free_object(x_31);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = x_5;
x_43 = x_6;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_11;
x_49 = x_34;
goto block_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_75; 
x_59 = lean_mk_string_unchecked("arg: ", 5, 5);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
lean_inc(x_36);
x_61 = l_Lean_MessageData_ofExpr(x_36);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_61);
lean_ctor_set(x_31, 0, x_60);
x_62 = lean_mk_string_unchecked(", support: ", 11, 11);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_31);
lean_ctor_set(x_64, 1, x_63);
x_75 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_40);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_mk_string_unchecked("false", 5, 5);
x_65 = x_76;
goto block_74;
}
else
{
lean_object* x_77; 
x_77 = lean_mk_string_unchecked("true", 4, 4);
x_65 = x_77;
goto block_74;
}
block_74:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_30, x_71, x_8, x_9, x_10, x_11, x_34);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = x_5;
x_43 = x_6;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_11;
x_49 = x_73;
goto block_57;
}
}
block_57:
{
uint8_t x_50; 
x_50 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_40);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_36, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_13 = x_41;
x_14 = x_52;
goto block_19;
}
else
{
uint8_t x_53; 
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_36);
x_13 = x_41;
x_14 = x_49;
goto block_19;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_103; 
x_78 = lean_ctor_get(x_31, 0);
x_79 = lean_ctor_get(x_31, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_31);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_array_uget(x_1, x_3);
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
lean_dec(x_4);
x_83 = lean_nat_add(x_22, x_80);
x_84 = lean_array_fget(x_82, x_22);
lean_dec(x_22);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_23);
x_103 = lean_unbox(x_78);
lean_dec(x_78);
if (x_103 == 0)
{
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
x_91 = x_9;
x_92 = x_10;
x_93 = x_11;
x_94 = x_79;
goto block_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_121; 
x_104 = lean_mk_string_unchecked("arg: ", 5, 5);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
lean_inc(x_81);
x_106 = l_Lean_MessageData_ofExpr(x_81);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked(", support: ", 11, 11);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_121 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_85);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_mk_string_unchecked("false", 5, 5);
x_111 = x_122;
goto block_120;
}
else
{
lean_object* x_123; 
x_123 = lean_mk_string_unchecked("true", 4, 4);
x_111 = x_123;
goto block_120;
}
block_120:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked("", 0, 0);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_30, x_117, x_8, x_9, x_10, x_11, x_79);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
x_91 = x_9;
x_92 = x_10;
x_93 = x_11;
x_94 = x_119;
goto block_102;
}
}
block_102:
{
uint8_t x_95; 
x_95 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_85);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_81, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_13 = x_86;
x_14 = x_97;
goto block_19;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_86);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_81);
x_13 = x_86;
x_14 = x_94;
goto block_19;
}
}
}
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_13;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_3, x_2);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_4, 2);
lean_inc(x_23);
x_24 = lean_nat_dec_lt(x_22, x_23);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_12);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_mk_string_unchecked("grind", 5, 5);
x_27 = lean_mk_string_unchecked("debug", 5, 5);
x_28 = lean_mk_string_unchecked("ematch", 6, 6);
x_29 = lean_mk_string_unchecked("pattern", 7, 7);
x_30 = l_Lean_Name_mkStr4(x_26, x_27, x_28, x_29);
lean_inc(x_30);
x_31 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_30, x_10, x_12);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; uint8_t x_58; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_array_uget(x_1, x_3);
x_37 = lean_ctor_get(x_4, 0);
lean_inc(x_37);
lean_dec(x_4);
x_38 = lean_nat_add(x_22, x_35);
x_39 = lean_array_fget(x_37, x_22);
lean_dec(x_22);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_41, 0, x_37);
lean_ctor_set(x_41, 1, x_38);
lean_ctor_set(x_41, 2, x_23);
x_58 = lean_unbox(x_33);
lean_dec(x_33);
if (x_58 == 0)
{
lean_free_object(x_31);
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = x_5;
x_43 = x_6;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_11;
x_49 = x_34;
goto block_57;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_75; 
x_59 = lean_mk_string_unchecked("arg: ", 5, 5);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
lean_inc(x_36);
x_61 = l_Lean_MessageData_ofExpr(x_36);
lean_ctor_set_tag(x_31, 7);
lean_ctor_set(x_31, 1, x_61);
lean_ctor_set(x_31, 0, x_60);
x_62 = lean_mk_string_unchecked(", support: ", 11, 11);
x_63 = l_Lean_stringToMessageData(x_62);
lean_dec(x_62);
x_64 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_64, 0, x_31);
lean_ctor_set(x_64, 1, x_63);
x_75 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_40);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_mk_string_unchecked("false", 5, 5);
x_65 = x_76;
goto block_74;
}
else
{
lean_object* x_77; 
x_77 = lean_mk_string_unchecked("true", 4, 4);
x_65 = x_77;
goto block_74;
}
block_74:
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_66 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_66, 0, x_65);
x_67 = l_Lean_MessageData_ofFormat(x_66);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_64);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("", 0, 0);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_30, x_71, x_8, x_9, x_10, x_11, x_34);
x_73 = lean_ctor_get(x_72, 1);
lean_inc(x_73);
lean_dec(x_72);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_42 = x_5;
x_43 = x_6;
x_44 = x_7;
x_45 = x_8;
x_46 = x_9;
x_47 = x_10;
x_48 = x_11;
x_49 = x_73;
goto block_57;
}
}
block_57:
{
uint8_t x_50; 
x_50 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_40);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_36, x_42, x_43, x_44, x_45, x_46, x_47, x_48, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; 
x_52 = lean_ctor_get(x_51, 1);
lean_inc(x_52);
lean_dec(x_51);
x_13 = x_41;
x_14 = x_52;
goto block_19;
}
else
{
uint8_t x_53; 
lean_dec(x_41);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_51);
if (x_53 == 0)
{
return x_51;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_51, 0);
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_51);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_42);
lean_dec(x_36);
x_13 = x_41;
x_14 = x_49;
goto block_19;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_103; 
x_78 = lean_ctor_get(x_31, 0);
x_79 = lean_ctor_get(x_31, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_31);
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_array_uget(x_1, x_3);
x_82 = lean_ctor_get(x_4, 0);
lean_inc(x_82);
lean_dec(x_4);
x_83 = lean_nat_add(x_22, x_80);
x_84 = lean_array_fget(x_82, x_22);
lean_dec(x_22);
x_85 = lean_unbox(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_83);
lean_ctor_set(x_86, 2, x_23);
x_103 = lean_unbox(x_78);
lean_dec(x_78);
if (x_103 == 0)
{
lean_dec(x_30);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
x_91 = x_9;
x_92 = x_10;
x_93 = x_11;
x_94 = x_79;
goto block_102;
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_121; 
x_104 = lean_mk_string_unchecked("arg: ", 5, 5);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
lean_inc(x_81);
x_106 = l_Lean_MessageData_ofExpr(x_81);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked(", support: ", 11, 11);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_121 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_85);
if (x_121 == 0)
{
lean_object* x_122; 
x_122 = lean_mk_string_unchecked("false", 5, 5);
x_111 = x_122;
goto block_120;
}
else
{
lean_object* x_123; 
x_123 = lean_mk_string_unchecked("true", 4, 4);
x_111 = x_123;
goto block_120;
}
block_120:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked("", 0, 0);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_30, x_117, x_8, x_9, x_10, x_11, x_79);
x_119 = lean_ctor_get(x_118, 1);
lean_inc(x_119);
lean_dec(x_118);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_87 = x_5;
x_88 = x_6;
x_89 = x_7;
x_90 = x_8;
x_91 = x_9;
x_92 = x_10;
x_93 = x_11;
x_94 = x_119;
goto block_102;
}
}
block_102:
{
uint8_t x_95; 
x_95 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_85);
if (x_95 == 0)
{
lean_object* x_96; 
x_96 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_81, x_87, x_88, x_89, x_90, x_91, x_92, x_93, x_94);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_96, 1);
lean_inc(x_97);
lean_dec(x_96);
x_13 = x_86;
x_14 = x_97;
goto block_19;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_dec(x_86);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_98 = lean_ctor_get(x_96, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_100 = x_96;
} else {
 lean_dec_ref(x_96);
 x_100 = lean_box(0);
}
if (lean_is_scalar(x_100)) {
 x_101 = lean_alloc_ctor(1, 2, 0);
} else {
 x_101 = x_100;
}
lean_ctor_set(x_101, 0, x_98);
lean_ctor_set(x_101, 1, x_99);
return x_101;
}
}
else
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_81);
x_13 = x_86;
x_14 = x_94;
goto block_19;
}
}
}
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; lean_object* x_18; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0_spec__0(x_1, x_2, x_17, x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_set(x_5, x_1, x_10);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_11, 0);
x_17 = lean_ctor_get(x_11, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_11);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_17);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_19; lean_object* x_20; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_6, 1);
lean_inc(x_48);
x_49 = lean_expr_abstract(x_1, x_48);
lean_dec(x_48);
x_50 = l_Lean_Expr_hasLooseBVars(x_49);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_inc(x_2);
x_51 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_2, x_11, x_13);
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_unbox(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_2);
x_54 = lean_ctor_get(x_51, 1);
lean_inc(x_54);
lean_dec(x_51);
x_14 = x_54;
goto block_18;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_mk_string_unchecked("skip, does not contain pattern variables", 40, 40);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_2, x_57, x_9, x_10, x_11, x_12, x_55);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_14 = x_59;
goto block_18;
}
}
else
{
lean_object* x_60; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_60 = l_Lean_Meta_Grind_NormalizePattern_normalizePattern(x_49, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_60) == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_61 = lean_ctor_get(x_60, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_st_ref_get(x_8, x_62);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_3, 2);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_64, 2);
lean_inc(x_68);
lean_dec(x_64);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec(x_68);
x_70 = lean_nat_dec_lt(x_67, x_69);
lean_dec(x_69);
lean_dec(x_67);
if (x_70 == 0)
{
lean_dec(x_66);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_4);
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_65;
goto block_47;
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
lean_inc(x_61);
x_71 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_hasChildWithSameNewBVars(x_61, x_4, x_66, x_11, x_12, x_65);
lean_dec(x_66);
x_72 = lean_ctor_get(x_71, 0);
lean_inc(x_72);
x_73 = lean_unbox(x_72);
lean_dec(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_3);
lean_dec(x_2);
x_74 = !lean_is_exclusive(x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_71, 1);
x_76 = lean_ctor_get(x_71, 0);
lean_dec(x_76);
x_77 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern(x_61, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_75);
lean_dec(x_8);
if (lean_obj_tag(x_77) == 0)
{
uint8_t x_78; 
x_78 = !lean_is_exclusive(x_77);
if (x_78 == 0)
{
lean_object* x_79; lean_object* x_80; 
x_79 = lean_ctor_get(x_77, 0);
lean_dec(x_79);
x_80 = lean_box(0);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_80);
lean_ctor_set(x_71, 0, x_80);
lean_ctor_set(x_77, 0, x_71);
return x_77;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_77, 1);
lean_inc(x_81);
lean_dec(x_77);
x_82 = lean_box(0);
lean_ctor_set_tag(x_71, 1);
lean_ctor_set(x_71, 1, x_82);
lean_ctor_set(x_71, 0, x_82);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_71);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
else
{
uint8_t x_84; 
lean_free_object(x_71);
x_84 = !lean_is_exclusive(x_77);
if (x_84 == 0)
{
return x_77;
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_85 = lean_ctor_get(x_77, 0);
x_86 = lean_ctor_get(x_77, 1);
lean_inc(x_86);
lean_inc(x_85);
lean_dec(x_77);
x_87 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_dec(x_71);
x_89 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern(x_61, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_88);
lean_dec(x_8);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_89, 1);
lean_inc(x_90);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_91 = x_89;
} else {
 lean_dec_ref(x_89);
 x_91 = lean_box(0);
}
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_92);
if (lean_is_scalar(x_91)) {
 x_94 = lean_alloc_ctor(0, 2, 0);
} else {
 x_94 = x_91;
}
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_95 = lean_ctor_get(x_89, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_89, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_89)) {
 lean_ctor_release(x_89, 0);
 lean_ctor_release(x_89, 1);
 x_97 = x_89;
} else {
 lean_dec_ref(x_89);
 x_97 = lean_box(0);
}
if (lean_is_scalar(x_97)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_97;
}
lean_ctor_set(x_98, 0, x_95);
lean_ctor_set(x_98, 1, x_96);
return x_98;
}
}
}
else
{
lean_object* x_99; 
lean_dec(x_61);
lean_dec(x_6);
x_99 = lean_ctor_get(x_71, 1);
lean_inc(x_99);
lean_dec(x_71);
x_32 = x_8;
x_33 = x_9;
x_34 = x_10;
x_35 = x_11;
x_36 = x_12;
x_37 = x_99;
goto block_47;
}
}
}
else
{
uint8_t x_100; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_100 = !lean_is_exclusive(x_60);
if (x_100 == 0)
{
return x_60;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_60, 0);
x_102 = lean_ctor_get(x_60, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_60);
x_103 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
}
block_18:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_14);
return x_17;
}
block_31:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_st_ref_set(x_19, x_3, x_20);
lean_dec(x_19);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_21, 0, x_25);
return x_21;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_26 = lean_ctor_get(x_21, 0);
x_27 = lean_ctor_get(x_21, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_21);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
return x_30;
}
}
block_47:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_inc(x_2);
x_38 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_2, x_35, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_unbox(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_2);
x_41 = lean_ctor_get(x_38, 1);
lean_inc(x_41);
lean_dec(x_38);
x_19 = x_32;
x_20 = x_41;
goto block_31;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_mk_string_unchecked("skip, no new variables covered", 30, 30);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_2, x_44, x_33, x_34, x_35, x_36, x_42);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_19 = x_32;
x_20 = x_46;
goto block_31;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_76; lean_object* x_77; uint8_t x_78; 
x_76 = lean_st_ref_get(x_3, x_9);
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get_uint8(x_77, sizeof(void*)*1);
lean_dec(x_77);
if (x_78 == 0)
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_244; lean_object* x_245; uint8_t x_246; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
x_81 = lean_mk_string_unchecked("grind", 5, 5);
x_82 = lean_mk_string_unchecked("debug", 5, 5);
x_83 = lean_mk_string_unchecked("ematch", 6, 6);
x_84 = lean_mk_string_unchecked("pattern", 7, 7);
x_85 = l_Lean_Name_mkStr4(x_81, x_82, x_83, x_84);
lean_inc(x_85);
x_244 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_85, x_7, x_79);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_unbox(x_245);
lean_dec(x_245);
if (x_246 == 0)
{
lean_object* x_247; 
x_247 = lean_ctor_get(x_244, 1);
lean_inc(x_247);
lean_dec(x_244);
x_165 = x_2;
x_166 = x_3;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_247;
goto block_243;
}
else
{
uint8_t x_248; 
x_248 = !lean_is_exclusive(x_244);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_249 = lean_ctor_get(x_244, 1);
x_250 = lean_ctor_get(x_244, 0);
lean_dec(x_250);
x_251 = lean_mk_string_unchecked("collect: ", 9, 9);
x_252 = l_Lean_stringToMessageData(x_251);
lean_dec(x_251);
lean_inc(x_1);
x_253 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_244, 7);
lean_ctor_set(x_244, 1, x_253);
lean_ctor_set(x_244, 0, x_252);
x_254 = lean_mk_string_unchecked("", 0, 0);
x_255 = l_Lean_stringToMessageData(x_254);
lean_dec(x_254);
x_256 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_256, 0, x_244);
lean_ctor_set(x_256, 1, x_255);
lean_inc(x_85);
x_257 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_85, x_256, x_5, x_6, x_7, x_8, x_249);
x_258 = lean_ctor_get(x_257, 1);
lean_inc(x_258);
lean_dec(x_257);
x_165 = x_2;
x_166 = x_3;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_258;
goto block_243;
}
else
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
x_259 = lean_ctor_get(x_244, 1);
lean_inc(x_259);
lean_dec(x_244);
x_260 = lean_mk_string_unchecked("collect: ", 9, 9);
x_261 = l_Lean_stringToMessageData(x_260);
lean_dec(x_260);
lean_inc(x_1);
x_262 = l_Lean_MessageData_ofExpr(x_1);
x_263 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_263, 0, x_261);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_mk_string_unchecked("", 0, 0);
x_265 = l_Lean_stringToMessageData(x_264);
lean_dec(x_264);
x_266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_266, 0, x_263);
lean_ctor_set(x_266, 1, x_265);
lean_inc(x_85);
x_267 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_85, x_266, x_5, x_6, x_7, x_8, x_259);
x_268 = lean_ctor_get(x_267, 1);
lean_inc(x_268);
lean_dec(x_267);
x_165 = x_2;
x_166 = x_3;
x_167 = x_4;
x_168 = x_5;
x_169 = x_6;
x_170 = x_7;
x_171 = x_8;
x_172 = x_268;
goto block_243;
}
}
block_133:
{
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; 
lean_dec(x_80);
lean_inc(x_85);
x_99 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_85, x_92, x_91);
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_unbox(x_100);
lean_dec(x_100);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_86);
lean_dec(x_85);
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
x_103 = lean_box(0);
lean_inc(x_89);
lean_inc(x_92);
lean_inc(x_93);
lean_inc(x_87);
lean_inc(x_94);
lean_inc(x_95);
lean_inc(x_90);
x_104 = lean_apply_9(x_97, x_103, x_90, x_95, x_94, x_87, x_93, x_92, x_89, x_102);
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_92;
x_64 = x_93;
x_65 = x_95;
x_66 = x_94;
x_67 = x_96;
x_68 = x_104;
goto block_75;
}
else
{
uint8_t x_105; 
x_105 = !lean_is_exclusive(x_99);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_106 = lean_ctor_get(x_99, 1);
x_107 = lean_ctor_get(x_99, 0);
lean_dec(x_107);
x_108 = lean_mk_string_unchecked("skip, exception during normalization", 36, 36);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = l_Lean_Exception_toMessageData(x_86);
x_111 = l_Lean_indentD(x_110);
lean_ctor_set_tag(x_99, 7);
lean_ctor_set(x_99, 1, x_111);
lean_ctor_set(x_99, 0, x_109);
x_112 = lean_mk_string_unchecked("", 0, 0);
x_113 = l_Lean_stringToMessageData(x_112);
lean_dec(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_99);
lean_ctor_set(x_114, 1, x_113);
x_115 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_85, x_114, x_87, x_93, x_92, x_89, x_106);
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
lean_dec(x_115);
lean_inc(x_89);
lean_inc(x_92);
lean_inc(x_93);
lean_inc(x_87);
lean_inc(x_94);
lean_inc(x_95);
lean_inc(x_90);
x_118 = lean_apply_9(x_97, x_116, x_90, x_95, x_94, x_87, x_93, x_92, x_89, x_117);
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_92;
x_64 = x_93;
x_65 = x_95;
x_66 = x_94;
x_67 = x_96;
x_68 = x_118;
goto block_75;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_119 = lean_ctor_get(x_99, 1);
lean_inc(x_119);
lean_dec(x_99);
x_120 = lean_mk_string_unchecked("skip, exception during normalization", 36, 36);
x_121 = l_Lean_stringToMessageData(x_120);
lean_dec(x_120);
x_122 = l_Lean_Exception_toMessageData(x_86);
x_123 = l_Lean_indentD(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_mk_string_unchecked("", 0, 0);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_85, x_127, x_87, x_93, x_92, x_89, x_119);
x_129 = lean_ctor_get(x_128, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
lean_inc(x_89);
lean_inc(x_92);
lean_inc(x_93);
lean_inc(x_87);
lean_inc(x_94);
lean_inc(x_95);
lean_inc(x_90);
x_131 = lean_apply_9(x_97, x_129, x_90, x_95, x_94, x_87, x_93, x_92, x_89, x_130);
x_59 = x_87;
x_60 = x_88;
x_61 = x_89;
x_62 = x_90;
x_63 = x_92;
x_64 = x_93;
x_65 = x_95;
x_66 = x_94;
x_67 = x_96;
x_68 = x_131;
goto block_75;
}
}
}
else
{
lean_object* x_132; 
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_87);
lean_dec(x_85);
lean_dec(x_1);
if (lean_is_scalar(x_80)) {
 x_132 = lean_alloc_ctor(1, 2, 0);
} else {
 x_132 = x_80;
 lean_ctor_set_tag(x_132, 1);
}
lean_ctor_set(x_132, 0, x_86);
lean_ctor_set(x_132, 1, x_91);
return x_132;
}
}
block_148:
{
uint8_t x_146; 
x_146 = l_Lean_Exception_isInterrupt(x_144);
if (x_146 == 0)
{
uint8_t x_147; 
x_147 = l_Lean_Exception_isRuntime(x_144);
x_86 = x_144;
x_87 = x_134;
x_88 = x_135;
x_89 = x_136;
x_90 = x_138;
x_91 = x_145;
x_92 = x_137;
x_93 = x_139;
x_94 = x_141;
x_95 = x_140;
x_96 = x_142;
x_97 = x_143;
x_98 = x_147;
goto block_133;
}
else
{
x_86 = x_144;
x_87 = x_134;
x_88 = x_135;
x_89 = x_136;
x_90 = x_138;
x_91 = x_145;
x_92 = x_137;
x_93 = x_139;
x_94 = x_141;
x_95 = x_140;
x_96 = x_142;
x_97 = x_143;
x_98 = x_146;
goto block_133;
}
}
block_164:
{
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; 
lean_dec(x_158);
lean_dec(x_85);
lean_dec(x_80);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_43 = x_149;
x_44 = x_150;
x_45 = x_151;
x_46 = x_153;
x_47 = x_152;
x_48 = x_154;
x_49 = x_156;
x_50 = x_155;
x_51 = x_157;
x_52 = x_160;
x_53 = x_161;
goto block_58;
}
else
{
lean_object* x_162; lean_object* x_163; 
x_162 = lean_ctor_get(x_159, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_159, 1);
lean_inc(x_163);
lean_dec(x_159);
x_134 = x_149;
x_135 = x_150;
x_136 = x_151;
x_137 = x_153;
x_138 = x_152;
x_139 = x_154;
x_140 = x_155;
x_141 = x_156;
x_142 = x_157;
x_143 = x_158;
x_144 = x_162;
x_145 = x_163;
goto block_148;
}
}
block_243:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; 
x_173 = l_Lean_Expr_getAppFn(x_1);
x_174 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_174);
lean_inc(x_173);
x_175 = l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(x_173, x_174, x_168, x_169, x_170, x_171, x_172);
if (lean_obj_tag(x_175) == 0)
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_176 = lean_ctor_get(x_175, 0);
lean_inc(x_176);
x_177 = lean_ctor_get(x_175, 1);
lean_inc(x_177);
lean_dec(x_175);
x_178 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg(x_173, x_165, x_177);
lean_dec(x_173);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_unbox(x_179);
lean_dec(x_179);
if (x_180 == 0)
{
lean_object* x_181; 
lean_dec(x_85);
lean_dec(x_80);
x_181 = lean_ctor_get(x_178, 1);
lean_inc(x_181);
lean_dec(x_178);
x_10 = x_174;
x_11 = x_176;
x_12 = x_165;
x_13 = x_166;
x_14 = x_167;
x_15 = x_168;
x_16 = x_169;
x_17 = x_170;
x_18 = x_171;
x_19 = x_181;
goto block_42;
}
else
{
lean_object* x_182; lean_object* x_183; uint8_t x_184; 
x_182 = lean_ctor_get(x_178, 1);
lean_inc(x_182);
lean_dec(x_178);
x_183 = lean_st_ref_get(x_167, x_182);
x_184 = !lean_is_exclusive(x_183);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; uint8_t x_190; 
x_185 = lean_ctor_get(x_183, 0);
x_186 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
x_187 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__0___boxed), 10, 1);
lean_closure_set(x_187, 0, x_185);
lean_inc(x_85);
x_188 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_85, x_170, x_186);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_unbox(x_189);
lean_dec(x_189);
if (x_190 == 0)
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_183);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
lean_dec(x_188);
x_192 = lean_box(0);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_176);
lean_inc(x_85);
x_193 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(x_1, x_85, x_185, x_176, x_192, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_191);
x_149 = x_168;
x_150 = x_174;
x_151 = x_171;
x_152 = x_165;
x_153 = x_170;
x_154 = x_169;
x_155 = x_166;
x_156 = x_167;
x_157 = x_176;
x_158 = x_187;
x_159 = x_193;
goto block_164;
}
else
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_188);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
x_195 = lean_ctor_get(x_188, 1);
x_196 = lean_ctor_get(x_188, 0);
lean_dec(x_196);
x_197 = lean_mk_string_unchecked("candidate: ", 11, 11);
x_198 = l_Lean_stringToMessageData(x_197);
lean_dec(x_197);
lean_inc(x_1);
x_199 = l_Lean_MessageData_ofExpr(x_1);
lean_ctor_set_tag(x_188, 7);
lean_ctor_set(x_188, 1, x_199);
lean_ctor_set(x_188, 0, x_198);
x_200 = lean_mk_string_unchecked("", 0, 0);
x_201 = l_Lean_stringToMessageData(x_200);
lean_dec(x_200);
lean_ctor_set_tag(x_183, 7);
lean_ctor_set(x_183, 1, x_201);
lean_ctor_set(x_183, 0, x_188);
lean_inc(x_85);
x_202 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_85, x_183, x_168, x_169, x_170, x_171, x_195);
x_203 = lean_ctor_get(x_202, 0);
lean_inc(x_203);
x_204 = lean_ctor_get(x_202, 1);
lean_inc(x_204);
lean_dec(x_202);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_176);
lean_inc(x_85);
x_205 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(x_1, x_85, x_185, x_176, x_203, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_204);
lean_dec(x_203);
x_149 = x_168;
x_150 = x_174;
x_151 = x_171;
x_152 = x_165;
x_153 = x_170;
x_154 = x_169;
x_155 = x_166;
x_156 = x_167;
x_157 = x_176;
x_158 = x_187;
x_159 = x_205;
goto block_164;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_206 = lean_ctor_get(x_188, 1);
lean_inc(x_206);
lean_dec(x_188);
x_207 = lean_mk_string_unchecked("candidate: ", 11, 11);
x_208 = l_Lean_stringToMessageData(x_207);
lean_dec(x_207);
lean_inc(x_1);
x_209 = l_Lean_MessageData_ofExpr(x_1);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_208);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("", 0, 0);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
lean_ctor_set_tag(x_183, 7);
lean_ctor_set(x_183, 1, x_212);
lean_ctor_set(x_183, 0, x_210);
lean_inc(x_85);
x_213 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_85, x_183, x_168, x_169, x_170, x_171, x_206);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_176);
lean_inc(x_85);
x_216 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(x_1, x_85, x_185, x_176, x_214, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_215);
lean_dec(x_214);
x_149 = x_168;
x_150 = x_174;
x_151 = x_171;
x_152 = x_165;
x_153 = x_170;
x_154 = x_169;
x_155 = x_166;
x_156 = x_167;
x_157 = x_176;
x_158 = x_187;
x_159 = x_216;
goto block_164;
}
}
}
else
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_217 = lean_ctor_get(x_183, 0);
x_218 = lean_ctor_get(x_183, 1);
lean_inc(x_218);
lean_inc(x_217);
lean_dec(x_183);
lean_inc(x_217);
x_219 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__0___boxed), 10, 1);
lean_closure_set(x_219, 0, x_217);
lean_inc(x_85);
x_220 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_85, x_170, x_218);
x_221 = lean_ctor_get(x_220, 0);
lean_inc(x_221);
x_222 = lean_unbox(x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_223 = lean_ctor_get(x_220, 1);
lean_inc(x_223);
lean_dec(x_220);
x_224 = lean_box(0);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_176);
lean_inc(x_85);
x_225 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(x_1, x_85, x_217, x_176, x_224, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_223);
x_149 = x_168;
x_150 = x_174;
x_151 = x_171;
x_152 = x_165;
x_153 = x_170;
x_154 = x_169;
x_155 = x_166;
x_156 = x_167;
x_157 = x_176;
x_158 = x_219;
x_159 = x_225;
goto block_164;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_226 = lean_ctor_get(x_220, 1);
lean_inc(x_226);
if (lean_is_exclusive(x_220)) {
 lean_ctor_release(x_220, 0);
 lean_ctor_release(x_220, 1);
 x_227 = x_220;
} else {
 lean_dec_ref(x_220);
 x_227 = lean_box(0);
}
x_228 = lean_mk_string_unchecked("candidate: ", 11, 11);
x_229 = l_Lean_stringToMessageData(x_228);
lean_dec(x_228);
lean_inc(x_1);
x_230 = l_Lean_MessageData_ofExpr(x_1);
if (lean_is_scalar(x_227)) {
 x_231 = lean_alloc_ctor(7, 2, 0);
} else {
 x_231 = x_227;
 lean_ctor_set_tag(x_231, 7);
}
lean_ctor_set(x_231, 0, x_229);
lean_ctor_set(x_231, 1, x_230);
x_232 = lean_mk_string_unchecked("", 0, 0);
x_233 = l_Lean_stringToMessageData(x_232);
lean_dec(x_232);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_231);
lean_ctor_set(x_234, 1, x_233);
lean_inc(x_85);
x_235 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_85, x_234, x_168, x_169, x_170, x_171, x_226);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_235, 1);
lean_inc(x_237);
lean_dec(x_235);
lean_inc(x_171);
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
lean_inc(x_165);
lean_inc(x_176);
lean_inc(x_85);
x_238 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(x_1, x_85, x_217, x_176, x_236, x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_237);
lean_dec(x_236);
x_149 = x_168;
x_150 = x_174;
x_151 = x_171;
x_152 = x_165;
x_153 = x_170;
x_154 = x_169;
x_155 = x_166;
x_156 = x_167;
x_157 = x_176;
x_158 = x_219;
x_159 = x_238;
goto block_164;
}
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_174);
lean_dec(x_173);
lean_dec(x_171);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_175);
if (x_239 == 0)
{
return x_175;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_175, 0);
x_241 = lean_ctor_get(x_175, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_175);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
}
case 7:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; uint8_t x_273; lean_object* x_274; lean_object* x_281; uint8_t x_290; 
x_269 = lean_ctor_get(x_76, 1);
lean_inc(x_269);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_270 = x_76;
} else {
 lean_dec_ref(x_76);
 x_270 = lean_box(0);
}
x_271 = lean_ctor_get(x_1, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_1, 2);
lean_inc(x_272);
x_290 = l_Lean_Expr_isArrow(x_1);
lean_dec(x_1);
if (x_290 == 0)
{
x_273 = x_290;
x_274 = x_269;
goto block_280;
}
else
{
lean_object* x_291; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_271);
x_291 = l_Lean_Meta_isProp(x_271, x_5, x_6, x_7, x_8, x_269);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; uint8_t x_293; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_unbox(x_292);
lean_dec(x_292);
if (x_293 == 0)
{
x_281 = x_291;
goto block_289;
}
else
{
lean_object* x_294; lean_object* x_295; 
x_294 = lean_ctor_get(x_291, 1);
lean_inc(x_294);
lean_dec(x_291);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_272);
x_295 = l_Lean_Meta_isProp(x_272, x_5, x_6, x_7, x_8, x_294);
x_281 = x_295;
goto block_289;
}
}
else
{
x_281 = x_291;
goto block_289;
}
}
block_280:
{
if (x_273 == 0)
{
lean_object* x_275; lean_object* x_276; 
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_275 = lean_box(0);
if (lean_is_scalar(x_270)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_270;
}
lean_ctor_set(x_276, 0, x_275);
lean_ctor_set(x_276, 1, x_274);
return x_276;
}
else
{
lean_object* x_277; 
lean_dec(x_270);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_277 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_271, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_274);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 1);
lean_inc(x_278);
lean_dec(x_277);
x_1 = x_272;
x_9 = x_278;
goto _start;
}
else
{
lean_dec(x_272);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_277;
}
}
}
block_289:
{
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; uint8_t x_284; 
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_281, 1);
lean_inc(x_283);
lean_dec(x_281);
x_284 = lean_unbox(x_282);
lean_dec(x_282);
x_273 = x_284;
x_274 = x_283;
goto block_280;
}
else
{
uint8_t x_285; 
lean_dec(x_272);
lean_dec(x_271);
lean_dec(x_270);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_285 = !lean_is_exclusive(x_281);
if (x_285 == 0)
{
return x_281;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_286 = lean_ctor_get(x_281, 0);
x_287 = lean_ctor_get(x_281, 1);
lean_inc(x_287);
lean_inc(x_286);
lean_dec(x_281);
x_288 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_288, 0, x_286);
lean_ctor_set(x_288, 1, x_287);
return x_288;
}
}
}
}
default: 
{
uint8_t x_296; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_296 = !lean_is_exclusive(x_76);
if (x_296 == 0)
{
lean_object* x_297; lean_object* x_298; 
x_297 = lean_ctor_get(x_76, 0);
lean_dec(x_297);
x_298 = lean_box(0);
lean_ctor_set(x_76, 0, x_298);
return x_76;
}
else
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; 
x_299 = lean_ctor_get(x_76, 1);
lean_inc(x_299);
lean_dec(x_76);
x_300 = lean_box(0);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_300);
lean_ctor_set(x_301, 1, x_299);
return x_301;
}
}
}
}
else
{
uint8_t x_302; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_302 = !lean_is_exclusive(x_76);
if (x_302 == 0)
{
lean_object* x_303; lean_object* x_304; 
x_303 = lean_ctor_get(x_76, 0);
lean_dec(x_303);
x_304 = lean_box(0);
lean_ctor_set(x_76, 0, x_304);
return x_76;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; 
x_305 = lean_ctor_get(x_76, 1);
lean_inc(x_305);
lean_dec(x_76);
x_306 = lean_box(0);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_306);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
block_42:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; lean_object* x_31; 
x_20 = lean_box(0);
x_21 = l_Lean_Expr_sort___override(x_20);
lean_inc(x_10);
x_22 = lean_mk_array(x_10, x_21);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_sub(x_10, x_23);
lean_dec(x_10);
x_25 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_22, x_24);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_11);
x_28 = l_Array_toSubarray___redArg(x_11, x_26, x_27);
x_29 = lean_array_size(x_25);
x_30 = lean_usize_of_nat(x_26);
x_31 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0(x_25, x_29, x_30, x_28, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
lean_dec(x_25);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
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
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_31);
if (x_38 == 0)
{
return x_31;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
block_58:
{
if (lean_obj_tag(x_52) == 0)
{
lean_dec(x_52);
x_10 = x_44;
x_11 = x_51;
x_12 = x_47;
x_13 = x_50;
x_14 = x_49;
x_15 = x_43;
x_16 = x_48;
x_17 = x_46;
x_18 = x_45;
x_19 = x_53;
goto block_42;
}
else
{
uint8_t x_54; 
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_52);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_52, 1);
lean_dec(x_55);
lean_ctor_set_tag(x_52, 0);
lean_ctor_set(x_52, 1, x_53);
return x_52;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_52, 0);
lean_inc(x_56);
lean_dec(x_52);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_53);
return x_57;
}
}
}
block_75:
{
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_43 = x_59;
x_44 = x_60;
x_45 = x_61;
x_46 = x_63;
x_47 = x_62;
x_48 = x_64;
x_49 = x_66;
x_50 = x_65;
x_51 = x_67;
x_52 = x_69;
x_53 = x_70;
goto block_58;
}
else
{
uint8_t x_71; 
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
lean_dec(x_1);
x_71 = !lean_is_exclusive(x_68);
if (x_71 == 0)
{
return x_68;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_68, 0);
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_68);
x_74 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
return x_74;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_mk_string_unchecked("grind", 5, 5);
x_17 = lean_mk_string_unchecked("debug", 5, 5);
x_18 = lean_mk_string_unchecked("ematch", 6, 6);
x_19 = lean_mk_string_unchecked("pattern", 7, 7);
x_20 = l_Lean_Name_mkStr4(x_16, x_17, x_18, x_19);
lean_inc(x_20);
x_21 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_20, x_10, x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_85; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(0);
lean_ctor_set(x_21, 1, x_25);
lean_ctor_set(x_21, 0, x_15);
x_26 = lean_array_uget(x_1, x_3);
x_85 = lean_unbox(x_23);
lean_dec(x_23);
if (x_85 == 0)
{
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_24;
goto block_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_mk_string_unchecked("place: ", 7, 7);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
lean_inc(x_26);
x_88 = l_Lean_MessageData_ofExpr(x_26);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("", 0, 0);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_20, x_92, x_8, x_9, x_10, x_11, x_24);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_94;
goto block_84;
}
block_84:
{
lean_object* x_35; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
x_35 = l_Lean_Meta_Grind_preprocessPattern(x_26, x_13, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_28);
x_38 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_36, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_get(x_28, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; 
lean_dec(x_28);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_usize_of_nat(x_44);
x_46 = lean_usize_add(x_3, x_45);
x_3 = x_46;
x_4 = x_21;
x_12 = x_43;
goto _start;
}
else
{
uint8_t x_48; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_40, 1);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
x_51 = lean_st_ref_get(x_28, x_49);
lean_dec(x_28);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_array_to_list(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 0, x_57);
lean_ctor_set(x_51, 0, x_40);
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_array_to_list(x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 0, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_40);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec(x_40);
x_66 = lean_st_ref_get(x_28, x_65);
lean_dec(x_28);
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
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_array_to_list(x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_25);
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_38);
if (x_76 == 0)
{
return x_38;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_38, 0);
x_78 = lean_ctor_get(x_38, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_38);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_35);
if (x_80 == 0)
{
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_35, 0);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_35);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_142; 
x_95 = lean_ctor_get(x_21, 0);
x_96 = lean_ctor_get(x_21, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_21);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_15);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_uget(x_1, x_3);
x_142 = lean_unbox(x_95);
lean_dec(x_95);
if (x_142 == 0)
{
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_10;
x_106 = x_11;
x_107 = x_96;
goto block_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_mk_string_unchecked("place: ", 7, 7);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
lean_inc(x_99);
x_145 = l_Lean_MessageData_ofExpr(x_99);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_mk_string_unchecked("", 0, 0);
x_148 = l_Lean_stringToMessageData(x_147);
lean_dec(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_20, x_149, x_8, x_9, x_10, x_11, x_96);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_10;
x_106 = x_11;
x_107 = x_151;
goto block_141;
}
block_141:
{
lean_object* x_108; 
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
x_108 = l_Lean_Meta_Grind_preprocessPattern(x_99, x_13, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_101);
x_111 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_109, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_st_ref_get(x_101, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_114, sizeof(void*)*1);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; 
lean_dec(x_101);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_usize_of_nat(x_117);
x_119 = lean_usize_add(x_3, x_118);
x_3 = x_119;
x_4 = x_98;
x_12 = x_116;
goto _start;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_122 = x_113;
} else {
 lean_dec_ref(x_113);
 x_122 = lean_box(0);
}
x_123 = lean_st_ref_get(x_101, x_121);
lean_dec(x_101);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_array_to_list(x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_122)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_122;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_97);
if (lean_is_scalar(x_126)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_126;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_125);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_133 = lean_ctor_get(x_111, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_111, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_135 = x_111;
} else {
 lean_dec_ref(x_111);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_137 = lean_ctor_get(x_108, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_108, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_139 = x_108;
} else {
 lean_dec_ref(x_108);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_dec(x_4);
x_15 = lean_box(0);
x_16 = lean_mk_string_unchecked("grind", 5, 5);
x_17 = lean_mk_string_unchecked("debug", 5, 5);
x_18 = lean_mk_string_unchecked("ematch", 6, 6);
x_19 = lean_mk_string_unchecked("pattern", 7, 7);
x_20 = l_Lean_Name_mkStr4(x_16, x_17, x_18, x_19);
lean_inc(x_20);
x_21 = l_Lean_isTracingEnabledFor___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__0___redArg(x_20, x_10, x_12);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_85; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_ctor_get(x_21, 1);
x_25 = lean_box(0);
lean_ctor_set(x_21, 1, x_25);
lean_ctor_set(x_21, 0, x_15);
x_26 = lean_array_uget(x_1, x_3);
x_85 = lean_unbox(x_23);
lean_dec(x_23);
if (x_85 == 0)
{
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_24;
goto block_84;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_86 = lean_mk_string_unchecked("place: ", 7, 7);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
lean_inc(x_26);
x_88 = l_Lean_MessageData_ofExpr(x_26);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("", 0, 0);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_20, x_92, x_8, x_9, x_10, x_11, x_24);
x_94 = lean_ctor_get(x_93, 1);
lean_inc(x_94);
lean_dec(x_93);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_27 = x_5;
x_28 = x_6;
x_29 = x_7;
x_30 = x_8;
x_31 = x_9;
x_32 = x_10;
x_33 = x_11;
x_34 = x_94;
goto block_84;
}
block_84:
{
lean_object* x_35; 
lean_inc(x_33);
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
x_35 = l_Lean_Meta_Grind_preprocessPattern(x_26, x_13, x_30, x_31, x_32, x_33, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_28);
x_38 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_36, x_27, x_28, x_29, x_30, x_31, x_32, x_33, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_st_ref_get(x_28, x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get_uint8(x_41, sizeof(void*)*1);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; size_t x_45; size_t x_46; lean_object* x_47; 
lean_dec(x_28);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_usize_of_nat(x_44);
x_46 = lean_usize_add(x_3, x_45);
x_47 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0_spec__0(x_1, x_2, x_46, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_43);
return x_47;
}
else
{
uint8_t x_48; 
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_40);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_49 = lean_ctor_get(x_40, 1);
x_50 = lean_ctor_get(x_40, 0);
lean_dec(x_50);
x_51 = lean_st_ref_get(x_28, x_49);
lean_dec(x_28);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
lean_dec(x_53);
x_55 = lean_array_to_list(x_54);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 0, x_57);
lean_ctor_set(x_51, 0, x_40);
return x_51;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_ctor_get(x_51, 0);
x_59 = lean_ctor_get(x_51, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_51);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_array_to_list(x_60);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_40, 1, x_25);
lean_ctor_set(x_40, 0, x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_40);
lean_ctor_set(x_64, 1, x_59);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_65 = lean_ctor_get(x_40, 1);
lean_inc(x_65);
lean_dec(x_40);
x_66 = lean_st_ref_get(x_28, x_65);
lean_dec(x_28);
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
x_70 = lean_ctor_get(x_67, 0);
lean_inc(x_70);
lean_dec(x_67);
x_71 = lean_array_to_list(x_70);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_73 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_73, 0, x_72);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_25);
if (lean_is_scalar(x_69)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_69;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_68);
return x_75;
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_28);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_76 = !lean_is_exclusive(x_38);
if (x_76 == 0)
{
return x_38;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_38, 0);
x_78 = lean_ctor_get(x_38, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_38);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
uint8_t x_80; 
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_21);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_80 = !lean_is_exclusive(x_35);
if (x_80 == 0)
{
return x_35;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_81 = lean_ctor_get(x_35, 0);
x_82 = lean_ctor_get(x_35, 1);
lean_inc(x_82);
lean_inc(x_81);
lean_dec(x_35);
x_83 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_82);
return x_83;
}
}
}
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_142; 
x_95 = lean_ctor_get(x_21, 0);
x_96 = lean_ctor_get(x_21, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_21);
x_97 = lean_box(0);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_15);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_array_uget(x_1, x_3);
x_142 = lean_unbox(x_95);
lean_dec(x_95);
if (x_142 == 0)
{
lean_dec(x_20);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_10;
x_106 = x_11;
x_107 = x_96;
goto block_141;
}
else
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
x_143 = lean_mk_string_unchecked("place: ", 7, 7);
x_144 = l_Lean_stringToMessageData(x_143);
lean_dec(x_143);
lean_inc(x_99);
x_145 = l_Lean_MessageData_ofExpr(x_99);
x_146 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_146, 0, x_144);
lean_ctor_set(x_146, 1, x_145);
x_147 = lean_mk_string_unchecked("", 0, 0);
x_148 = l_Lean_stringToMessageData(x_147);
lean_dec(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_146);
lean_ctor_set(x_149, 1, x_148);
x_150 = l_Lean_addTrace___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addNewPattern_spec__1___redArg(x_20, x_149, x_8, x_9, x_10, x_11, x_96);
x_151 = lean_ctor_get(x_150, 1);
lean_inc(x_151);
lean_dec(x_150);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_100 = x_5;
x_101 = x_6;
x_102 = x_7;
x_103 = x_8;
x_104 = x_9;
x_105 = x_10;
x_106 = x_11;
x_107 = x_151;
goto block_141;
}
block_141:
{
lean_object* x_108; 
lean_inc(x_106);
lean_inc(x_105);
lean_inc(x_104);
lean_inc(x_103);
x_108 = l_Lean_Meta_Grind_preprocessPattern(x_99, x_13, x_103, x_104, x_105, x_106, x_107);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
lean_inc(x_101);
x_111 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collect(x_109, x_100, x_101, x_102, x_103, x_104, x_105, x_106, x_110);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
lean_dec(x_111);
x_113 = lean_st_ref_get(x_101, x_112);
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get_uint8(x_114, sizeof(void*)*1);
lean_dec(x_114);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; size_t x_118; size_t x_119; lean_object* x_120; 
lean_dec(x_101);
x_116 = lean_ctor_get(x_113, 1);
lean_inc(x_116);
lean_dec(x_113);
x_117 = lean_unsigned_to_nat(1u);
x_118 = lean_usize_of_nat(x_117);
x_119 = lean_usize_add(x_3, x_118);
x_120 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0_spec__0(x_1, x_2, x_119, x_98, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_116);
return x_120;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; 
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_121 = lean_ctor_get(x_113, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_122 = x_113;
} else {
 lean_dec_ref(x_113);
 x_122 = lean_box(0);
}
x_123 = lean_st_ref_get(x_101, x_121);
lean_dec(x_101);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_126 = x_123;
} else {
 lean_dec_ref(x_123);
 x_126 = lean_box(0);
}
x_127 = lean_ctor_get(x_124, 0);
lean_inc(x_127);
lean_dec(x_124);
x_128 = lean_array_to_list(x_127);
x_129 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_129, 0, x_128);
x_130 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_130, 0, x_129);
if (lean_is_scalar(x_122)) {
 x_131 = lean_alloc_ctor(0, 2, 0);
} else {
 x_131 = x_122;
}
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_97);
if (lean_is_scalar(x_126)) {
 x_132 = lean_alloc_ctor(0, 2, 0);
} else {
 x_132 = x_126;
}
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_125);
return x_132;
}
}
else
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_101);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_133 = lean_ctor_get(x_111, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_111, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_135 = x_111;
} else {
 lean_dec_ref(x_111);
 x_135 = lean_box(0);
}
if (lean_is_scalar(x_135)) {
 x_136 = lean_alloc_ctor(1, 2, 0);
} else {
 x_136 = x_135;
}
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_134);
return x_136;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_137 = lean_ctor_get(x_108, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_108, 1);
lean_inc(x_138);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_139 = x_108;
} else {
 lean_dec_ref(x_108);
 x_139 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_140 = lean_alloc_ctor(1, 2, 0);
} else {
 x_140 = x_139;
}
lean_ctor_set(x_140, 0, x_137);
lean_ctor_set(x_140, 1, x_138);
return x_140;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
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
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_9);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_box(0);
x_21 = lean_mk_array(x_16, x_20);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_9);
lean_ctor_set(x_22, 1, x_21);
lean_inc(x_10);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_19);
lean_ctor_set(x_23, 2, x_22);
x_24 = lean_st_mk_ref(x_23, x_8);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_29, 0, x_10);
x_30 = lean_unbox(x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*1, x_30);
x_31 = lean_st_mk_ref(x_29, x_27);
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; lean_object* x_39; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = lean_ctor_get(x_31, 1);
x_35 = lean_box(0);
x_36 = lean_box(0);
lean_ctor_set(x_31, 1, x_36);
lean_ctor_set(x_31, 0, x_35);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 0, x_1);
x_37 = lean_array_size(x_3);
x_38 = lean_usize_of_nat(x_9);
lean_inc(x_26);
lean_inc(x_33);
x_39 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0(x_3, x_37, x_38, x_31, x_24, x_33, x_26, x_4, x_5, x_6, x_7, x_34);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_90; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_90 = lean_ctor_get(x_40, 0);
lean_inc(x_90);
lean_dec(x_40);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_91; 
x_91 = lean_box(0);
x_42 = x_91;
goto block_89;
}
else
{
lean_object* x_92; 
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_dec(x_90);
x_42 = x_92;
goto block_89;
}
block_89:
{
lean_object* x_43; uint8_t x_44; 
x_43 = lean_st_ref_get(x_33, x_41);
lean_dec(x_33);
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_43, 1);
x_46 = lean_ctor_get(x_43, 0);
lean_dec(x_46);
x_47 = lean_st_ref_get(x_26, x_45);
lean_dec(x_26);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_48; 
lean_free_object(x_43);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_47, 0);
lean_dec(x_49);
x_50 = lean_box(0);
lean_ctor_set(x_47, 0, x_50);
return x_47;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_47, 1);
lean_inc(x_51);
lean_dec(x_47);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_51);
return x_53;
}
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_47);
if (x_54 == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_42);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_56 = lean_ctor_get(x_47, 0);
x_57 = lean_ctor_get(x_42, 0);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec(x_56);
x_59 = lean_array_to_list(x_58);
lean_ctor_set(x_43, 1, x_59);
lean_ctor_set(x_43, 0, x_57);
lean_ctor_set(x_42, 0, x_43);
lean_ctor_set(x_47, 0, x_42);
return x_47;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_60 = lean_ctor_get(x_47, 0);
x_61 = lean_ctor_get(x_42, 0);
lean_inc(x_61);
lean_dec(x_42);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_array_to_list(x_62);
lean_ctor_set(x_43, 1, x_63);
lean_ctor_set(x_43, 0, x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_43);
lean_ctor_set(x_47, 0, x_64);
return x_47;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_47, 0);
x_66 = lean_ctor_get(x_47, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_47);
x_67 = lean_ctor_get(x_42, 0);
lean_inc(x_67);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_68 = x_42;
} else {
 lean_dec_ref(x_42);
 x_68 = lean_box(0);
}
x_69 = lean_ctor_get(x_65, 0);
lean_inc(x_69);
lean_dec(x_65);
x_70 = lean_array_to_list(x_69);
lean_ctor_set(x_43, 1, x_70);
lean_ctor_set(x_43, 0, x_67);
if (lean_is_scalar(x_68)) {
 x_71 = lean_alloc_ctor(1, 1, 0);
} else {
 x_71 = x_68;
}
lean_ctor_set(x_71, 0, x_43);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_43, 1);
lean_inc(x_73);
lean_dec(x_43);
x_74 = lean_st_ref_get(x_26, x_73);
lean_dec(x_26);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_74, 1);
lean_inc(x_75);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_76 = x_74;
} else {
 lean_dec_ref(x_74);
 x_76 = lean_box(0);
}
x_77 = lean_box(0);
if (lean_is_scalar(x_76)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_76;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_75);
return x_78;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_79 = lean_ctor_get(x_74, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_74, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_74)) {
 lean_ctor_release(x_74, 0);
 lean_ctor_release(x_74, 1);
 x_81 = x_74;
} else {
 lean_dec_ref(x_74);
 x_81 = lean_box(0);
}
x_82 = lean_ctor_get(x_42, 0);
lean_inc(x_82);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_83 = x_42;
} else {
 lean_dec_ref(x_42);
 x_83 = lean_box(0);
}
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
lean_dec(x_79);
x_85 = lean_array_to_list(x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_82);
lean_ctor_set(x_86, 1, x_85);
if (lean_is_scalar(x_83)) {
 x_87 = lean_alloc_ctor(1, 1, 0);
} else {
 x_87 = x_83;
}
lean_ctor_set(x_87, 0, x_86);
if (lean_is_scalar(x_81)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_81;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_80);
return x_88;
}
}
}
}
else
{
uint8_t x_93; 
lean_dec(x_33);
lean_dec(x_26);
x_93 = !lean_is_exclusive(x_39);
if (x_93 == 0)
{
return x_39;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_39, 0);
x_95 = lean_ctor_get(x_39, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_39);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; size_t x_102; size_t x_103; lean_object* x_104; 
x_97 = lean_ctor_get(x_31, 0);
x_98 = lean_ctor_get(x_31, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_31);
x_99 = lean_box(0);
x_100 = lean_box(0);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_24, 1, x_2);
lean_ctor_set(x_24, 0, x_1);
x_102 = lean_array_size(x_3);
x_103 = lean_usize_of_nat(x_9);
lean_inc(x_26);
lean_inc(x_97);
x_104 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0(x_3, x_102, x_103, x_101, x_24, x_97, x_26, x_4, x_5, x_6, x_7, x_98);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_127; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_127 = lean_ctor_get(x_105, 0);
lean_inc(x_127);
lean_dec(x_105);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; 
x_128 = lean_box(0);
x_107 = x_128;
goto block_126;
}
else
{
lean_object* x_129; 
x_129 = lean_ctor_get(x_127, 0);
lean_inc(x_129);
lean_dec(x_127);
x_107 = x_129;
goto block_126;
}
block_126:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_108 = lean_st_ref_get(x_97, x_106);
lean_dec(x_97);
x_109 = lean_ctor_get(x_108, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_110 = x_108;
} else {
 lean_dec_ref(x_108);
 x_110 = lean_box(0);
}
x_111 = lean_st_ref_get(x_26, x_109);
lean_dec(x_26);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_110);
x_112 = lean_ctor_get(x_111, 1);
lean_inc(x_112);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_113 = x_111;
} else {
 lean_dec_ref(x_111);
 x_113 = lean_box(0);
}
x_114 = lean_box(0);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
x_116 = lean_ctor_get(x_111, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_111, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_118 = x_111;
} else {
 lean_dec_ref(x_111);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_107, 0);
lean_inc(x_119);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 x_120 = x_107;
} else {
 lean_dec_ref(x_107);
 x_120 = lean_box(0);
}
x_121 = lean_ctor_get(x_116, 0);
lean_inc(x_121);
lean_dec(x_116);
x_122 = lean_array_to_list(x_121);
if (lean_is_scalar(x_110)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_110;
}
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
if (lean_is_scalar(x_120)) {
 x_124 = lean_alloc_ctor(1, 1, 0);
} else {
 x_124 = x_120;
}
lean_ctor_set(x_124, 0, x_123);
if (lean_is_scalar(x_118)) {
 x_125 = lean_alloc_ctor(0, 2, 0);
} else {
 x_125 = x_118;
}
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_117);
return x_125;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_97);
lean_dec(x_26);
x_130 = lean_ctor_get(x_104, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_104, 1);
lean_inc(x_131);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_132 = x_104;
} else {
 lean_dec_ref(x_104);
 x_132 = lean_box(0);
}
if (lean_is_scalar(x_132)) {
 x_133 = lean_alloc_ctor(1, 2, 0);
} else {
 x_133 = x_132;
}
lean_ctor_set(x_133, 0, x_130);
lean_ctor_set(x_133, 1, x_131);
return x_133;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; size_t x_147; size_t x_148; lean_object* x_149; 
x_134 = lean_ctor_get(x_24, 0);
x_135 = lean_ctor_get(x_24, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_24);
x_136 = lean_box(0);
x_137 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_137, 0, x_10);
x_138 = lean_unbox(x_136);
lean_ctor_set_uint8(x_137, sizeof(void*)*1, x_138);
x_139 = lean_st_mk_ref(x_137, x_135);
x_140 = lean_ctor_get(x_139, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_139, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_139)) {
 lean_ctor_release(x_139, 0);
 lean_ctor_release(x_139, 1);
 x_142 = x_139;
} else {
 lean_dec_ref(x_139);
 x_142 = lean_box(0);
}
x_143 = lean_box(0);
x_144 = lean_box(0);
if (lean_is_scalar(x_142)) {
 x_145 = lean_alloc_ctor(0, 2, 0);
} else {
 x_145 = x_142;
}
lean_ctor_set(x_145, 0, x_143);
lean_ctor_set(x_145, 1, x_144);
x_146 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_146, 0, x_1);
lean_ctor_set(x_146, 1, x_2);
x_147 = lean_array_size(x_3);
x_148 = lean_usize_of_nat(x_9);
lean_inc(x_134);
lean_inc(x_140);
x_149 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0(x_3, x_147, x_148, x_145, x_146, x_140, x_134, x_4, x_5, x_6, x_7, x_141);
if (lean_obj_tag(x_149) == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_172; 
x_150 = lean_ctor_get(x_149, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_149, 1);
lean_inc(x_151);
lean_dec(x_149);
x_172 = lean_ctor_get(x_150, 0);
lean_inc(x_172);
lean_dec(x_150);
if (lean_obj_tag(x_172) == 0)
{
lean_object* x_173; 
x_173 = lean_box(0);
x_152 = x_173;
goto block_171;
}
else
{
lean_object* x_174; 
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_152 = x_174;
goto block_171;
}
block_171:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_st_ref_get(x_140, x_151);
lean_dec(x_140);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_155 = x_153;
} else {
 lean_dec_ref(x_153);
 x_155 = lean_box(0);
}
x_156 = lean_st_ref_get(x_134, x_154);
lean_dec(x_134);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_155);
x_157 = lean_ctor_get(x_156, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_158 = x_156;
} else {
 lean_dec_ref(x_156);
 x_158 = lean_box(0);
}
x_159 = lean_box(0);
if (lean_is_scalar(x_158)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_158;
}
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_157);
return x_160;
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_161 = lean_ctor_get(x_156, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_156, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_163 = x_156;
} else {
 lean_dec_ref(x_156);
 x_163 = lean_box(0);
}
x_164 = lean_ctor_get(x_152, 0);
lean_inc(x_164);
if (lean_is_exclusive(x_152)) {
 lean_ctor_release(x_152, 0);
 x_165 = x_152;
} else {
 lean_dec_ref(x_152);
 x_165 = lean_box(0);
}
x_166 = lean_ctor_get(x_161, 0);
lean_inc(x_166);
lean_dec(x_161);
x_167 = lean_array_to_list(x_166);
if (lean_is_scalar(x_155)) {
 x_168 = lean_alloc_ctor(0, 2, 0);
} else {
 x_168 = x_155;
}
lean_ctor_set(x_168, 0, x_164);
lean_ctor_set(x_168, 1, x_167);
if (lean_is_scalar(x_165)) {
 x_169 = lean_alloc_ctor(1, 1, 0);
} else {
 x_169 = x_165;
}
lean_ctor_set(x_169, 0, x_168);
if (lean_is_scalar(x_163)) {
 x_170 = lean_alloc_ctor(0, 2, 0);
} else {
 x_170 = x_163;
}
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_162);
return x_170;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_140);
lean_dec(x_134);
x_175 = lean_ctor_get(x_149, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_149, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_149)) {
 lean_ctor_release(x_149, 0);
 lean_ctor_release(x_149, 1);
 x_177 = x_149;
} else {
 lean_dec_ref(x_149);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_177)) {
 x_178 = lean_alloc_ctor(1, 2, 0);
} else {
 x_178 = x_177;
}
lean_ctor_set(x_178, 0, x_175);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_3, x_2);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_box(0);
x_23 = lean_ctor_get(x_4, 1);
lean_inc(x_23);
lean_dec(x_4);
x_24 = lean_ctor_get(x_23, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_22);
lean_ctor_set(x_27, 1, x_23);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_12);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
x_30 = lean_array_fget(x_29, x_24);
x_31 = lean_unbox(x_30);
lean_dec(x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_24, x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_25);
x_35 = l_Lean_Meta_Grind_NormalizePattern_PatternArgKind_isSupport(x_31);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_array_uget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_37 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f(x_36, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; 
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_22);
lean_ctor_set(x_40, 1, x_34);
x_13 = x_40;
x_14 = x_39;
goto block_19;
}
else
{
uint8_t x_41; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_41 = !lean_is_exclusive(x_37);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_37, 0);
lean_dec(x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_38);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_34);
lean_ctor_set(x_37, 0, x_44);
return x_37;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_37, 1);
lean_inc(x_45);
lean_dec(x_37);
x_46 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_46, 0, x_38);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_34);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_45);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_34);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_49 = !lean_is_exclusive(x_37);
if (x_49 == 0)
{
return x_37;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_37, 0);
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_37);
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
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_22);
lean_ctor_set(x_53, 1, x_34);
x_13 = x_53;
x_14 = x_12;
goto block_19;
}
}
}
block_19:
{
lean_object* x_15; size_t x_16; size_t x_17; 
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_13;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = l_Lean_Expr_getAppFn(x_1);
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_isPatternFnCandidate___redArg(x_10, x_2, x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_unbox(x_12);
lean_dec(x_12);
if (x_13 == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_11);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_15 = lean_ctor_get(x_11, 1);
x_16 = lean_ctor_get(x_11, 0);
lean_dec(x_16);
x_17 = lean_box(0);
x_18 = l_Lean_Expr_sort___override(x_17);
x_19 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_19);
x_20 = lean_mk_array(x_19, x_18);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_sub(x_19, x_21);
lean_dec(x_19);
x_23 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_20, x_22);
x_24 = lean_array_get_size(x_23);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_25 = l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(x_10, x_24, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_unsigned_to_nat(0u);
x_29 = lean_array_get_size(x_26);
x_30 = l_Array_toSubarray___redArg(x_26, x_28, x_29);
x_31 = lean_box(0);
lean_ctor_set(x_11, 1, x_30);
lean_ctor_set(x_11, 0, x_31);
x_32 = lean_array_size(x_23);
x_33 = lean_usize_of_nat(x_28);
x_34 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f_spec__0(x_23, x_32, x_33, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_23);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
lean_dec(x_35);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_34);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_34, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_34, 0, x_39);
return x_34;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_34, 1);
lean_inc(x_40);
lean_dec(x_34);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
else
{
uint8_t x_43; 
x_43 = !lean_is_exclusive(x_34);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_34, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
lean_dec(x_36);
lean_ctor_set(x_34, 0, x_45);
return x_34;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_34, 1);
lean_inc(x_46);
lean_dec(x_34);
x_47 = lean_ctor_get(x_36, 0);
lean_inc(x_47);
lean_dec(x_36);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_34);
if (x_49 == 0)
{
return x_34;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_34, 0);
x_51 = lean_ctor_get(x_34, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_34);
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
lean_dec(x_23);
lean_free_object(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_53 = !lean_is_exclusive(x_25);
if (x_53 == 0)
{
return x_25;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_25, 0);
x_55 = lean_ctor_get(x_25, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_25);
x_56 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_56, 0, x_54);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_57 = lean_ctor_get(x_11, 1);
lean_inc(x_57);
lean_dec(x_11);
x_58 = lean_box(0);
x_59 = l_Lean_Expr_sort___override(x_58);
x_60 = l_Lean_Expr_getAppNumArgs(x_1);
lean_inc(x_60);
x_61 = lean_mk_array(x_60, x_59);
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_sub(x_60, x_62);
lean_dec(x_60);
x_64 = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(x_1, x_61, x_63);
x_65 = lean_array_get_size(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_66 = l_Lean_Meta_Grind_NormalizePattern_getPatternArgKinds(x_10, x_65, x_5, x_6, x_7, x_8, x_57);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; size_t x_74; size_t x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_array_get_size(x_67);
x_71 = l_Array_toSubarray___redArg(x_67, x_69, x_70);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
x_74 = lean_array_size(x_64);
x_75 = lean_usize_of_nat(x_69);
x_76 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f_spec__0(x_64, x_74, x_75, x_73, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_68);
lean_dec(x_64);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec(x_77);
if (lean_obj_tag(x_78) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_80 = x_76;
} else {
 lean_dec_ref(x_76);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_83 = lean_ctor_get(x_76, 1);
lean_inc(x_83);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_84 = x_76;
} else {
 lean_dec_ref(x_76);
 x_84 = lean_box(0);
}
x_85 = lean_ctor_get(x_78, 0);
lean_inc(x_85);
lean_dec(x_78);
if (lean_is_scalar(x_84)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_84;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_83);
return x_86;
}
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_76, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_76, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_89 = x_76;
} else {
 lean_dec_ref(x_76);
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
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
lean_dec(x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_91 = lean_ctor_get(x_66, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_66, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_93 = x_66;
} else {
 lean_dec_ref(x_66);
 x_93 = lean_box(0);
}
if (lean_is_scalar(x_93)) {
 x_94 = lean_alloc_ctor(1, 2, 0);
} else {
 x_94 = x_93;
}
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_92);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
lean_dec(x_10);
x_95 = lean_ctor_get(x_11, 1);
lean_inc(x_95);
lean_dec(x_11);
x_96 = l_Lean_Meta_Grind_NormalizePattern_normalizePattern(x_1, x_4, x_5, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_96) == 0)
{
uint8_t x_97; 
x_97 = !lean_is_exclusive(x_96);
if (x_97 == 0)
{
lean_object* x_98; lean_object* x_99; 
x_98 = lean_ctor_get(x_96, 0);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_96, 0, x_99);
return x_96;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_96, 0);
x_101 = lean_ctor_get(x_96, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_96);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_100);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_101);
return x_103;
}
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_96);
if (x_104 == 0)
{
return x_96;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_96, 0);
x_106 = lean_ctor_get(x_96, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_96);
x_107 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
return x_107;
}
}
}
}
case 7:
{
lean_object* x_108; lean_object* x_109; uint8_t x_110; lean_object* x_111; lean_object* x_119; uint8_t x_128; 
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
x_109 = lean_ctor_get(x_1, 2);
lean_inc(x_109);
x_128 = l_Lean_Expr_isArrow(x_1);
lean_dec(x_1);
if (x_128 == 0)
{
x_110 = x_128;
x_111 = x_9;
goto block_118;
}
else
{
lean_object* x_129; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_108);
x_129 = l_Lean_Meta_isProp(x_108, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; uint8_t x_131; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_unbox(x_130);
lean_dec(x_130);
if (x_131 == 0)
{
x_119 = x_129;
goto block_127;
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_129, 1);
lean_inc(x_132);
lean_dec(x_129);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_109);
x_133 = l_Lean_Meta_isProp(x_109, x_5, x_6, x_7, x_8, x_132);
x_119 = x_133;
goto block_127;
}
}
else
{
x_119 = x_129;
goto block_127;
}
}
block_118:
{
if (x_110 == 0)
{
lean_object* x_112; lean_object* x_113; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
else
{
lean_object* x_114; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_114 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f(x_108, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_111);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_1 = x_109;
x_9 = x_116;
goto _start;
}
else
{
lean_dec(x_115);
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_114;
}
}
else
{
lean_dec(x_109);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_114;
}
}
}
block_127:
{
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_unbox(x_120);
lean_dec(x_120);
x_110 = x_122;
x_111 = x_121;
goto block_118;
}
else
{
uint8_t x_123; 
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_123 = !lean_is_exclusive(x_119);
if (x_123 == 0)
{
return x_119;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_124 = lean_ctor_get(x_119, 0);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
lean_inc(x_124);
lean_dec(x_119);
x_126 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_126, 0, x_124);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
}
default: 
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_134 = lean_box(0);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_9);
return x_135;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_16 = l_Lean_Meta_Grind_preprocessPattern(x_15, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_19 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_visit_x3f(x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_box(0);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; size_t x_28; 
lean_free_object(x_19);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_add(x_3, x_27);
x_3 = x_28;
x_4 = x_25;
x_12 = x_22;
goto _start;
}
else
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_30, 0, x_21);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_23);
lean_ctor_set(x_19, 0, x_31);
return x_19;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_19, 0);
x_33 = lean_ctor_get(x_19, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_19);
x_34 = lean_box(0);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; size_t x_39; 
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_add(x_3, x_38);
x_3 = x_39;
x_4 = x_36;
x_12 = x_33;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_34);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_33);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_19);
if (x_44 == 0)
{
return x_19;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_19, 0);
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_19);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_48 = !lean_is_exclusive(x_16);
if (x_48 == 0)
{
return x_16;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_16, 0);
x_50 = lean_ctor_get(x_16, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_16);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_unsigned_to_nat(8u);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_unsigned_to_nat(2u);
x_13 = lean_nat_shiftl(x_10, x_12);
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_nat_div(x_13, x_14);
lean_dec(x_13);
x_16 = l_Nat_nextPowerOfTwo(x_15);
lean_dec(x_15);
x_17 = lean_box(0);
lean_inc(x_16);
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_19);
lean_inc(x_1);
x_20 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_checkCoverage(x_1, x_9, x_19, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_mk_empty_array_with_capacity(x_11);
x_24 = lean_box(0);
x_25 = lean_mk_array(x_16, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_11);
lean_ctor_set(x_26, 1, x_25);
lean_inc(x_23);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_19);
x_28 = lean_st_mk_ref(x_27, x_22);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_35; uint8_t x_36; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_ctor_get(x_28, 1);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_33, 0, x_23);
x_34 = lean_unbox(x_32);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_34);
x_35 = lean_st_mk_ref(x_33, x_31);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_box(0);
x_40 = lean_box(0);
lean_ctor_set(x_35, 1, x_40);
lean_ctor_set(x_35, 0, x_39);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 0, x_1);
x_41 = lean_array_size(x_3);
x_42 = lean_usize_of_nat(x_11);
lean_inc(x_30);
x_43 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0(x_3, x_41, x_42, x_35, x_28, x_37, x_30, x_4, x_5, x_6, x_7, x_38);
lean_dec(x_28);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_94; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_94 = lean_ctor_get(x_44, 0);
lean_inc(x_94);
lean_dec(x_44);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; 
x_95 = lean_box(0);
x_46 = x_95;
goto block_93;
}
else
{
lean_object* x_96; 
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
lean_dec(x_94);
x_46 = x_96;
goto block_93;
}
block_93:
{
lean_object* x_47; uint8_t x_48; 
x_47 = lean_st_ref_get(x_37, x_45);
lean_dec(x_37);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = lean_st_ref_get(x_30, x_49);
lean_dec(x_30);
if (lean_obj_tag(x_46) == 0)
{
uint8_t x_52; 
lean_free_object(x_47);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_46);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_46, 0);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_array_to_list(x_62);
lean_ctor_set(x_47, 1, x_63);
lean_ctor_set(x_47, 0, x_61);
lean_ctor_set(x_46, 0, x_47);
lean_ctor_set(x_51, 0, x_46);
return x_51;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_51, 0);
x_65 = lean_ctor_get(x_46, 0);
lean_inc(x_65);
lean_dec(x_46);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_array_to_list(x_66);
lean_ctor_set(x_47, 1, x_67);
lean_ctor_set(x_47, 0, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_47);
lean_ctor_set(x_51, 0, x_68);
return x_51;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_69 = lean_ctor_get(x_51, 0);
x_70 = lean_ctor_get(x_51, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_51);
x_71 = lean_ctor_get(x_46, 0);
lean_inc(x_71);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_72 = x_46;
} else {
 lean_dec_ref(x_46);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec(x_69);
x_74 = lean_array_to_list(x_73);
lean_ctor_set(x_47, 1, x_74);
lean_ctor_set(x_47, 0, x_71);
if (lean_is_scalar(x_72)) {
 x_75 = lean_alloc_ctor(1, 1, 0);
} else {
 x_75 = x_72;
}
lean_ctor_set(x_75, 0, x_47);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_70);
return x_76;
}
}
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_47, 1);
lean_inc(x_77);
lean_dec(x_47);
x_78 = lean_st_ref_get(x_30, x_77);
lean_dec(x_30);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
x_81 = lean_box(0);
if (lean_is_scalar(x_80)) {
 x_82 = lean_alloc_ctor(0, 2, 0);
} else {
 x_82 = x_80;
}
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_79);
return x_82;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_83 = lean_ctor_get(x_78, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_78, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_85 = x_78;
} else {
 lean_dec_ref(x_78);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_46, 0);
lean_inc(x_86);
if (lean_is_exclusive(x_46)) {
 lean_ctor_release(x_46, 0);
 x_87 = x_46;
} else {
 lean_dec_ref(x_46);
 x_87 = lean_box(0);
}
x_88 = lean_ctor_get(x_83, 0);
lean_inc(x_88);
lean_dec(x_83);
x_89 = lean_array_to_list(x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_86);
lean_ctor_set(x_90, 1, x_89);
if (lean_is_scalar(x_87)) {
 x_91 = lean_alloc_ctor(1, 1, 0);
} else {
 x_91 = x_87;
}
lean_ctor_set(x_91, 0, x_90);
if (lean_is_scalar(x_85)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_85;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_84);
return x_92;
}
}
}
}
else
{
uint8_t x_97; 
lean_dec(x_37);
lean_dec(x_30);
x_97 = !lean_is_exclusive(x_43);
if (x_97 == 0)
{
return x_43;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_43, 0);
x_99 = lean_ctor_get(x_43, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_43);
x_100 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_100, 0, x_98);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; size_t x_106; size_t x_107; lean_object* x_108; 
x_101 = lean_ctor_get(x_35, 0);
x_102 = lean_ctor_get(x_35, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_35);
x_103 = lean_box(0);
x_104 = lean_box(0);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_28, 0, x_1);
x_106 = lean_array_size(x_3);
x_107 = lean_usize_of_nat(x_11);
lean_inc(x_30);
x_108 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0(x_3, x_106, x_107, x_105, x_28, x_101, x_30, x_4, x_5, x_6, x_7, x_102);
lean_dec(x_28);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_131; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_131 = lean_ctor_get(x_109, 0);
lean_inc(x_131);
lean_dec(x_109);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; 
x_132 = lean_box(0);
x_111 = x_132;
goto block_130;
}
else
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_dec(x_131);
x_111 = x_133;
goto block_130;
}
block_130:
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_112 = lean_st_ref_get(x_101, x_110);
lean_dec(x_101);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_114 = x_112;
} else {
 lean_dec_ref(x_112);
 x_114 = lean_box(0);
}
x_115 = lean_st_ref_get(x_30, x_113);
lean_dec(x_30);
if (lean_obj_tag(x_111) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_114);
x_116 = lean_ctor_get(x_115, 1);
lean_inc(x_116);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_117 = x_115;
} else {
 lean_dec_ref(x_115);
 x_117 = lean_box(0);
}
x_118 = lean_box(0);
if (lean_is_scalar(x_117)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_117;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_116);
return x_119;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_120 = lean_ctor_get(x_115, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_115, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_122 = x_115;
} else {
 lean_dec_ref(x_115);
 x_122 = lean_box(0);
}
x_123 = lean_ctor_get(x_111, 0);
lean_inc(x_123);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 x_124 = x_111;
} else {
 lean_dec_ref(x_111);
 x_124 = lean_box(0);
}
x_125 = lean_ctor_get(x_120, 0);
lean_inc(x_125);
lean_dec(x_120);
x_126 = lean_array_to_list(x_125);
if (lean_is_scalar(x_114)) {
 x_127 = lean_alloc_ctor(0, 2, 0);
} else {
 x_127 = x_114;
}
lean_ctor_set(x_127, 0, x_123);
lean_ctor_set(x_127, 1, x_126);
if (lean_is_scalar(x_124)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_124;
}
lean_ctor_set(x_128, 0, x_127);
if (lean_is_scalar(x_122)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_122;
}
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_121);
return x_129;
}
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_101);
lean_dec(x_30);
x_134 = lean_ctor_get(x_108, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_108, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_108)) {
 lean_ctor_release(x_108, 0);
 lean_ctor_release(x_108, 1);
 x_136 = x_108;
} else {
 lean_dec_ref(x_108);
 x_136 = lean_box(0);
}
if (lean_is_scalar(x_136)) {
 x_137 = lean_alloc_ctor(1, 2, 0);
} else {
 x_137 = x_136;
}
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_135);
return x_137;
}
}
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; size_t x_151; size_t x_152; lean_object* x_153; 
x_138 = lean_ctor_get(x_28, 0);
x_139 = lean_ctor_get(x_28, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_28);
x_140 = lean_box(0);
x_141 = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(x_141, 0, x_23);
x_142 = lean_unbox(x_140);
lean_ctor_set_uint8(x_141, sizeof(void*)*1, x_142);
x_143 = lean_st_mk_ref(x_141, x_139);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_146 = x_143;
} else {
 lean_dec_ref(x_143);
 x_146 = lean_box(0);
}
x_147 = lean_box(0);
x_148 = lean_box(0);
if (lean_is_scalar(x_146)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_146;
}
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_1);
lean_ctor_set(x_150, 1, x_2);
x_151 = lean_array_size(x_3);
x_152 = lean_usize_of_nat(x_11);
lean_inc(x_138);
x_153 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0(x_3, x_151, x_152, x_149, x_150, x_144, x_138, x_4, x_5, x_6, x_7, x_145);
lean_dec(x_150);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_176; 
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
lean_dec(x_153);
x_176 = lean_ctor_get(x_154, 0);
lean_inc(x_176);
lean_dec(x_154);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; 
x_177 = lean_box(0);
x_156 = x_177;
goto block_175;
}
else
{
lean_object* x_178; 
x_178 = lean_ctor_get(x_176, 0);
lean_inc(x_178);
lean_dec(x_176);
x_156 = x_178;
goto block_175;
}
block_175:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_157 = lean_st_ref_get(x_144, x_155);
lean_dec(x_144);
x_158 = lean_ctor_get(x_157, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_159 = x_157;
} else {
 lean_dec_ref(x_157);
 x_159 = lean_box(0);
}
x_160 = lean_st_ref_get(x_138, x_158);
lean_dec(x_138);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_159);
x_161 = lean_ctor_get(x_160, 1);
lean_inc(x_161);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_162 = x_160;
} else {
 lean_dec_ref(x_160);
 x_162 = lean_box(0);
}
x_163 = lean_box(0);
if (lean_is_scalar(x_162)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_162;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_161);
return x_164;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_160, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_160, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_167 = x_160;
} else {
 lean_dec_ref(x_160);
 x_167 = lean_box(0);
}
x_168 = lean_ctor_get(x_156, 0);
lean_inc(x_168);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 x_169 = x_156;
} else {
 lean_dec_ref(x_156);
 x_169 = lean_box(0);
}
x_170 = lean_ctor_get(x_165, 0);
lean_inc(x_170);
lean_dec(x_165);
x_171 = lean_array_to_list(x_170);
if (lean_is_scalar(x_159)) {
 x_172 = lean_alloc_ctor(0, 2, 0);
} else {
 x_172 = x_159;
}
lean_ctor_set(x_172, 0, x_168);
lean_ctor_set(x_172, 1, x_171);
if (lean_is_scalar(x_169)) {
 x_173 = lean_alloc_ctor(1, 1, 0);
} else {
 x_173 = x_169;
}
lean_ctor_set(x_173, 0, x_172);
if (lean_is_scalar(x_167)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_167;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_166);
return x_174;
}
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_144);
lean_dec(x_138);
x_179 = lean_ctor_get(x_153, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_153, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_181 = x_153;
} else {
 lean_dec_ref(x_153);
 x_181 = lean_box(0);
}
if (lean_is_scalar(x_181)) {
 x_182 = lean_alloc_ctor(1, 2, 0);
} else {
 x_182 = x_181;
}
lean_ctor_set(x_182, 0, x_179);
lean_ctor_set(x_182, 1, x_180);
return x_182;
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_20);
if (x_183 == 0)
{
lean_object* x_184; lean_object* x_185; 
x_184 = lean_ctor_get(x_20, 0);
lean_dec(x_184);
x_185 = lean_box(0);
lean_ctor_set(x_20, 0, x_185);
return x_20;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_186 = lean_ctor_get(x_20, 1);
lean_inc(x_186);
lean_dec(x_20);
x_187 = lean_box(0);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_187);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
else
{
uint8_t x_189; 
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_189 = !lean_is_exclusive(x_20);
if (x_189 == 0)
{
return x_20;
}
else
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_20, 0);
x_191 = lean_ctor_get(x_20, 1);
lean_inc(x_191);
lean_inc(x_190);
lean_dec(x_20);
x_192 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_192, 0, x_190);
lean_ctor_set(x_192, 1, x_191);
return x_192;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_84; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_3);
x_84 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectPatterns_x3f(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
if (x_5 == 0)
{
uint8_t x_86; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_86 = !lean_is_exclusive(x_84);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; 
x_87 = lean_ctor_get(x_84, 0);
lean_dec(x_87);
x_88 = lean_box(0);
lean_ctor_set(x_84, 0, x_88);
return x_84;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_dec(x_84);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_84, 1);
lean_inc(x_92);
lean_dec(x_84);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_3);
x_93 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_collectGroundPattern_x3f(x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_92);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = !lean_is_exclusive(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_93, 0);
lean_dec(x_96);
x_97 = lean_box(0);
lean_ctor_set(x_93, 0, x_97);
return x_93;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_93, 1);
lean_inc(x_98);
lean_dec(x_93);
x_99 = lean_box(0);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
else
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_ctor_get(x_94, 0);
lean_inc(x_101);
lean_dec(x_94);
x_102 = lean_ctor_get(x_93, 1);
lean_inc(x_102);
lean_dec(x_93);
x_103 = !lean_is_exclusive(x_101);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; 
x_104 = lean_ctor_get(x_101, 1);
x_105 = lean_box(0);
lean_ctor_set_tag(x_101, 1);
lean_ctor_set(x_101, 1, x_105);
x_21 = x_101;
x_22 = x_104;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_102;
goto block_83;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_106 = lean_ctor_get(x_101, 0);
x_107 = lean_ctor_get(x_101, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_101);
x_108 = lean_box(0);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_106);
lean_ctor_set(x_109, 1, x_108);
x_21 = x_109;
x_22 = x_107;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_102;
goto block_83;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_93);
if (x_110 == 0)
{
return x_93;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_93, 0);
x_112 = lean_ctor_get(x_93, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_93);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_85, 0);
lean_inc(x_114);
lean_dec(x_85);
x_115 = lean_ctor_get(x_84, 1);
lean_inc(x_115);
lean_dec(x_84);
x_116 = lean_ctor_get(x_114, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_114, 1);
lean_inc(x_117);
lean_dec(x_114);
x_21 = x_116;
x_22 = x_117;
x_23 = x_8;
x_24 = x_9;
x_25 = x_10;
x_26 = x_11;
x_27 = x_115;
goto block_83;
}
}
else
{
uint8_t x_118; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_118 = !lean_is_exclusive(x_84);
if (x_118 == 0)
{
return x_84;
}
else
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_84, 0);
x_120 = lean_ctor_get(x_84, 1);
lean_inc(x_120);
lean_inc(x_119);
lean_dec(x_84);
x_121 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
return x_121;
}
}
block_20:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_alloc_ctor(0, 6, 1);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_ctor_set(x_17, 2, x_14);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_15);
lean_ctor_set(x_17, 5, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*6, x_4);
x_18 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_18, 0, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_16);
return x_19;
}
block_83:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_28 = lean_mk_string_unchecked("grind", 5, 5);
x_29 = lean_mk_string_unchecked("ematch", 6, 6);
x_30 = lean_mk_string_unchecked("pattern", 7, 7);
x_31 = l_Lean_Name_mkStr3(x_28, x_29, x_30);
lean_inc(x_31);
x_32 = l_Lean_isTracingEnabledFor___at___Lean_Meta_processPostponed_loop_spec__0(x_31, x_23, x_24, x_25, x_26, x_27);
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_ctor_get(x_32, 1);
x_36 = lean_array_get_size(x_6);
lean_dec(x_6);
x_37 = lean_unbox(x_34);
lean_dec(x_34);
if (x_37 == 0)
{
lean_free_object(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_13 = x_21;
x_14 = x_36;
x_15 = x_22;
x_16 = x_35;
goto block_20;
}
else
{
lean_object* x_38; 
lean_inc(x_1);
x_38 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_1, x_23, x_24, x_25, x_26, x_35);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = l_Lean_stringToMessageData(x_41);
lean_dec(x_41);
lean_inc(x_42);
lean_ctor_set_tag(x_32, 7);
lean_ctor_set(x_32, 1, x_39);
lean_ctor_set(x_32, 0, x_42);
x_43 = lean_mk_string_unchecked(": ", 2, 2);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_box(0);
lean_inc(x_21);
x_47 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(x_21, x_46);
x_48 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__1(x_47, x_46);
x_49 = l_Lean_MessageData_ofList(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
x_52 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_31, x_51, x_23, x_24, x_25, x_26, x_40);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_13 = x_21;
x_14 = x_36;
x_15 = x_22;
x_16 = x_53;
goto block_20;
}
else
{
uint8_t x_54; 
lean_dec(x_36);
lean_free_object(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_54 = !lean_is_exclusive(x_38);
if (x_54 == 0)
{
return x_38;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_38, 0);
x_56 = lean_ctor_get(x_38, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_38);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_58 = lean_ctor_get(x_32, 0);
x_59 = lean_ctor_get(x_32, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_32);
x_60 = lean_array_get_size(x_6);
lean_dec(x_6);
x_61 = lean_unbox(x_58);
lean_dec(x_58);
if (x_61 == 0)
{
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_13 = x_21;
x_14 = x_60;
x_15 = x_22;
x_16 = x_59;
goto block_20;
}
else
{
lean_object* x_62; 
lean_inc(x_1);
x_62 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_1, x_23, x_24, x_25, x_26, x_59);
if (lean_obj_tag(x_62) == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_63 = lean_ctor_get(x_62, 0);
lean_inc(x_63);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = lean_mk_string_unchecked("", 0, 0);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
lean_inc(x_66);
x_67 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_63);
x_68 = lean_mk_string_unchecked(": ", 2, 2);
x_69 = l_Lean_stringToMessageData(x_68);
lean_dec(x_68);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_67);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_box(0);
lean_inc(x_21);
x_72 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__0(x_21, x_71);
x_73 = l_List_mapTR_loop___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__1(x_72, x_71);
x_74 = l_Lean_MessageData_ofList(x_73);
x_75 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_75, 0, x_70);
lean_ctor_set(x_75, 1, x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_66);
x_77 = l_Lean_addTrace___at___Lean_Meta_processPostponed_loop_spec__1(x_31, x_76, x_23, x_24, x_25, x_26, x_64);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
lean_dec(x_77);
x_13 = x_21;
x_14 = x_60;
x_15 = x_22;
x_16 = x_78;
goto block_20;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_60);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_ctor_get(x_62, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_62, 1);
lean_inc(x_80);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_81 = x_62;
} else {
 lean_dec_ref(x_62);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; lean_object* x_32; uint8_t x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; uint8_t x_39; uint64_t x_40; uint64_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; uint8_t x_50; lean_object* x_51; lean_object* x_52; 
x_13 = lean_box(1);
x_14 = lean_ctor_get(x_8, 0);
x_15 = lean_ctor_get_uint8(x_14, 0);
x_16 = lean_ctor_get_uint8(x_14, 1);
x_17 = lean_ctor_get_uint8(x_14, 2);
x_18 = lean_ctor_get_uint8(x_14, 3);
x_19 = lean_ctor_get_uint8(x_14, 4);
x_20 = lean_ctor_get_uint8(x_14, 5);
x_21 = lean_ctor_get_uint8(x_14, 6);
x_22 = lean_ctor_get_uint8(x_14, 7);
x_23 = lean_ctor_get_uint8(x_14, 8);
x_24 = lean_ctor_get_uint8(x_14, 10);
x_25 = lean_ctor_get_uint8(x_14, 11);
x_26 = lean_ctor_get_uint8(x_14, 12);
x_27 = lean_ctor_get_uint8(x_14, 13);
x_28 = lean_ctor_get_uint8(x_14, 14);
x_29 = lean_ctor_get_uint8(x_14, 15);
x_30 = lean_ctor_get_uint8(x_14, 16);
x_31 = lean_ctor_get_uint8(x_14, 17);
x_32 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_32, 0, x_15);
lean_ctor_set_uint8(x_32, 1, x_16);
lean_ctor_set_uint8(x_32, 2, x_17);
lean_ctor_set_uint8(x_32, 3, x_18);
lean_ctor_set_uint8(x_32, 4, x_19);
lean_ctor_set_uint8(x_32, 5, x_20);
lean_ctor_set_uint8(x_32, 6, x_21);
lean_ctor_set_uint8(x_32, 7, x_22);
lean_ctor_set_uint8(x_32, 8, x_23);
x_33 = lean_unbox(x_13);
lean_ctor_set_uint8(x_32, 9, x_33);
lean_ctor_set_uint8(x_32, 10, x_24);
lean_ctor_set_uint8(x_32, 11, x_25);
lean_ctor_set_uint8(x_32, 12, x_26);
lean_ctor_set_uint8(x_32, 13, x_27);
lean_ctor_set_uint8(x_32, 14, x_28);
lean_ctor_set_uint8(x_32, 15, x_29);
lean_ctor_set_uint8(x_32, 16, x_30);
lean_ctor_set_uint8(x_32, 17, x_31);
x_34 = lean_ctor_get_uint64(x_8, sizeof(void*)*7);
x_35 = lean_unsigned_to_nat(2u);
x_36 = lean_uint64_of_nat(x_35);
x_37 = lean_uint64_shift_right(x_34, x_36);
x_38 = lean_uint64_shift_left(x_37, x_36);
x_39 = lean_unbox(x_13);
x_40 = l_Lean_Meta_TransparencyMode_toUInt64(x_39);
x_41 = lean_uint64_lor(x_38, x_40);
x_42 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_43 = lean_ctor_get(x_8, 1);
x_44 = lean_ctor_get(x_8, 2);
x_45 = lean_ctor_get(x_8, 3);
x_46 = lean_ctor_get(x_8, 4);
x_47 = lean_ctor_get(x_8, 5);
x_48 = lean_ctor_get(x_8, 6);
x_49 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_50 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
x_51 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_51, 0, x_32);
lean_ctor_set(x_51, 1, x_43);
lean_ctor_set(x_51, 2, x_44);
lean_ctor_set(x_51, 3, x_45);
lean_ctor_set(x_51, 4, x_46);
lean_ctor_set(x_51, 5, x_47);
lean_ctor_set(x_51, 6, x_48);
lean_ctor_set_uint64(x_51, sizeof(void*)*7, x_41);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 8, x_42);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 9, x_49);
lean_ctor_set_uint8(x_51, sizeof(void*)*7 + 10, x_50);
x_52 = lean_box(x_1);
switch (lean_obj_tag(x_52)) {
case 4:
{
lean_object* x_53; 
lean_dec(x_7);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_51);
x_53 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes(x_6, x_51, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = l_Array_isEmpty___redArg(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(x_2, x_3, x_4, x_1, x_5, x_6, x_54, x_51, x_9, x_10, x_11, x_55);
lean_dec(x_54);
return x_57;
}
else
{
lean_object* x_58; 
lean_dec(x_54);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_58 = l_Lean_Meta_Grind_Origin_pp___at___Lean_Meta_Grind_mkEMatchTheoremCore_spec__2(x_2, x_51, x_9, x_10, x_11, x_55);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_mk_string_unchecked("invalid `grind` forward theorem, theorem `", 42, 42);
x_62 = l_Lean_stringToMessageData(x_61);
lean_dec(x_61);
x_63 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_59);
x_64 = lean_mk_string_unchecked("` does not have propositional hypotheses", 40, 40);
x_65 = l_Lean_stringToMessageData(x_64);
lean_dec(x_64);
x_66 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_66, 0, x_63);
lean_ctor_set(x_66, 1, x_65);
x_67 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_66, x_51, x_9, x_10, x_11, x_60);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_51);
x_68 = !lean_is_exclusive(x_67);
if (x_68 == 0)
{
return x_67;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_67, 0);
x_70 = lean_ctor_get(x_67, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_67);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
else
{
uint8_t x_72; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
x_72 = !lean_is_exclusive(x_58);
if (x_72 == 0)
{
return x_58;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_58, 0);
x_74 = lean_ctor_get(x_58, 1);
lean_inc(x_74);
lean_inc(x_73);
lean_dec(x_58);
x_75 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_75, 0, x_73);
lean_ctor_set(x_75, 1, x_74);
return x_75;
}
}
}
}
else
{
uint8_t x_76; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_76 = !lean_is_exclusive(x_53);
if (x_76 == 0)
{
return x_53;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_53, 0);
x_78 = lean_ctor_get(x_53, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_53);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
case 5:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_unsigned_to_nat(1u);
x_81 = lean_mk_empty_array_with_capacity(x_80);
x_82 = lean_array_push(x_81, x_7);
x_83 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(x_2, x_3, x_4, x_1, x_5, x_6, x_82, x_51, x_9, x_10, x_11, x_12);
lean_dec(x_82);
return x_83;
}
case 6:
{
lean_object* x_84; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_51);
x_84 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes(x_6, x_51, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_array_push(x_85, x_7);
x_88 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(x_2, x_3, x_4, x_1, x_5, x_6, x_87, x_51, x_9, x_10, x_11, x_86);
lean_dec(x_87);
return x_88;
}
else
{
uint8_t x_89; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_89 = !lean_is_exclusive(x_84);
if (x_89 == 0)
{
return x_84;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_84, 0);
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_84);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
}
case 7:
{
lean_object* x_93; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_51);
x_93 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes(x_6, x_51, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_94 = lean_ctor_get(x_93, 0);
lean_inc(x_94);
x_95 = lean_ctor_get(x_93, 1);
lean_inc(x_95);
lean_dec(x_93);
x_96 = lean_unsigned_to_nat(1u);
x_97 = lean_mk_empty_array_with_capacity(x_96);
x_98 = lean_array_push(x_97, x_7);
x_99 = l_Array_reverse(lean_box(0), x_94);
x_100 = l_Array_append(lean_box(0), x_98, x_99);
lean_dec(x_99);
x_101 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(x_2, x_3, x_4, x_1, x_5, x_6, x_100, x_51, x_9, x_10, x_11, x_95);
lean_dec(x_100);
return x_101;
}
else
{
uint8_t x_102; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_102 = !lean_is_exclusive(x_93);
if (x_102 == 0)
{
return x_93;
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = lean_ctor_get(x_93, 0);
x_104 = lean_ctor_get(x_93, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_93);
x_105 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
return x_105;
}
}
}
case 8:
{
lean_object* x_106; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_51);
x_106 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getPropTypes(x_6, x_51, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
lean_dec(x_106);
x_109 = lean_unsigned_to_nat(1u);
x_110 = lean_mk_empty_array_with_capacity(x_109);
x_111 = lean_array_push(x_110, x_7);
x_112 = l_Array_append(lean_box(0), x_111, x_107);
lean_dec(x_107);
x_113 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(x_2, x_3, x_4, x_1, x_5, x_6, x_112, x_51, x_9, x_10, x_11, x_108);
lean_dec(x_112);
return x_113;
}
else
{
uint8_t x_114; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_114 = !lean_is_exclusive(x_106);
if (x_114 == 0)
{
return x_106;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_106, 0);
x_116 = lean_ctor_get(x_106, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_106);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
default: 
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_52);
lean_dec(x_7);
x_118 = lean_mk_string_unchecked("Lean.Meta.Tactic.Grind.EMatchTheorem", 36, 36);
x_119 = lean_mk_string_unchecked("Lean.Meta.Grind.mkEMatchTheoremWithKind\?", 40, 40);
x_120 = lean_unsigned_to_nat(883u);
x_121 = lean_unsigned_to_nat(13u);
x_122 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_123 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_118, x_119, x_120, x_121, x_122);
lean_dec(x_122);
lean_dec(x_119);
lean_dec(x_118);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_51);
x_124 = l_panic___at___Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_spec__0(x_123, x_51, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; 
x_125 = lean_ctor_get(x_124, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_124, 1);
lean_inc(x_126);
lean_dec(x_124);
x_127 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f_go(x_2, x_3, x_4, x_1, x_5, x_6, x_125, x_51, x_9, x_10, x_11, x_126);
lean_dec(x_125);
return x_127;
}
else
{
uint8_t x_128; 
lean_dec(x_51);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_124);
if (x_128 == 0)
{
return x_124;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_124, 0);
x_130 = lean_ctor_get(x_124, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_124);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_4, x_12);
x_14 = lean_box(1);
if (x_13 == 0)
{
lean_object* x_15; uint8_t x_16; uint8_t x_17; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
x_17 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_4, x_16);
if (x_17 == 0)
{
lean_object* x_18; uint8_t x_19; uint8_t x_20; 
x_18 = lean_box(3);
x_19 = lean_unbox(x_18);
x_20 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_4, x_19);
if (x_20 == 0)
{
lean_object* x_21; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_3);
x_21 = lean_infer_type(x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; uint8_t x_30; uint8_t x_31; uint8_t x_32; uint8_t x_33; uint8_t x_34; uint8_t x_35; uint8_t x_36; uint8_t x_37; uint8_t x_38; uint8_t x_39; uint8_t x_40; uint8_t x_41; uint8_t x_42; uint8_t x_43; uint8_t x_44; uint8_t x_45; lean_object* x_46; uint8_t x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; uint8_t x_53; uint64_t x_54; uint64_t x_55; uint8_t x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; uint8_t x_64; lean_object* x_65; lean_object* x_66; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(x_4);
x_25 = lean_box(x_5);
x_26 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___lam__0___boxed), 12, 5);
lean_closure_set(x_26, 0, x_24);
lean_closure_set(x_26, 1, x_1);
lean_closure_set(x_26, 2, x_2);
lean_closure_set(x_26, 3, x_3);
lean_closure_set(x_26, 4, x_25);
x_27 = lean_box(2);
x_28 = lean_ctor_get(x_6, 0);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_28, 0);
x_30 = lean_ctor_get_uint8(x_28, 1);
x_31 = lean_ctor_get_uint8(x_28, 2);
x_32 = lean_ctor_get_uint8(x_28, 3);
x_33 = lean_ctor_get_uint8(x_28, 4);
x_34 = lean_ctor_get_uint8(x_28, 5);
x_35 = lean_ctor_get_uint8(x_28, 6);
x_36 = lean_ctor_get_uint8(x_28, 7);
x_37 = lean_ctor_get_uint8(x_28, 8);
x_38 = lean_ctor_get_uint8(x_28, 10);
x_39 = lean_ctor_get_uint8(x_28, 11);
x_40 = lean_ctor_get_uint8(x_28, 12);
x_41 = lean_ctor_get_uint8(x_28, 13);
x_42 = lean_ctor_get_uint8(x_28, 14);
x_43 = lean_ctor_get_uint8(x_28, 15);
x_44 = lean_ctor_get_uint8(x_28, 16);
x_45 = lean_ctor_get_uint8(x_28, 17);
lean_dec(x_28);
x_46 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_46, 0, x_29);
lean_ctor_set_uint8(x_46, 1, x_30);
lean_ctor_set_uint8(x_46, 2, x_31);
lean_ctor_set_uint8(x_46, 3, x_32);
lean_ctor_set_uint8(x_46, 4, x_33);
lean_ctor_set_uint8(x_46, 5, x_34);
lean_ctor_set_uint8(x_46, 6, x_35);
lean_ctor_set_uint8(x_46, 7, x_36);
lean_ctor_set_uint8(x_46, 8, x_37);
x_47 = lean_unbox(x_27);
lean_ctor_set_uint8(x_46, 9, x_47);
lean_ctor_set_uint8(x_46, 10, x_38);
lean_ctor_set_uint8(x_46, 11, x_39);
lean_ctor_set_uint8(x_46, 12, x_40);
lean_ctor_set_uint8(x_46, 13, x_41);
lean_ctor_set_uint8(x_46, 14, x_42);
lean_ctor_set_uint8(x_46, 15, x_43);
lean_ctor_set_uint8(x_46, 16, x_44);
lean_ctor_set_uint8(x_46, 17, x_45);
x_48 = lean_ctor_get_uint64(x_6, sizeof(void*)*7);
x_49 = lean_unsigned_to_nat(2u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_right(x_48, x_50);
x_52 = lean_uint64_shift_left(x_51, x_50);
x_53 = lean_unbox(x_27);
x_54 = l_Lean_Meta_TransparencyMode_toUInt64(x_53);
x_55 = lean_uint64_lor(x_52, x_54);
x_56 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 8);
x_57 = lean_ctor_get(x_6, 1);
lean_inc(x_57);
x_58 = lean_ctor_get(x_6, 2);
lean_inc(x_58);
x_59 = lean_ctor_get(x_6, 3);
lean_inc(x_59);
x_60 = lean_ctor_get(x_6, 4);
lean_inc(x_60);
x_61 = lean_ctor_get(x_6, 5);
lean_inc(x_61);
x_62 = lean_ctor_get(x_6, 6);
lean_inc(x_62);
x_63 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 9);
x_64 = lean_ctor_get_uint8(x_6, sizeof(void*)*7 + 10);
lean_dec(x_6);
x_65 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_65, 0, x_46);
lean_ctor_set(x_65, 1, x_57);
lean_ctor_set(x_65, 2, x_58);
lean_ctor_set(x_65, 3, x_59);
lean_ctor_set(x_65, 4, x_60);
lean_ctor_set(x_65, 5, x_61);
lean_ctor_set(x_65, 6, x_62);
lean_ctor_set_uint64(x_65, sizeof(void*)*7, x_55);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 8, x_56);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 9, x_63);
lean_ctor_set_uint8(x_65, sizeof(void*)*7 + 10, x_64);
x_66 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_22, x_26, x_20, x_65, x_7, x_8, x_9, x_23);
return x_66;
}
else
{
uint8_t x_67; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_67 = !lean_is_exclusive(x_21);
if (x_67 == 0)
{
return x_21;
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_68 = lean_ctor_get(x_21, 0);
x_69 = lean_ctor_get(x_21, 1);
lean_inc(x_69);
lean_inc(x_68);
lean_dec(x_21);
x_70 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
return x_70;
}
}
}
else
{
lean_object* x_71; 
x_71 = l_Lean_Meta_Grind_mkEMatchEqBwdTheoremCore(x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; lean_object* x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_71, 0, x_74);
return x_71;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_71, 0);
x_76 = lean_ctor_get(x_71, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_71);
x_77 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_77, 0, x_75);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
else
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_71);
if (x_79 == 0)
{
return x_71;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = lean_ctor_get(x_71, 0);
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_inc(x_80);
lean_dec(x_71);
x_82 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
return x_82;
}
}
}
}
else
{
uint8_t x_83; lean_object* x_84; 
x_83 = lean_unbox(x_14);
x_84 = l_Lean_Meta_Grind_mkEMatchEqTheoremCore(x_1, x_2, x_3, x_83, x_13, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_84, 0, x_87);
return x_84;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_84, 0);
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_84);
x_90 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_90, 0, x_88);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_90);
lean_ctor_set(x_91, 1, x_89);
return x_91;
}
}
else
{
uint8_t x_92; 
x_92 = !lean_is_exclusive(x_84);
if (x_92 == 0)
{
return x_84;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_84, 0);
x_94 = lean_ctor_get(x_84, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_84);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
}
else
{
uint8_t x_96; uint8_t x_97; lean_object* x_98; 
x_96 = lean_unbox(x_14);
x_97 = lean_unbox(x_14);
x_98 = l_Lean_Meta_Grind_mkEMatchEqTheoremCore(x_1, x_2, x_3, x_96, x_97, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_98) == 0)
{
uint8_t x_99; 
x_99 = !lean_is_exclusive(x_98);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; 
x_100 = lean_ctor_get(x_98, 0);
x_101 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_101, 0, x_100);
lean_ctor_set(x_98, 0, x_101);
return x_98;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_98, 0);
x_103 = lean_ctor_get(x_98, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_98);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_102);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_104);
lean_ctor_set(x_105, 1, x_103);
return x_105;
}
}
else
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
return x_98;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_98, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_98);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___lam__0(x_13, x_2, x_3, x_4, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_8);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = lean_unbox(x_5);
lean_dec(x_5);
x_13 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_1, x_2, x_3, x_11, x_12, x_6, x_7, x_8, x_9, x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_getProofFor(x_1, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_1);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_box(1);
x_15 = lean_unbox(x_14);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_16 = l_Lean_Meta_Grind_mkEMatchTheoremWithKind_x3f(x_11, x_13, x_9, x_2, x_15, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("`@", 2, 2);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_2);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked(" theorem ", 9, 9);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofName(x_1);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_mk_string_unchecked("` ", 2, 2);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_explainFailure(x_2);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked(", consider using different options or the `grind_pattern` command", 65, 65);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_37, x_3, x_4, x_5, x_6, x_18);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_38;
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_16);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_16, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_17, 0);
lean_inc(x_41);
lean_dec(x_17);
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_16, 1);
lean_inc(x_42);
lean_dec(x_16);
x_43 = lean_ctor_get(x_17, 0);
lean_inc(x_43);
lean_dec(x_17);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_16);
if (x_45 == 0)
{
return x_16;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_16, 0);
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_16);
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
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_8);
if (x_49 == 0)
{
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 0);
x_51 = lean_ctor_get(x_8, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_8);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchTheoremForDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_12 = l_Lean_Meta_Grind_mkEMatchEqTheorem(x_11, x_9, x_9, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_uset(x_3, x_2, x_15);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_20 = lean_array_uset(x_16, x_2, x_13);
x_2 = x_19;
x_3 = x_20;
x_8 = x_14;
goto _start;
}
else
{
uint8_t x_22; 
lean_dec(x_7);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_7 = l_Lean_Meta_getEqnsFor_x3f(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_box(0);
lean_ctor_set(x_7, 0, x_11);
return x_7;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
lean_dec(x_7);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = !lean_is_exclusive(x_8);
if (x_16 == 0)
{
lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_8, 0);
x_18 = lean_array_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = l_Array_mapMUnsafe_map___at___Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f_spec__0(x_18, x_20, x_17, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_8, 0, x_23);
lean_ctor_set(x_21, 0, x_8);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_8, 0, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_8);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_free_object(x_8);
x_27 = !lean_is_exclusive(x_21);
if (x_27 == 0)
{
return x_21;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_21, 0);
x_29 = lean_ctor_get(x_21, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_21);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; size_t x_32; lean_object* x_33; size_t x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_8, 0);
lean_inc(x_31);
lean_dec(x_8);
x_32 = lean_array_size(x_31);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_usize_of_nat(x_33);
x_35 = l_Array_mapMUnsafe_map___at___Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f_spec__0(x_32, x_34, x_31, x_2, x_3, x_4, x_5, x_15);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_38 = x_35;
} else {
 lean_dec_ref(x_35);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_36);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_35, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_43 = x_35;
} else {
 lean_dec_ref(x_35);
 x_43 = lean_box(0);
}
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(1, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_41);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_45 = !lean_is_exclusive(x_7);
if (x_45 == 0)
{
return x_7;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_7, 0);
x_47 = lean_ctor_get(x_7, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_7);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = l_Array_mapMUnsafe_map___at___Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f_spec__0(x_9, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
lean_inc(x_8);
x_14 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_13, x_12, x_1, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_15;
x_10 = x_16;
goto _start;
}
else
{
lean_object* x_21; 
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
lean_inc(x_8);
x_14 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_13, x_12, x_1, x_6, x_7, x_8, x_9, x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_3, x_18);
x_20 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0_spec__0(x_1, x_2, x_19, x_4, x_15, x_6, x_7, x_8, x_9, x_16);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_8);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_st_ref_get(x_8, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
lean_inc(x_1);
x_15 = l_Lean_wasOriginallyTheorem(x_14, x_1);
if (x_15 == 0)
{
lean_object* x_16; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_16 = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(x_1, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_10);
lean_dec(x_1);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_mk_string_unchecked("`", 1, 1);
x_20 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_3);
x_21 = lean_string_append(x_19, x_20);
lean_dec(x_20);
x_22 = lean_mk_string_unchecked("` attribute can only be applied to equational theorems or function definitions", 78, 78);
x_23 = lean_string_append(x_21, x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = l_Lean_MessageData_ofFormat(x_24);
x_26 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_25, x_5, x_6, x_7, x_8, x_18);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_26;
}
else
{
if (x_4 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
lean_dec(x_17);
x_27 = lean_ctor_get(x_16, 1);
lean_inc(x_27);
lean_dec(x_16);
x_28 = lean_mk_string_unchecked("`", 1, 1);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_30);
lean_ctor_set(x_10, 0, x_29);
x_31 = lean_mk_string_unchecked("` is a definition, you must only use the left-hand side for extracting patterns", 79, 79);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_10);
lean_ctor_set(x_33, 1, x_32);
x_34 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_33, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_34;
}
else
{
uint8_t x_35; 
lean_free_object(x_10);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_16);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_36 = lean_ctor_get(x_16, 1);
x_37 = lean_ctor_get(x_16, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_17, 0);
lean_inc(x_38);
lean_dec(x_17);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get_size(x_38);
x_41 = lean_box(0);
x_42 = lean_nat_dec_lt(x_39, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_40, x_40);
if (x_43 == 0)
{
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_16, 0, x_41);
return x_16;
}
else
{
size_t x_44; size_t x_45; lean_object* x_46; 
lean_free_object(x_16);
x_44 = lean_usize_of_nat(x_39);
x_45 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_46 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0(x_2, x_38, x_44, x_45, x_41, x_5, x_6, x_7, x_8, x_36);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_38);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_47 = lean_ctor_get(x_16, 1);
lean_inc(x_47);
lean_dec(x_16);
x_48 = lean_ctor_get(x_17, 0);
lean_inc(x_48);
lean_dec(x_17);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_48);
x_51 = lean_box(0);
x_52 = lean_nat_dec_lt(x_49, x_50);
if (x_52 == 0)
{
lean_object* x_53; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_47);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_50, x_50);
if (x_54 == 0)
{
lean_object* x_55; 
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_47);
return x_55;
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; 
x_56 = lean_usize_of_nat(x_49);
x_57 = lean_usize_of_nat(x_50);
lean_dec(x_50);
x_58 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0(x_2, x_48, x_56, x_57, x_51, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_48);
return x_58;
}
}
}
}
}
}
else
{
uint8_t x_59; 
lean_free_object(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_16);
if (x_59 == 0)
{
return x_16;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_16, 0);
x_61 = lean_ctor_get(x_16, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_16);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_object* x_63; 
lean_free_object(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_63 = l_Lean_Meta_Grind_mkEMatchEqTheorem(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_67 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_66, x_64, x_2, x_5, x_6, x_7, x_8, x_65);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_67;
}
else
{
uint8_t x_68; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_68 = !lean_is_exclusive(x_63);
if (x_68 == 0)
{
return x_63;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_69 = lean_ctor_get(x_63, 0);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_63);
x_71 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_71, 0, x_69);
lean_ctor_set(x_71, 1, x_70);
return x_71;
}
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_72 = lean_ctor_get(x_10, 0);
x_73 = lean_ctor_get(x_10, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_10);
x_74 = lean_ctor_get(x_72, 0);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_1);
x_75 = l_Lean_wasOriginallyTheorem(x_74, x_1);
if (x_75 == 0)
{
lean_object* x_76; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_1);
x_76 = l_Lean_Meta_Grind_mkEMatchEqTheoremsForDef_x3f(x_1, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_1);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_mk_string_unchecked("`", 1, 1);
x_80 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_EMatchTheoremKind_toAttribute(x_3);
x_81 = lean_string_append(x_79, x_80);
lean_dec(x_80);
x_82 = lean_mk_string_unchecked("` attribute can only be applied to equational theorems or function definitions", 78, 78);
x_83 = lean_string_append(x_81, x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = l_Lean_MessageData_ofFormat(x_84);
x_86 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_85, x_5, x_6, x_7, x_8, x_78);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_86;
}
else
{
if (x_4 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_77);
x_87 = lean_ctor_get(x_76, 1);
lean_inc(x_87);
lean_dec(x_76);
x_88 = lean_mk_string_unchecked("`", 1, 1);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
x_90 = l_Lean_MessageData_ofName(x_1);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_mk_string_unchecked("` is a definition, you must only use the left-hand side for extracting patterns", 79, 79);
x_93 = l_Lean_stringToMessageData(x_92);
lean_dec(x_92);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_91);
lean_ctor_set(x_94, 1, x_93);
x_95 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_94, x_5, x_6, x_7, x_8, x_87);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_95;
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_1);
x_96 = lean_ctor_get(x_76, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_97 = x_76;
} else {
 lean_dec_ref(x_76);
 x_97 = lean_box(0);
}
x_98 = lean_ctor_get(x_77, 0);
lean_inc(x_98);
lean_dec(x_77);
x_99 = lean_unsigned_to_nat(0u);
x_100 = lean_array_get_size(x_98);
x_101 = lean_box(0);
x_102 = lean_nat_dec_lt(x_99, x_100);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_97)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_97;
}
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_96);
return x_103;
}
else
{
uint8_t x_104; 
x_104 = lean_nat_dec_le(x_100, x_100);
if (x_104 == 0)
{
lean_object* x_105; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
if (lean_is_scalar(x_97)) {
 x_105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_105 = x_97;
}
lean_ctor_set(x_105, 0, x_101);
lean_ctor_set(x_105, 1, x_96);
return x_105;
}
else
{
size_t x_106; size_t x_107; lean_object* x_108; 
lean_dec(x_97);
x_106 = lean_usize_of_nat(x_99);
x_107 = lean_usize_of_nat(x_100);
lean_dec(x_100);
x_108 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0(x_2, x_98, x_106, x_107, x_101, x_5, x_6, x_7, x_8, x_96);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_98);
return x_108;
}
}
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_109 = lean_ctor_get(x_76, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_76, 1);
lean_inc(x_110);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_111 = x_76;
} else {
 lean_dec_ref(x_76);
 x_111 = lean_box(0);
}
if (lean_is_scalar(x_111)) {
 x_112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_112 = x_111;
}
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_110);
return x_112;
}
}
else
{
lean_object* x_113; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_113 = l_Lean_Meta_Grind_mkEMatchEqTheorem(x_1, x_75, x_4, x_5, x_6, x_7, x_8, x_73);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_113, 1);
lean_inc(x_115);
lean_dec(x_113);
x_116 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_117 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_116, x_114, x_2, x_5, x_6, x_7, x_8, x_115);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
return x_117;
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_118 = lean_ctor_get(x_113, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_113, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_120 = x_113;
} else {
 lean_dec_ref(x_113);
 x_120 = lean_box(0);
}
if (lean_is_scalar(x_120)) {
 x_121 = lean_alloc_ctor(1, 2, 0);
} else {
 x_121 = x_120;
}
lean_ctor_set(x_121, 0, x_118);
lean_ctor_set(x_121, 1, x_119);
return x_121;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0_spec__0(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = l_Array_foldlMUnsafe_fold___at_____private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr_spec__0(x_11, x_2, x_12, x_13, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(x_1, x_10, x_11, x_12, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
x_8 = l_Lean_Meta_Grind_EMatchTheorems_erase(x_4, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_8;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_box(1);
x_8 = lean_array_uget(x_3, x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_1);
x_10 = l_Lean_Meta_Grind_EMatchTheorems_contains(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = lean_unbox(x_7);
return x_11;
}
else
{
if (x_2 == 0)
{
lean_object* x_12; size_t x_13; size_t x_14; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_usize_of_nat(x_12);
x_14 = lean_usize_add(x_4, x_13);
x_4 = x_14;
goto _start;
}
else
{
uint8_t x_16; 
lean_dec(x_1);
x_16 = lean_unbox(x_7);
return x_16;
}
}
}
else
{
lean_object* x_17; uint8_t x_18; 
lean_dec(x_1);
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_mk_string_unchecked("`", 1, 1);
x_9 = l_Lean_stringToMessageData(x_8);
lean_dec(x_8);
x_10 = l_Lean_MessageData_ofName(x_1);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("` is not marked with the `[grind]` attribute", 44, 44);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_14, x_3, x_4, x_5, x_6, x_7);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = lean_st_ref_get(x_6, x_7);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_wasOriginallyTheorem(x_16, x_2);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_18 = l_Lean_Meta_getEqnsFor_x3f(x_2, x_3, x_4, x_5, x_6, x_15);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0(x_2, lean_box(0), x_3, x_4, x_5, x_6, x_20);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_34; lean_object* x_35; uint8_t x_47; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_st_ref_get(x_6, x_22);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_ctor_get(x_25, 0);
lean_inc(x_28);
lean_dec(x_25);
x_29 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_30 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get_uint8(x_32, sizeof(void*)*3);
lean_dec(x_32);
x_34 = l_Lean_ScopedEnvExtension_getState___redArg(x_29, x_30, x_28, x_33);
x_54 = lean_unsigned_to_nat(0u);
x_55 = lean_array_get_size(x_23);
x_56 = lean_nat_dec_lt(x_54, x_55);
if (x_56 == 0)
{
lean_dec(x_55);
x_47 = x_17;
goto block_53;
}
else
{
if (x_56 == 0)
{
lean_dec(x_55);
x_47 = x_17;
goto block_53;
}
else
{
size_t x_57; size_t x_58; uint8_t x_59; 
x_57 = lean_usize_of_nat(x_54);
x_58 = lean_usize_of_nat(x_55);
lean_dec(x_55);
lean_inc(x_34);
x_59 = l_Array_anyMUnsafe_any___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__1(x_34, x_17, x_23, x_57, x_58);
x_47 = x_59;
goto block_53;
}
}
block_46:
{
lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = lean_array_get_size(x_23);
x_38 = lean_nat_dec_lt(x_36, x_37);
if (x_38 == 0)
{
lean_object* x_39; 
lean_dec(x_37);
lean_dec(x_23);
if (lean_is_scalar(x_27)) {
 x_39 = lean_alloc_ctor(0, 2, 0);
} else {
 x_39 = x_27;
}
lean_ctor_set(x_39, 0, x_34);
lean_ctor_set(x_39, 1, x_35);
return x_39;
}
else
{
uint8_t x_40; 
x_40 = lean_nat_dec_le(x_37, x_37);
if (x_40 == 0)
{
lean_object* x_41; 
lean_dec(x_37);
lean_dec(x_23);
if (lean_is_scalar(x_27)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_27;
}
lean_ctor_set(x_41, 0, x_34);
lean_ctor_set(x_41, 1, x_35);
return x_41;
}
else
{
size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_usize_of_nat(x_36);
x_43 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_44 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__0(x_23, x_42, x_43, x_34);
lean_dec(x_23);
if (lean_is_scalar(x_27)) {
 x_45 = lean_alloc_ctor(0, 2, 0);
} else {
 x_45 = x_27;
}
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_35);
return x_45;
}
}
}
block_53:
{
if (x_47 == 0)
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_35 = x_26;
goto block_46;
}
else
{
lean_object* x_48; uint8_t x_49; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_23);
x_48 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0(x_2, lean_box(0), x_3, x_4, x_5, x_6, x_26);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
return x_48;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
}
else
{
uint8_t x_60; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_60 = !lean_is_exclusive(x_18);
if (x_60 == 0)
{
return x_18;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_18, 0);
x_62 = lean_ctor_get(x_18, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_18);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_64 = lean_st_ref_get(x_6, x_15);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_64, 1);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
lean_dec(x_65);
x_68 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_69 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get_uint8(x_71, sizeof(void*)*3);
lean_dec(x_71);
x_73 = l_Lean_ScopedEnvExtension_getState___redArg(x_68, x_69, x_67, x_72);
lean_inc(x_2);
x_74 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_74, 0, x_2);
x_75 = l_Lean_Meta_Grind_EMatchTheorems_contains(x_73, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; uint8_t x_77; 
lean_dec(x_1);
x_76 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0(x_2, lean_box(0), x_3, x_4, x_5, x_6, x_66);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_77 = !lean_is_exclusive(x_76);
if (x_77 == 0)
{
return x_76;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_76, 0);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_76);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_8 = x_66;
goto block_12;
}
}
block_12:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_2);
x_10 = l_Lean_Meta_Grind_EMatchTheorems_erase(x_1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; uint8_t x_9; lean_object* x_10; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_9 = l_Array_anyMUnsafe_any___at___Lean_Meta_Grind_EMatchTheorems_eraseDecl_spec__1(x_1, x_6, x_3, x_7, x_8);
lean_dec(x_3);
x_10 = lean_box(x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_EMatchTheorems_eraseDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchAttr(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_9 = lean_box(0);
x_10 = lean_unbox(x_9);
x_11 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_10);
x_12 = lean_box(1);
if (x_11 == 0)
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; 
x_13 = lean_box(1);
x_14 = lean_unbox(x_13);
x_15 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; uint8_t x_18; 
x_16 = lean_box(2);
x_17 = lean_unbox(x_16);
x_18 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_beqEMatchTheoremKind____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_1361_(x_3, x_17);
if (x_18 == 0)
{
lean_object* x_19; 
lean_inc(x_1);
x_19 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_43; uint8_t x_44; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_st_ref_get(x_7, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_43 = lean_ctor_get(x_23, 0);
lean_inc(x_43);
lean_dec(x_23);
lean_inc(x_1);
x_44 = l_Lean_wasOriginallyTheorem(x_43, x_1);
if (x_44 == 0)
{
goto block_42;
}
else
{
if (x_18 == 0)
{
lean_dec(x_20);
goto block_34;
}
else
{
goto block_42;
}
}
block_34:
{
lean_object* x_25; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_25 = l_Lean_Meta_Grind_mkEMatchTheoremForDecl(x_1, x_3, x_4, x_5, x_6, x_7, x_24);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_29 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addSimpCongrTheorem_spec__0(lean_box(0), lean_box(0), lean_box(0), x_28, x_26, x_2, x_4, x_5, x_6, x_7, x_27);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
return x_29;
}
else
{
uint8_t x_30; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_30 = !lean_is_exclusive(x_25);
if (x_30 == 0)
{
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 0);
x_32 = lean_ctor_get(x_25, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_25);
x_33 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
block_40:
{
uint8_t x_35; 
x_35 = l_Lean_ConstantInfo_isAxiom(x_20);
lean_dec(x_20);
if (x_35 == 0)
{
uint8_t x_36; lean_object* x_37; 
x_36 = lean_unbox(x_12);
x_37 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(x_1, x_2, x_3, x_36, x_4, x_5, x_6, x_7, x_24);
return x_37;
}
else
{
if (x_18 == 0)
{
goto block_34;
}
else
{
uint8_t x_38; lean_object* x_39; 
x_38 = lean_unbox(x_12);
x_39 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(x_1, x_2, x_3, x_38, x_4, x_5, x_6, x_7, x_24);
return x_39;
}
}
}
block_42:
{
uint8_t x_41; 
x_41 = l_Lean_ConstantInfo_isCtor(x_20);
if (x_41 == 0)
{
goto block_40;
}
else
{
if (x_18 == 0)
{
lean_dec(x_20);
goto block_34;
}
else
{
goto block_40;
}
}
}
}
else
{
uint8_t x_45; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_45 = !lean_is_exclusive(x_19);
if (x_45 == 0)
{
return x_19;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_19, 0);
x_47 = lean_ctor_get(x_19, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_19);
x_48 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_48, 0, x_46);
lean_ctor_set(x_48, 1, x_47);
return x_48;
}
}
}
else
{
uint8_t x_49; lean_object* x_50; 
x_49 = lean_unbox(x_12);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_50 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(x_1, x_2, x_3, x_49, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(x_1, x_2, x_3, x_15, x_4, x_5, x_6, x_7, x_51);
return x_52;
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_50;
}
}
}
else
{
lean_object* x_53; 
x_53 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(x_1, x_2, x_3, x_11, x_4, x_5, x_6, x_7, x_8);
return x_53;
}
}
else
{
uint8_t x_54; lean_object* x_55; 
x_54 = lean_unbox(x_12);
x_55 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_addGrindEqAttr(x_1, x_2, x_3, x_54, x_4, x_5, x_6, x_7, x_8);
return x_55;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_addEMatchAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; uint8_t x_10; lean_object* x_11; 
x_9 = lean_unbox(x_2);
lean_dec(x_2);
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l_Lean_Meta_Grind_addEMatchAttr(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_Meta_Grind_instInhabitedEMatchTheorems;
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt;
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
lean_dec(x_14);
x_16 = l_Lean_ScopedEnvExtension_getState___redArg(x_10, x_12, x_11, x_15);
lean_inc(x_5);
lean_inc(x_3);
x_17 = l_Lean_Meta_Grind_EMatchTheorems_eraseDecl(x_16, x_1, x_2, x_3, x_4, x_5, x_9);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_take(x_5, x_19);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
x_24 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseEMatchAttr___lam__0___boxed), 2, 1);
lean_closure_set(x_24, 0, x_18);
x_25 = lean_ctor_get(x_22, 0);
lean_inc(x_25);
x_26 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_12, x_25, x_24);
x_27 = lean_ctor_get(x_22, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_22, 2);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 3);
lean_inc(x_29);
x_30 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_30);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
lean_inc(x_31);
lean_ctor_set(x_20, 1, x_31);
lean_ctor_set(x_20, 0, x_31);
x_32 = lean_ctor_get(x_22, 5);
lean_inc(x_32);
x_33 = lean_ctor_get(x_22, 6);
lean_inc(x_33);
x_34 = lean_ctor_get(x_22, 7);
lean_inc(x_34);
lean_dec(x_22);
x_35 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_35, 0, x_26);
lean_ctor_set(x_35, 1, x_27);
lean_ctor_set(x_35, 2, x_28);
lean_ctor_set(x_35, 3, x_29);
lean_ctor_set(x_35, 4, x_20);
lean_ctor_set(x_35, 5, x_32);
lean_ctor_set(x_35, 6, x_33);
lean_ctor_set(x_35, 7, x_34);
x_36 = lean_st_ref_set(x_5, x_35, x_23);
lean_dec(x_5);
x_37 = lean_ctor_get(x_36, 1);
lean_inc(x_37);
lean_dec(x_36);
x_38 = lean_st_ref_take(x_3, x_37);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_inc(x_30);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_30);
lean_inc(x_30);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_30);
lean_inc(x_30);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_30);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_30);
lean_inc(x_45);
lean_inc(x_42);
x_46 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_46, 0, x_42);
lean_ctor_set(x_46, 1, x_43);
lean_ctor_set(x_46, 2, x_44);
lean_ctor_set(x_46, 3, x_42);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set(x_46, 5, x_45);
x_47 = lean_ctor_get(x_39, 2);
lean_inc(x_47);
x_48 = lean_ctor_get(x_39, 3);
lean_inc(x_48);
x_49 = lean_ctor_get(x_39, 4);
lean_inc(x_49);
lean_dec(x_39);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_41);
lean_ctor_set(x_50, 1, x_46);
lean_ctor_set(x_50, 2, x_47);
lean_ctor_set(x_50, 3, x_48);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_st_ref_set(x_3, x_50, x_40);
lean_dec(x_3);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_51, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_51, 0, x_54);
return x_51;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_51, 1);
lean_inc(x_55);
lean_dec(x_51);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_58 = lean_ctor_get(x_20, 0);
x_59 = lean_ctor_get(x_20, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_20);
x_60 = lean_alloc_closure((void*)(l_Lean_Meta_Grind_eraseEMatchAttr___lam__0___boxed), 2, 1);
lean_closure_set(x_60, 0, x_18);
x_61 = lean_ctor_get(x_58, 0);
lean_inc(x_61);
x_62 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_12, x_61, x_60);
x_63 = lean_ctor_get(x_58, 1);
lean_inc(x_63);
x_64 = lean_ctor_get(x_58, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_58, 3);
lean_inc(x_65);
x_66 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_66);
x_67 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_67, 0, x_66);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_ctor_get(x_58, 5);
lean_inc(x_69);
x_70 = lean_ctor_get(x_58, 6);
lean_inc(x_70);
x_71 = lean_ctor_get(x_58, 7);
lean_inc(x_71);
lean_dec(x_58);
x_72 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_72, 0, x_62);
lean_ctor_set(x_72, 1, x_63);
lean_ctor_set(x_72, 2, x_64);
lean_ctor_set(x_72, 3, x_65);
lean_ctor_set(x_72, 4, x_68);
lean_ctor_set(x_72, 5, x_69);
lean_ctor_set(x_72, 6, x_70);
lean_ctor_set(x_72, 7, x_71);
x_73 = lean_st_ref_set(x_5, x_72, x_59);
lean_dec(x_5);
x_74 = lean_ctor_get(x_73, 1);
lean_inc(x_74);
lean_dec(x_73);
x_75 = lean_st_ref_take(x_3, x_74);
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 0);
lean_inc(x_78);
lean_inc(x_66);
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_66);
lean_inc(x_66);
x_80 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_80, 0, x_66);
lean_inc(x_66);
x_81 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_81, 0, x_66);
x_82 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_82, 0, x_66);
lean_inc(x_82);
lean_inc(x_79);
x_83 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_83, 0, x_79);
lean_ctor_set(x_83, 1, x_80);
lean_ctor_set(x_83, 2, x_81);
lean_ctor_set(x_83, 3, x_79);
lean_ctor_set(x_83, 4, x_82);
lean_ctor_set(x_83, 5, x_82);
x_84 = lean_ctor_get(x_76, 2);
lean_inc(x_84);
x_85 = lean_ctor_get(x_76, 3);
lean_inc(x_85);
x_86 = lean_ctor_get(x_76, 4);
lean_inc(x_86);
lean_dec(x_76);
x_87 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_87, 0, x_78);
lean_ctor_set(x_87, 1, x_83);
lean_ctor_set(x_87, 2, x_84);
lean_ctor_set(x_87, 3, x_85);
lean_ctor_set(x_87, 4, x_86);
x_88 = lean_st_ref_set(x_3, x_87, x_77);
lean_dec(x_3);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
if (lean_is_exclusive(x_88)) {
 lean_ctor_release(x_88, 0);
 lean_ctor_release(x_88, 1);
 x_90 = x_88;
} else {
 lean_dec_ref(x_88);
 x_90 = lean_box(0);
}
x_91 = lean_box(0);
if (lean_is_scalar(x_90)) {
 x_92 = lean_alloc_ctor(0, 2, 0);
} else {
 x_92 = x_90;
}
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
}
else
{
uint8_t x_93; 
lean_dec(x_5);
lean_dec(x_3);
x_93 = !lean_is_exclusive(x_17);
if (x_93 == 0)
{
return x_17;
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_17, 0);
x_95 = lean_ctor_get(x_17, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_17);
x_96 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
return x_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Grind_eraseEMatchAttr___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Grind_eraseEMatchAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_Grind_eraseEMatchAttr(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
lean_object* initialize_Init_Grind_Util(uint8_t builtin, lean_object*);
lean_object* initialize_Init_Grind_Tactics(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_HeadIndex(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_FoldConsts(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_CollectFVars(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Grind_Util(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_EMatchTheorem(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Grind_Tactics(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_HeadIndex(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_FoldConsts(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_CollectFVars(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_Util(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig = _init_l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_normConfig);
l_Lean_Meta_Grind_instInhabitedOrigin = _init_l_Lean_Meta_Grind_instInhabitedOrigin();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedOrigin);
l_Lean_Meta_Grind_instReprOrigin = _init_l_Lean_Meta_Grind_instReprOrigin();
lean_mark_persistent(l_Lean_Meta_Grind_instReprOrigin);
l_Lean_Meta_Grind_instBEqOrigin = _init_l_Lean_Meta_Grind_instBEqOrigin();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqOrigin);
l_Lean_Meta_Grind_instBEqOrigin__1 = _init_l_Lean_Meta_Grind_instBEqOrigin__1();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqOrigin__1);
l_Lean_Meta_Grind_instHashableOrigin = _init_l_Lean_Meta_Grind_instHashableOrigin();
lean_mark_persistent(l_Lean_Meta_Grind_instHashableOrigin);
l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind = _init_l_Lean_Meta_Grind_instInhabitedEMatchTheoremKind();
l_Lean_Meta_Grind_instBEqEMatchTheoremKind = _init_l_Lean_Meta_Grind_instBEqEMatchTheoremKind();
lean_mark_persistent(l_Lean_Meta_Grind_instBEqEMatchTheoremKind);
l_Lean_Meta_Grind_instReprEMatchTheoremKind = _init_l_Lean_Meta_Grind_instReprEMatchTheoremKind();
lean_mark_persistent(l_Lean_Meta_Grind_instReprEMatchTheoremKind);
l_Lean_Meta_Grind_instHashableEMatchTheoremKind = _init_l_Lean_Meta_Grind_instHashableEMatchTheoremKind();
lean_mark_persistent(l_Lean_Meta_Grind_instHashableEMatchTheoremKind);
l_Lean_Meta_Grind_instInhabitedEMatchTheorem = _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorem();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorem);
l_Lean_Meta_Grind_instInhabitedEMatchTheorems = _init_l_Lean_Meta_Grind_instInhabitedEMatchTheorems();
lean_mark_persistent(l_Lean_Meta_Grind_instInhabitedEMatchTheorems);
if (builtin) {res = l_Lean_Meta_Grind_initFn____x40_Lean_Meta_Tactic_Grind_EMatchTheorem___hyg_2570_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt = lean_io_result_get_value(res);
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_ematchTheoremsExt);
lean_dec_ref(res);
}l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_forbiddenDeclNames = _init_l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_forbiddenDeclNames();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_forbiddenDeclNames);
l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare = _init_l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare();
lean_mark_persistent(l___private_Lean_Meta_Tactic_Grind_EMatchTheorem_0__Lean_Meta_Grind_dontCare);
l_Lean_Meta_Grind_NormalizePattern_instReprPatternArgKind = _init_l_Lean_Meta_Grind_NormalizePattern_instReprPatternArgKind();
lean_mark_persistent(l_Lean_Meta_Grind_NormalizePattern_instReprPatternArgKind);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
