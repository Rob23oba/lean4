// Lean compiler output
// Module: Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis
// Imports: Init.Data.SInt.Basic Lean.Elab.Tactic.BVDecide.Frontend.Normalize.Basic
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
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addMessageContextFull___at___Lean_Meta_recordSynthPendingFailure_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Expr_isConst___boxed(lean_object*);
lean_object* l_Lean_Level_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getNatValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Meta_congrArg_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isApp(lean_object*);
lean_object* l_Lean_Level_succ___override(lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isBuiltIn(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Level_max___override(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
extern lean_object* l_Lean_ForEachExprWhere_initCache;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass;
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_cleanupAnnotations(lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_List_head_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numTypeFormers(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkCasesOnName(lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_builtinTypes;
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__1(lean_object*, size_t, size_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withMVarContextImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Match_instInhabitedDiscrInfo;
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__2(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* l_Lean_Expr_constName_x3f(lean_object*);
uint64_t l_Lean_Expr_hash(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_typeCasesRelevant(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isLet(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_mod(size_t, size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_LocalDecl_isImplementationDetail(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__3(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppNumArgs(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFnCleanup___redArg(lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__0(lean_object*, lean_object*);
uint8_t l_Lean_isStructure(lean_object*, lean_object*);
uint8_t l_instDecidableNot___redArg(uint8_t);
uint8_t l_Lean_Expr_isProp(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_findIdx_x3f_loop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getType___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_InductiveVal_numCtors(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instMonadMetaM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isBuiltIn___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Level_imax___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_array_get_size(x_5);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_dec_eq(x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
if (x_4 == 0)
{
goto block_24;
}
else
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_1);
x_28 = lean_box(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
return x_29;
}
}
else
{
goto block_24;
}
block_24:
{
if (lean_obj_tag(x_6) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_ctor_get(x_6, 0);
x_13 = lean_ctor_get(x_6, 1);
lean_inc(x_1);
x_14 = lean_array_get(x_1, x_2, x_3);
x_15 = lean_expr_eqv(x_12, x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_1);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_11);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_get(x_1, x_5, x_3);
x_19 = lean_expr_eqv(x_18, x_13);
lean_dec(x_18);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; 
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_11);
return x_23;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_mkCasesOnName(x_11);
x_13 = l_Lean_Expr_isConstOf(x_2, x_12);
lean_dec(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_16 = l_Lean_instInhabitedExpr;
x_41 = lean_array_get_size(x_3);
x_42 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_43 = lean_unsigned_to_nat(2u);
x_44 = lean_nat_add(x_42, x_43);
lean_dec(x_42);
x_45 = lean_nat_dec_eq(x_41, x_44);
lean_dec(x_44);
lean_dec(x_41);
if (x_45 == 0)
{
if (x_13 == 0)
{
goto block_40;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_9);
return x_47;
}
}
else
{
goto block_40;
}
block_24:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_array_get(x_16, x_3, x_18);
x_20 = lean_array_get(x_16, x_4, x_18);
lean_dec(x_4);
x_21 = lean_expr_eqv(x_19, x_20);
lean_dec(x_20);
lean_dec(x_19);
x_22 = lean_box(x_21);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
return x_23;
}
block_40:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; 
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_box(x_13);
lean_inc(x_4);
x_27 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___lam__0___boxed), 11, 4);
lean_closure_set(x_27, 0, x_16);
lean_closure_set(x_27, 1, x_4);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_26);
x_28 = lean_array_get(x_16, x_3, x_25);
x_29 = lean_box(0);
x_30 = lean_unbox(x_29);
x_31 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_28, x_27, x_30, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_unbox(x_32);
lean_dec(x_32);
if (x_33 == 0)
{
if (x_13 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
lean_dec(x_31);
x_17 = x_34;
goto block_24;
}
else
{
uint8_t x_35; 
lean_dec(x_4);
x_35 = !lean_is_exclusive(x_31);
if (x_35 == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_31, 0);
lean_dec(x_36);
lean_ctor_set(x_31, 0, x_29);
return x_31;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_31, 1);
lean_inc(x_37);
lean_dec(x_31);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_29);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
lean_dec(x_31);
x_17 = x_39;
goto block_24;
}
}
else
{
lean_dec(x_4);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___lam__0(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_box(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_2);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_9 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifySimpleEnum", 78, 78);
x_10 = lean_unsigned_to_nat(142u);
x_11 = lean_unsigned_to_nat(85u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT uint8_t l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_name_eq(x_4, x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_4, 1);
x_34 = lean_nat_dec_lt(x_6, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_36 = l_Lean_instInhabitedExpr;
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_add(x_6, x_39);
x_41 = lean_array_get(x_36, x_1, x_40);
lean_dec(x_40);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Expr_bvar___override(x_42);
x_44 = lean_unbox(x_37);
x_45 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_44, x_38, x_43, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_43);
x_18 = x_45;
goto block_32;
}
case 1:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Expr_fvar___override(x_46);
x_48 = lean_unbox(x_37);
x_49 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_48, x_38, x_47, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_47);
x_18 = x_49;
goto block_32;
}
case 2:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec(x_41);
x_51 = l_Lean_Expr_mvar___override(x_50);
x_52 = lean_unbox(x_37);
x_53 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_52, x_38, x_51, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_51);
x_18 = x_53;
goto block_32;
}
case 3:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Lean_Expr_sort___override(x_54);
x_56 = lean_unbox(x_37);
x_57 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_56, x_38, x_55, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_55);
x_18 = x_57;
goto block_32;
}
case 4:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_41, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_dec(x_41);
x_60 = l_Lean_Expr_const___override(x_58, x_59);
x_61 = lean_unbox(x_37);
x_62 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_61, x_38, x_60, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_60);
x_18 = x_62;
goto block_32;
}
case 5:
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_41, 0);
lean_inc(x_64);
lean_dec(x_41);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Expr_bvar___override(x_65);
x_67 = l_Lean_Expr_app___override(x_64, x_66);
x_68 = lean_unbox(x_37);
x_69 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_68, x_38, x_67, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_67);
x_18 = x_69;
goto block_32;
}
case 1:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_41, 0);
lean_inc(x_70);
lean_dec(x_41);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_72 = l_Lean_Expr_fvar___override(x_71);
x_73 = l_Lean_Expr_app___override(x_70, x_72);
x_74 = lean_unbox(x_37);
x_75 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_74, x_38, x_73, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_73);
x_18 = x_75;
goto block_32;
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_41, 0);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
lean_dec(x_63);
x_78 = l_Lean_Expr_mvar___override(x_77);
x_79 = l_Lean_Expr_app___override(x_76, x_78);
x_80 = lean_unbox(x_37);
x_81 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_80, x_38, x_79, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_79);
x_18 = x_81;
goto block_32;
}
case 3:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_41, 0);
lean_inc(x_82);
lean_dec(x_41);
x_83 = lean_ctor_get(x_63, 0);
lean_inc(x_83);
lean_dec(x_63);
x_84 = l_Lean_Expr_sort___override(x_83);
x_85 = l_Lean_Expr_app___override(x_82, x_84);
x_86 = lean_unbox(x_37);
x_87 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_86, x_38, x_85, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_85);
x_18 = x_87;
goto block_32;
}
case 4:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_41, 0);
lean_inc(x_88);
lean_dec(x_41);
x_89 = lean_ctor_get(x_63, 0);
lean_inc(x_89);
x_90 = lean_ctor_get(x_63, 1);
lean_inc(x_90);
lean_dec(x_63);
x_91 = lean_box(0);
switch (lean_obj_tag(x_89)) {
case 0:
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; lean_object* x_95; 
x_92 = l_Lean_Expr_const___override(x_91, x_90);
x_93 = l_Lean_Expr_app___override(x_88, x_92);
x_94 = lean_unbox(x_37);
x_95 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_94, x_38, x_93, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_93);
x_18 = x_95;
goto block_32;
}
case 1:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_89, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_89, 1);
lean_inc(x_97);
lean_dec(x_89);
lean_inc(x_97);
x_98 = l_Lean_Name_str___override(x_91, x_97);
switch (lean_obj_tag(x_96)) {
case 0:
{
lean_object* x_99; lean_object* x_100; uint8_t x_101; lean_object* x_102; 
lean_dec(x_97);
x_99 = l_Lean_Expr_const___override(x_98, x_90);
x_100 = l_Lean_Expr_app___override(x_88, x_99);
x_101 = lean_unbox(x_37);
x_102 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_101, x_38, x_100, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_100);
x_18 = x_102;
goto block_32;
}
case 1:
{
lean_object* x_103; 
lean_dec(x_98);
x_103 = lean_ctor_get(x_96, 0);
lean_inc(x_103);
switch (lean_obj_tag(x_103)) {
case 0:
{
lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_104 = lean_ctor_get(x_96, 1);
lean_inc(x_104);
lean_dec(x_96);
x_105 = lean_mk_string_unchecked("Unit", 4, 4);
x_106 = lean_string_dec_eq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; lean_object* x_112; 
lean_dec(x_105);
x_107 = l_Lean_Name_str___override(x_91, x_104);
x_108 = l_Lean_Name_str___override(x_107, x_97);
x_109 = l_Lean_Expr_const___override(x_108, x_90);
x_110 = l_Lean_Expr_app___override(x_88, x_109);
x_111 = lean_unbox(x_37);
x_112 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_111, x_38, x_110, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_110);
x_18 = x_112;
goto block_32;
}
else
{
lean_object* x_113; uint8_t x_114; 
lean_dec(x_104);
x_113 = lean_mk_string_unchecked("unit", 4, 4);
x_114 = lean_string_dec_eq(x_97, x_113);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; uint8_t x_119; lean_object* x_120; 
lean_dec(x_113);
x_115 = l_Lean_Name_str___override(x_91, x_105);
x_116 = l_Lean_Name_str___override(x_115, x_97);
x_117 = l_Lean_Expr_const___override(x_116, x_90);
x_118 = l_Lean_Expr_app___override(x_88, x_117);
x_119 = lean_unbox(x_37);
x_120 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_119, x_38, x_118, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_118);
x_18 = x_120;
goto block_32;
}
else
{
lean_dec(x_97);
if (lean_obj_tag(x_90) == 0)
{
lean_object* x_121; 
lean_dec(x_113);
lean_dec(x_105);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_88);
x_121 = lean_infer_type(x_88, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_121) == 0)
{
uint8_t x_122; 
x_122 = !lean_is_exclusive(x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_123 = lean_ctor_get(x_121, 0);
x_124 = lean_ctor_get(x_121, 1);
x_125 = lean_box(0);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_38);
if (lean_obj_tag(x_123) == 7)
{
lean_object* x_127; lean_object* x_128; uint8_t x_129; 
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
x_128 = lean_ctor_get(x_123, 2);
lean_inc(x_128);
lean_dec(x_123);
x_129 = l_Lean_Expr_hasLooseBVars(x_128);
if (x_129 == 0)
{
switch (lean_obj_tag(x_128)) {
case 0:
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_121);
lean_dec(x_88);
x_130 = lean_ctor_get(x_128, 0);
lean_inc(x_130);
lean_dec(x_128);
x_131 = l_Lean_Expr_bvar___override(x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_127);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_134 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_133, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_133);
x_18 = x_134;
goto block_32;
}
case 1:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_free_object(x_121);
lean_dec(x_88);
x_135 = lean_ctor_get(x_128, 0);
lean_inc(x_135);
lean_dec(x_128);
x_136 = l_Lean_Expr_fvar___override(x_135);
x_137 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_137, 0, x_127);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_138, 0, x_137);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_139 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_138, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_138);
x_18 = x_139;
goto block_32;
}
case 2:
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_free_object(x_121);
lean_dec(x_88);
x_140 = lean_ctor_get(x_128, 0);
lean_inc(x_140);
lean_dec(x_128);
x_141 = l_Lean_Expr_mvar___override(x_140);
x_142 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_142, 0, x_127);
lean_ctor_set(x_142, 1, x_141);
x_143 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_143, 0, x_142);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_144 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_143, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_143);
x_18 = x_144;
goto block_32;
}
case 3:
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
lean_free_object(x_121);
lean_dec(x_88);
x_145 = lean_ctor_get(x_128, 0);
lean_inc(x_145);
lean_dec(x_128);
x_146 = l_Lean_Expr_sort___override(x_145);
x_147 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_147, 0, x_127);
lean_ctor_set(x_147, 1, x_146);
x_148 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_148, 0, x_147);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_149 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_148, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_148);
x_18 = x_149;
goto block_32;
}
case 4:
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_free_object(x_121);
lean_dec(x_88);
x_150 = lean_ctor_get(x_128, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_128, 1);
lean_inc(x_151);
lean_dec(x_128);
x_152 = l_Lean_Expr_const___override(x_150, x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_127);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_155 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_154, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_154);
x_18 = x_155;
goto block_32;
}
case 5:
{
lean_object* x_156; 
x_156 = lean_ctor_get(x_128, 1);
lean_inc(x_156);
switch (lean_obj_tag(x_156)) {
case 0:
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_free_object(x_121);
lean_dec(x_88);
x_157 = lean_ctor_get(x_128, 0);
lean_inc(x_157);
lean_dec(x_128);
x_158 = lean_ctor_get(x_156, 0);
lean_inc(x_158);
lean_dec(x_156);
x_159 = l_Lean_Expr_bvar___override(x_158);
x_160 = l_Lean_Expr_app___override(x_157, x_159);
x_161 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_161, 0, x_127);
lean_ctor_set(x_161, 1, x_160);
x_162 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_163 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_162, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_162);
x_18 = x_163;
goto block_32;
}
case 1:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
lean_free_object(x_121);
lean_dec(x_88);
x_164 = lean_ctor_get(x_128, 0);
lean_inc(x_164);
lean_dec(x_128);
x_165 = lean_ctor_get(x_156, 0);
lean_inc(x_165);
lean_dec(x_156);
x_166 = l_Lean_Expr_fvar___override(x_165);
x_167 = l_Lean_Expr_app___override(x_164, x_166);
x_168 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_168, 0, x_127);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_169, 0, x_168);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_170 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_169, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_169);
x_18 = x_170;
goto block_32;
}
case 2:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_free_object(x_121);
lean_dec(x_88);
x_171 = lean_ctor_get(x_128, 0);
lean_inc(x_171);
lean_dec(x_128);
x_172 = lean_ctor_get(x_156, 0);
lean_inc(x_172);
lean_dec(x_156);
x_173 = l_Lean_Expr_mvar___override(x_172);
x_174 = l_Lean_Expr_app___override(x_171, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_127);
lean_ctor_set(x_175, 1, x_174);
x_176 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_176, 0, x_175);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_177 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_176, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_176);
x_18 = x_177;
goto block_32;
}
case 3:
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
lean_free_object(x_121);
lean_dec(x_88);
x_178 = lean_ctor_get(x_128, 0);
lean_inc(x_178);
lean_dec(x_128);
x_179 = lean_ctor_get(x_156, 0);
lean_inc(x_179);
lean_dec(x_156);
x_180 = l_Lean_Expr_sort___override(x_179);
x_181 = l_Lean_Expr_app___override(x_178, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_127);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_183, 0, x_182);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_184 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_183, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_183);
x_18 = x_184;
goto block_32;
}
case 4:
{
lean_object* x_185; 
x_185 = lean_ctor_get(x_156, 1);
lean_inc(x_185);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_128);
lean_dec(x_127);
x_186 = lean_ctor_get(x_156, 0);
lean_inc(x_186);
lean_dec(x_156);
x_187 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_187, 0, x_186);
x_188 = lean_unsigned_to_nat(0u);
x_189 = l_Array_findIdx_x3f_loop___redArg(x_187, x_2, x_188);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; 
lean_free_object(x_121);
lean_dec(x_88);
x_190 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_191 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifySimpleEnum", 78, 78);
x_192 = lean_unsigned_to_nat(143u);
x_193 = lean_unsigned_to_nat(72u);
x_194 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_195 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_190, x_191, x_192, x_193, x_194);
lean_dec(x_194);
lean_dec(x_191);
lean_dec(x_190);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_196 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_195, x_7, x_8, x_9, x_10, x_124);
if (lean_obj_tag(x_196) == 0)
{
lean_object* x_197; 
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
lean_dec(x_196);
x_12 = x_126;
x_13 = x_197;
goto block_17;
}
else
{
uint8_t x_198; 
lean_dec(x_126);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_198 = !lean_is_exclusive(x_196);
if (x_198 == 0)
{
return x_196;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_196, 0);
x_200 = lean_ctor_get(x_196, 1);
lean_inc(x_200);
lean_inc(x_199);
lean_dec(x_196);
x_201 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_201, 0, x_199);
lean_ctor_set(x_201, 1, x_200);
return x_201;
}
}
}
else
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_189);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; uint8_t x_206; 
x_203 = lean_ctor_get(x_189, 0);
x_204 = lean_nat_add(x_203, x_39);
lean_dec(x_203);
x_205 = lean_array_get(x_36, x_3, x_204);
lean_dec(x_204);
x_206 = lean_expr_eqv(x_88, x_205);
lean_dec(x_205);
lean_dec(x_88);
if (x_206 == 0)
{
lean_object* x_207; 
lean_dec(x_126);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_189, 0, x_37);
x_207 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_207, 0, x_189);
lean_ctor_set(x_207, 1, x_38);
lean_ctor_set(x_121, 0, x_207);
return x_121;
}
else
{
lean_free_object(x_189);
lean_free_object(x_121);
x_12 = x_126;
x_13 = x_124;
goto block_17;
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; uint8_t x_211; 
x_208 = lean_ctor_get(x_189, 0);
lean_inc(x_208);
lean_dec(x_189);
x_209 = lean_nat_add(x_208, x_39);
lean_dec(x_208);
x_210 = lean_array_get(x_36, x_3, x_209);
lean_dec(x_209);
x_211 = lean_expr_eqv(x_88, x_210);
lean_dec(x_210);
lean_dec(x_88);
if (x_211 == 0)
{
lean_object* x_212; lean_object* x_213; 
lean_dec(x_126);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_212 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_212, 0, x_37);
x_213 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_213, 0, x_212);
lean_ctor_set(x_213, 1, x_38);
lean_ctor_set(x_121, 0, x_213);
return x_121;
}
else
{
lean_free_object(x_121);
x_12 = x_126;
x_13 = x_124;
goto block_17;
}
}
}
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; uint8_t x_217; 
lean_free_object(x_121);
lean_dec(x_88);
x_214 = lean_ctor_get(x_128, 0);
lean_inc(x_214);
lean_dec(x_128);
x_215 = lean_ctor_get(x_156, 0);
lean_inc(x_215);
lean_dec(x_156);
lean_inc(x_185);
x_216 = l_Lean_Expr_const___override(x_215, x_185);
x_217 = !lean_is_exclusive(x_185);
if (x_217 == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
x_218 = lean_ctor_get(x_185, 1);
lean_dec(x_218);
x_219 = lean_ctor_get(x_185, 0);
lean_dec(x_219);
x_220 = l_Lean_Expr_app___override(x_214, x_216);
lean_ctor_set_tag(x_185, 0);
lean_ctor_set(x_185, 1, x_220);
lean_ctor_set(x_185, 0, x_127);
x_221 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_221, 0, x_185);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_222 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_221, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_221);
x_18 = x_222;
goto block_32;
}
else
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
lean_dec(x_185);
x_223 = l_Lean_Expr_app___override(x_214, x_216);
x_224 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_224, 0, x_127);
lean_ctor_set(x_224, 1, x_223);
x_225 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_225, 0, x_224);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_226 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_225, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_225);
x_18 = x_226;
goto block_32;
}
}
}
case 5:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
lean_free_object(x_121);
lean_dec(x_88);
x_227 = lean_ctor_get(x_128, 0);
lean_inc(x_227);
lean_dec(x_128);
x_228 = lean_ctor_get(x_156, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_156, 1);
lean_inc(x_229);
lean_dec(x_156);
x_230 = l_Lean_Expr_app___override(x_228, x_229);
x_231 = l_Lean_Expr_app___override(x_227, x_230);
x_232 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_232, 0, x_127);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_232);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_234 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_233, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_233);
x_18 = x_234;
goto block_32;
}
case 6:
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; uint8_t x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_free_object(x_121);
lean_dec(x_88);
x_235 = lean_ctor_get(x_128, 0);
lean_inc(x_235);
lean_dec(x_128);
x_236 = lean_ctor_get(x_156, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_156, 1);
lean_inc(x_237);
x_238 = lean_ctor_get(x_156, 2);
lean_inc(x_238);
x_239 = lean_ctor_get_uint8(x_156, sizeof(void*)*3 + 8);
lean_dec(x_156);
x_240 = l_Lean_Expr_lam___override(x_236, x_237, x_238, x_239);
x_241 = l_Lean_Expr_app___override(x_235, x_240);
x_242 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_242, 0, x_127);
lean_ctor_set(x_242, 1, x_241);
x_243 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_243, 0, x_242);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_244 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_243, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_243);
x_18 = x_244;
goto block_32;
}
case 7:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; uint8_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_free_object(x_121);
lean_dec(x_88);
x_245 = lean_ctor_get(x_128, 0);
lean_inc(x_245);
lean_dec(x_128);
x_246 = lean_ctor_get(x_156, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_156, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_156, 2);
lean_inc(x_248);
x_249 = lean_ctor_get_uint8(x_156, sizeof(void*)*3 + 8);
lean_dec(x_156);
x_250 = l_Lean_Expr_forallE___override(x_246, x_247, x_248, x_249);
x_251 = l_Lean_Expr_app___override(x_245, x_250);
x_252 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_252, 0, x_127);
lean_ctor_set(x_252, 1, x_251);
x_253 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_253, 0, x_252);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_254 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_253, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_253);
x_18 = x_254;
goto block_32;
}
case 8:
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; 
lean_free_object(x_121);
lean_dec(x_88);
x_255 = lean_ctor_get(x_128, 0);
lean_inc(x_255);
lean_dec(x_128);
x_256 = lean_ctor_get(x_156, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_156, 1);
lean_inc(x_257);
x_258 = lean_ctor_get(x_156, 2);
lean_inc(x_258);
x_259 = lean_ctor_get(x_156, 3);
lean_inc(x_259);
x_260 = lean_ctor_get_uint8(x_156, sizeof(void*)*4 + 8);
lean_dec(x_156);
x_261 = l_Lean_Expr_letE___override(x_256, x_257, x_258, x_259, x_260);
x_262 = l_Lean_Expr_app___override(x_255, x_261);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_127);
lean_ctor_set(x_263, 1, x_262);
x_264 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_264, 0, x_263);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_265 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_264, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_264);
x_18 = x_265;
goto block_32;
}
case 9:
{
lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_free_object(x_121);
lean_dec(x_88);
x_266 = lean_ctor_get(x_128, 0);
lean_inc(x_266);
lean_dec(x_128);
x_267 = lean_ctor_get(x_156, 0);
lean_inc(x_267);
lean_dec(x_156);
x_268 = l_Lean_Expr_lit___override(x_267);
x_269 = l_Lean_Expr_app___override(x_266, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_127);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_272 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_271, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_271);
x_18 = x_272;
goto block_32;
}
case 10:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
lean_free_object(x_121);
lean_dec(x_88);
x_273 = lean_ctor_get(x_128, 0);
lean_inc(x_273);
lean_dec(x_128);
x_274 = lean_ctor_get(x_156, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_156, 1);
lean_inc(x_275);
lean_dec(x_156);
x_276 = l_Lean_Expr_mdata___override(x_274, x_275);
x_277 = l_Lean_Expr_app___override(x_273, x_276);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_127);
lean_ctor_set(x_278, 1, x_277);
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_278);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_280 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_279, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_279);
x_18 = x_280;
goto block_32;
}
default: 
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
lean_free_object(x_121);
lean_dec(x_88);
x_281 = lean_ctor_get(x_128, 0);
lean_inc(x_281);
lean_dec(x_128);
x_282 = lean_ctor_get(x_156, 0);
lean_inc(x_282);
x_283 = lean_ctor_get(x_156, 1);
lean_inc(x_283);
x_284 = lean_ctor_get(x_156, 2);
lean_inc(x_284);
lean_dec(x_156);
x_285 = l_Lean_Expr_proj___override(x_282, x_283, x_284);
x_286 = l_Lean_Expr_app___override(x_281, x_285);
x_287 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_287, 0, x_127);
lean_ctor_set(x_287, 1, x_286);
x_288 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_288, 0, x_287);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_289 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_288, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_288);
x_18 = x_289;
goto block_32;
}
}
}
case 6:
{
lean_object* x_290; lean_object* x_291; lean_object* x_292; uint8_t x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
lean_free_object(x_121);
lean_dec(x_88);
x_290 = lean_ctor_get(x_128, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_128, 1);
lean_inc(x_291);
x_292 = lean_ctor_get(x_128, 2);
lean_inc(x_292);
x_293 = lean_ctor_get_uint8(x_128, sizeof(void*)*3 + 8);
lean_dec(x_128);
x_294 = l_Lean_Expr_lam___override(x_290, x_291, x_292, x_293);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_127);
lean_ctor_set(x_295, 1, x_294);
x_296 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_296, 0, x_295);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_297 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_296, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_296);
x_18 = x_297;
goto block_32;
}
case 7:
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; uint8_t x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_free_object(x_121);
lean_dec(x_88);
x_298 = lean_ctor_get(x_128, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_128, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_128, 2);
lean_inc(x_300);
x_301 = lean_ctor_get_uint8(x_128, sizeof(void*)*3 + 8);
lean_dec(x_128);
x_302 = l_Lean_Expr_forallE___override(x_298, x_299, x_300, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_127);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_305 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_304, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_304);
x_18 = x_305;
goto block_32;
}
case 8:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; uint8_t x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_free_object(x_121);
lean_dec(x_88);
x_306 = lean_ctor_get(x_128, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_128, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_128, 2);
lean_inc(x_308);
x_309 = lean_ctor_get(x_128, 3);
lean_inc(x_309);
x_310 = lean_ctor_get_uint8(x_128, sizeof(void*)*4 + 8);
lean_dec(x_128);
x_311 = l_Lean_Expr_letE___override(x_306, x_307, x_308, x_309, x_310);
x_312 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_312, 0, x_127);
lean_ctor_set(x_312, 1, x_311);
x_313 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_313, 0, x_312);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_314 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_313, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_313);
x_18 = x_314;
goto block_32;
}
case 9:
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
lean_free_object(x_121);
lean_dec(x_88);
x_315 = lean_ctor_get(x_128, 0);
lean_inc(x_315);
lean_dec(x_128);
x_316 = l_Lean_Expr_lit___override(x_315);
x_317 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_317, 0, x_127);
lean_ctor_set(x_317, 1, x_316);
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_317);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_319 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_318, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_318);
x_18 = x_319;
goto block_32;
}
case 10:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_free_object(x_121);
lean_dec(x_88);
x_320 = lean_ctor_get(x_128, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_128, 1);
lean_inc(x_321);
lean_dec(x_128);
x_322 = l_Lean_Expr_mdata___override(x_320, x_321);
x_323 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_323, 0, x_127);
lean_ctor_set(x_323, 1, x_322);
x_324 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_324, 0, x_323);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_325 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_324, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_324);
x_18 = x_325;
goto block_32;
}
default: 
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; 
lean_free_object(x_121);
lean_dec(x_88);
x_326 = lean_ctor_get(x_128, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_128, 1);
lean_inc(x_327);
x_328 = lean_ctor_get(x_128, 2);
lean_inc(x_328);
lean_dec(x_128);
x_329 = l_Lean_Expr_proj___override(x_326, x_327, x_328);
x_330 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_330, 0, x_127);
lean_ctor_set(x_330, 1, x_329);
x_331 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_331, 0, x_330);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_332 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_331, x_7, x_8, x_9, x_10, x_124);
lean_dec(x_331);
x_18 = x_332;
goto block_32;
}
}
}
else
{
lean_object* x_333; lean_object* x_334; 
lean_dec(x_128);
lean_dec(x_127);
lean_free_object(x_121);
lean_dec(x_88);
x_333 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_334 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_333, x_7, x_8, x_9, x_10, x_124);
x_18 = x_334;
goto block_32;
}
}
else
{
lean_object* x_335; lean_object* x_336; 
lean_free_object(x_121);
lean_dec(x_123);
lean_dec(x_88);
x_335 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_336 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_126, x_335, x_7, x_8, x_9, x_10, x_124);
x_18 = x_336;
goto block_32;
}
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; 
x_337 = lean_ctor_get(x_121, 0);
x_338 = lean_ctor_get(x_121, 1);
lean_inc(x_338);
lean_inc(x_337);
lean_dec(x_121);
x_339 = lean_box(0);
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_339);
lean_ctor_set(x_340, 1, x_38);
if (lean_obj_tag(x_337) == 7)
{
lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_341 = lean_ctor_get(x_337, 1);
lean_inc(x_341);
x_342 = lean_ctor_get(x_337, 2);
lean_inc(x_342);
lean_dec(x_337);
x_343 = l_Lean_Expr_hasLooseBVars(x_342);
if (x_343 == 0)
{
switch (lean_obj_tag(x_342)) {
case 0:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_88);
x_344 = lean_ctor_get(x_342, 0);
lean_inc(x_344);
lean_dec(x_342);
x_345 = l_Lean_Expr_bvar___override(x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_341);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_346);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_348 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_347, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_347);
x_18 = x_348;
goto block_32;
}
case 1:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_88);
x_349 = lean_ctor_get(x_342, 0);
lean_inc(x_349);
lean_dec(x_342);
x_350 = l_Lean_Expr_fvar___override(x_349);
x_351 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_351, 0, x_341);
lean_ctor_set(x_351, 1, x_350);
x_352 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_352, 0, x_351);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_353 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_352, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_352);
x_18 = x_353;
goto block_32;
}
case 2:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_88);
x_354 = lean_ctor_get(x_342, 0);
lean_inc(x_354);
lean_dec(x_342);
x_355 = l_Lean_Expr_mvar___override(x_354);
x_356 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_356, 0, x_341);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_357, 0, x_356);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_358 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_357, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_357);
x_18 = x_358;
goto block_32;
}
case 3:
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; 
lean_dec(x_88);
x_359 = lean_ctor_get(x_342, 0);
lean_inc(x_359);
lean_dec(x_342);
x_360 = l_Lean_Expr_sort___override(x_359);
x_361 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_361, 0, x_341);
lean_ctor_set(x_361, 1, x_360);
x_362 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_362, 0, x_361);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_363 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_362, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_362);
x_18 = x_363;
goto block_32;
}
case 4:
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_88);
x_364 = lean_ctor_get(x_342, 0);
lean_inc(x_364);
x_365 = lean_ctor_get(x_342, 1);
lean_inc(x_365);
lean_dec(x_342);
x_366 = l_Lean_Expr_const___override(x_364, x_365);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_341);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_369 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_368, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_368);
x_18 = x_369;
goto block_32;
}
case 5:
{
lean_object* x_370; 
x_370 = lean_ctor_get(x_342, 1);
lean_inc(x_370);
switch (lean_obj_tag(x_370)) {
case 0:
{
lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_88);
x_371 = lean_ctor_get(x_342, 0);
lean_inc(x_371);
lean_dec(x_342);
x_372 = lean_ctor_get(x_370, 0);
lean_inc(x_372);
lean_dec(x_370);
x_373 = l_Lean_Expr_bvar___override(x_372);
x_374 = l_Lean_Expr_app___override(x_371, x_373);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_341);
lean_ctor_set(x_375, 1, x_374);
x_376 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_376, 0, x_375);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_377 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_376, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_376);
x_18 = x_377;
goto block_32;
}
case 1:
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_88);
x_378 = lean_ctor_get(x_342, 0);
lean_inc(x_378);
lean_dec(x_342);
x_379 = lean_ctor_get(x_370, 0);
lean_inc(x_379);
lean_dec(x_370);
x_380 = l_Lean_Expr_fvar___override(x_379);
x_381 = l_Lean_Expr_app___override(x_378, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_341);
lean_ctor_set(x_382, 1, x_381);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_384 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_383, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_383);
x_18 = x_384;
goto block_32;
}
case 2:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_88);
x_385 = lean_ctor_get(x_342, 0);
lean_inc(x_385);
lean_dec(x_342);
x_386 = lean_ctor_get(x_370, 0);
lean_inc(x_386);
lean_dec(x_370);
x_387 = l_Lean_Expr_mvar___override(x_386);
x_388 = l_Lean_Expr_app___override(x_385, x_387);
x_389 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_389, 0, x_341);
lean_ctor_set(x_389, 1, x_388);
x_390 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_390, 0, x_389);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_391 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_390, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_390);
x_18 = x_391;
goto block_32;
}
case 3:
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_dec(x_88);
x_392 = lean_ctor_get(x_342, 0);
lean_inc(x_392);
lean_dec(x_342);
x_393 = lean_ctor_get(x_370, 0);
lean_inc(x_393);
lean_dec(x_370);
x_394 = l_Lean_Expr_sort___override(x_393);
x_395 = l_Lean_Expr_app___override(x_392, x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_341);
lean_ctor_set(x_396, 1, x_395);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_398 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_397, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_397);
x_18 = x_398;
goto block_32;
}
case 4:
{
lean_object* x_399; 
x_399 = lean_ctor_get(x_370, 1);
lean_inc(x_399);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; 
lean_dec(x_342);
lean_dec(x_341);
x_400 = lean_ctor_get(x_370, 0);
lean_inc(x_400);
lean_dec(x_370);
x_401 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_401, 0, x_400);
x_402 = lean_unsigned_to_nat(0u);
x_403 = l_Array_findIdx_x3f_loop___redArg(x_401, x_2, x_402);
if (lean_obj_tag(x_403) == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; 
lean_dec(x_88);
x_404 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_405 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifySimpleEnum", 78, 78);
x_406 = lean_unsigned_to_nat(143u);
x_407 = lean_unsigned_to_nat(72u);
x_408 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_409 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_404, x_405, x_406, x_407, x_408);
lean_dec(x_408);
lean_dec(x_405);
lean_dec(x_404);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_410 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_409, x_7, x_8, x_9, x_10, x_338);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_410, 1);
lean_inc(x_411);
lean_dec(x_410);
x_12 = x_340;
x_13 = x_411;
goto block_17;
}
else
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
lean_dec(x_340);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_412 = lean_ctor_get(x_410, 0);
lean_inc(x_412);
x_413 = lean_ctor_get(x_410, 1);
lean_inc(x_413);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_414 = x_410;
} else {
 lean_dec_ref(x_410);
 x_414 = lean_box(0);
}
if (lean_is_scalar(x_414)) {
 x_415 = lean_alloc_ctor(1, 2, 0);
} else {
 x_415 = x_414;
}
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_413);
return x_415;
}
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint8_t x_420; 
x_416 = lean_ctor_get(x_403, 0);
lean_inc(x_416);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 x_417 = x_403;
} else {
 lean_dec_ref(x_403);
 x_417 = lean_box(0);
}
x_418 = lean_nat_add(x_416, x_39);
lean_dec(x_416);
x_419 = lean_array_get(x_36, x_3, x_418);
lean_dec(x_418);
x_420 = lean_expr_eqv(x_88, x_419);
lean_dec(x_419);
lean_dec(x_88);
if (x_420 == 0)
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_340);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_417)) {
 x_421 = lean_alloc_ctor(1, 1, 0);
} else {
 x_421 = x_417;
}
lean_ctor_set(x_421, 0, x_37);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_38);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_338);
return x_423;
}
else
{
lean_dec(x_417);
x_12 = x_340;
x_13 = x_338;
goto block_17;
}
}
}
else
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; 
lean_dec(x_88);
x_424 = lean_ctor_get(x_342, 0);
lean_inc(x_424);
lean_dec(x_342);
x_425 = lean_ctor_get(x_370, 0);
lean_inc(x_425);
lean_dec(x_370);
lean_inc(x_399);
x_426 = l_Lean_Expr_const___override(x_425, x_399);
if (lean_is_exclusive(x_399)) {
 lean_ctor_release(x_399, 0);
 lean_ctor_release(x_399, 1);
 x_427 = x_399;
} else {
 lean_dec_ref(x_399);
 x_427 = lean_box(0);
}
x_428 = l_Lean_Expr_app___override(x_424, x_426);
if (lean_is_scalar(x_427)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_427;
 lean_ctor_set_tag(x_429, 0);
}
lean_ctor_set(x_429, 0, x_341);
lean_ctor_set(x_429, 1, x_428);
x_430 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_430, 0, x_429);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_431 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_430, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_430);
x_18 = x_431;
goto block_32;
}
}
case 5:
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; 
lean_dec(x_88);
x_432 = lean_ctor_get(x_342, 0);
lean_inc(x_432);
lean_dec(x_342);
x_433 = lean_ctor_get(x_370, 0);
lean_inc(x_433);
x_434 = lean_ctor_get(x_370, 1);
lean_inc(x_434);
lean_dec(x_370);
x_435 = l_Lean_Expr_app___override(x_433, x_434);
x_436 = l_Lean_Expr_app___override(x_432, x_435);
x_437 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_437, 0, x_341);
lean_ctor_set(x_437, 1, x_436);
x_438 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_438, 0, x_437);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_439 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_438, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_438);
x_18 = x_439;
goto block_32;
}
case 6:
{
lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; uint8_t x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_88);
x_440 = lean_ctor_get(x_342, 0);
lean_inc(x_440);
lean_dec(x_342);
x_441 = lean_ctor_get(x_370, 0);
lean_inc(x_441);
x_442 = lean_ctor_get(x_370, 1);
lean_inc(x_442);
x_443 = lean_ctor_get(x_370, 2);
lean_inc(x_443);
x_444 = lean_ctor_get_uint8(x_370, sizeof(void*)*3 + 8);
lean_dec(x_370);
x_445 = l_Lean_Expr_lam___override(x_441, x_442, x_443, x_444);
x_446 = l_Lean_Expr_app___override(x_440, x_445);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_341);
lean_ctor_set(x_447, 1, x_446);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_449 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_448, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_448);
x_18 = x_449;
goto block_32;
}
case 7:
{
lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; uint8_t x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_88);
x_450 = lean_ctor_get(x_342, 0);
lean_inc(x_450);
lean_dec(x_342);
x_451 = lean_ctor_get(x_370, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_370, 1);
lean_inc(x_452);
x_453 = lean_ctor_get(x_370, 2);
lean_inc(x_453);
x_454 = lean_ctor_get_uint8(x_370, sizeof(void*)*3 + 8);
lean_dec(x_370);
x_455 = l_Lean_Expr_forallE___override(x_451, x_452, x_453, x_454);
x_456 = l_Lean_Expr_app___override(x_450, x_455);
x_457 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_457, 0, x_341);
lean_ctor_set(x_457, 1, x_456);
x_458 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_458, 0, x_457);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_459 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_458, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_458);
x_18 = x_459;
goto block_32;
}
case 8:
{
lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_88);
x_460 = lean_ctor_get(x_342, 0);
lean_inc(x_460);
lean_dec(x_342);
x_461 = lean_ctor_get(x_370, 0);
lean_inc(x_461);
x_462 = lean_ctor_get(x_370, 1);
lean_inc(x_462);
x_463 = lean_ctor_get(x_370, 2);
lean_inc(x_463);
x_464 = lean_ctor_get(x_370, 3);
lean_inc(x_464);
x_465 = lean_ctor_get_uint8(x_370, sizeof(void*)*4 + 8);
lean_dec(x_370);
x_466 = l_Lean_Expr_letE___override(x_461, x_462, x_463, x_464, x_465);
x_467 = l_Lean_Expr_app___override(x_460, x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_341);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_468);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_470 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_469, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_469);
x_18 = x_470;
goto block_32;
}
case 9:
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; 
lean_dec(x_88);
x_471 = lean_ctor_get(x_342, 0);
lean_inc(x_471);
lean_dec(x_342);
x_472 = lean_ctor_get(x_370, 0);
lean_inc(x_472);
lean_dec(x_370);
x_473 = l_Lean_Expr_lit___override(x_472);
x_474 = l_Lean_Expr_app___override(x_471, x_473);
x_475 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_475, 0, x_341);
lean_ctor_set(x_475, 1, x_474);
x_476 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_476, 0, x_475);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_477 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_476, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_476);
x_18 = x_477;
goto block_32;
}
case 10:
{
lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_88);
x_478 = lean_ctor_get(x_342, 0);
lean_inc(x_478);
lean_dec(x_342);
x_479 = lean_ctor_get(x_370, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_370, 1);
lean_inc(x_480);
lean_dec(x_370);
x_481 = l_Lean_Expr_mdata___override(x_479, x_480);
x_482 = l_Lean_Expr_app___override(x_478, x_481);
x_483 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_483, 0, x_341);
lean_ctor_set(x_483, 1, x_482);
x_484 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_484, 0, x_483);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_485 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_484, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_484);
x_18 = x_485;
goto block_32;
}
default: 
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_88);
x_486 = lean_ctor_get(x_342, 0);
lean_inc(x_486);
lean_dec(x_342);
x_487 = lean_ctor_get(x_370, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_370, 1);
lean_inc(x_488);
x_489 = lean_ctor_get(x_370, 2);
lean_inc(x_489);
lean_dec(x_370);
x_490 = l_Lean_Expr_proj___override(x_487, x_488, x_489);
x_491 = l_Lean_Expr_app___override(x_486, x_490);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_341);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_493, 0, x_492);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_494 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_493, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_493);
x_18 = x_494;
goto block_32;
}
}
}
case 6:
{
lean_object* x_495; lean_object* x_496; lean_object* x_497; uint8_t x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; 
lean_dec(x_88);
x_495 = lean_ctor_get(x_342, 0);
lean_inc(x_495);
x_496 = lean_ctor_get(x_342, 1);
lean_inc(x_496);
x_497 = lean_ctor_get(x_342, 2);
lean_inc(x_497);
x_498 = lean_ctor_get_uint8(x_342, sizeof(void*)*3 + 8);
lean_dec(x_342);
x_499 = l_Lean_Expr_lam___override(x_495, x_496, x_497, x_498);
x_500 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_500, 0, x_341);
lean_ctor_set(x_500, 1, x_499);
x_501 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_501, 0, x_500);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_502 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_501, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_501);
x_18 = x_502;
goto block_32;
}
case 7:
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; uint8_t x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; 
lean_dec(x_88);
x_503 = lean_ctor_get(x_342, 0);
lean_inc(x_503);
x_504 = lean_ctor_get(x_342, 1);
lean_inc(x_504);
x_505 = lean_ctor_get(x_342, 2);
lean_inc(x_505);
x_506 = lean_ctor_get_uint8(x_342, sizeof(void*)*3 + 8);
lean_dec(x_342);
x_507 = l_Lean_Expr_forallE___override(x_503, x_504, x_505, x_506);
x_508 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_508, 0, x_341);
lean_ctor_set(x_508, 1, x_507);
x_509 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_509, 0, x_508);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_510 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_509, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_509);
x_18 = x_510;
goto block_32;
}
case 8:
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; uint8_t x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; 
lean_dec(x_88);
x_511 = lean_ctor_get(x_342, 0);
lean_inc(x_511);
x_512 = lean_ctor_get(x_342, 1);
lean_inc(x_512);
x_513 = lean_ctor_get(x_342, 2);
lean_inc(x_513);
x_514 = lean_ctor_get(x_342, 3);
lean_inc(x_514);
x_515 = lean_ctor_get_uint8(x_342, sizeof(void*)*4 + 8);
lean_dec(x_342);
x_516 = l_Lean_Expr_letE___override(x_511, x_512, x_513, x_514, x_515);
x_517 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_517, 0, x_341);
lean_ctor_set(x_517, 1, x_516);
x_518 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_518, 0, x_517);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_519 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_518, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_518);
x_18 = x_519;
goto block_32;
}
case 9:
{
lean_object* x_520; lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; 
lean_dec(x_88);
x_520 = lean_ctor_get(x_342, 0);
lean_inc(x_520);
lean_dec(x_342);
x_521 = l_Lean_Expr_lit___override(x_520);
x_522 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_522, 0, x_341);
lean_ctor_set(x_522, 1, x_521);
x_523 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_523, 0, x_522);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_524 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_523, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_523);
x_18 = x_524;
goto block_32;
}
case 10:
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_88);
x_525 = lean_ctor_get(x_342, 0);
lean_inc(x_525);
x_526 = lean_ctor_get(x_342, 1);
lean_inc(x_526);
lean_dec(x_342);
x_527 = l_Lean_Expr_mdata___override(x_525, x_526);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_341);
lean_ctor_set(x_528, 1, x_527);
x_529 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_529, 0, x_528);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_530 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_529, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_529);
x_18 = x_530;
goto block_32;
}
default: 
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_88);
x_531 = lean_ctor_get(x_342, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_342, 1);
lean_inc(x_532);
x_533 = lean_ctor_get(x_342, 2);
lean_inc(x_533);
lean_dec(x_342);
x_534 = l_Lean_Expr_proj___override(x_531, x_532, x_533);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_341);
lean_ctor_set(x_535, 1, x_534);
x_536 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_536, 0, x_535);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_537 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_536, x_7, x_8, x_9, x_10, x_338);
lean_dec(x_536);
x_18 = x_537;
goto block_32;
}
}
}
else
{
lean_object* x_538; lean_object* x_539; 
lean_dec(x_342);
lean_dec(x_341);
lean_dec(x_88);
x_538 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_539 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_538, x_7, x_8, x_9, x_10, x_338);
x_18 = x_539;
goto block_32;
}
}
else
{
lean_object* x_540; lean_object* x_541; 
lean_dec(x_337);
lean_dec(x_88);
x_540 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_541 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_340, x_540, x_7, x_8, x_9, x_10, x_338);
x_18 = x_541;
goto block_32;
}
}
}
else
{
uint8_t x_542; 
lean_dec(x_88);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_542 = !lean_is_exclusive(x_121);
if (x_542 == 0)
{
return x_121;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
x_543 = lean_ctor_get(x_121, 0);
x_544 = lean_ctor_get(x_121, 1);
lean_inc(x_544);
lean_inc(x_543);
lean_dec(x_121);
x_545 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
return x_545;
}
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; uint8_t x_550; lean_object* x_551; 
x_546 = l_Lean_Name_str___override(x_91, x_105);
x_547 = l_Lean_Name_str___override(x_546, x_113);
x_548 = l_Lean_Expr_const___override(x_547, x_90);
x_549 = l_Lean_Expr_app___override(x_88, x_548);
x_550 = lean_unbox(x_37);
x_551 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_550, x_38, x_549, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_549);
x_18 = x_551;
goto block_32;
}
}
}
}
case 1:
{
lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; uint8_t x_560; lean_object* x_561; 
x_552 = lean_ctor_get(x_96, 1);
lean_inc(x_552);
lean_dec(x_96);
x_553 = lean_ctor_get(x_103, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_103, 1);
lean_inc(x_554);
lean_dec(x_103);
x_555 = l_Lean_Name_str___override(x_553, x_554);
x_556 = l_Lean_Name_str___override(x_555, x_552);
x_557 = l_Lean_Name_str___override(x_556, x_97);
x_558 = l_Lean_Expr_const___override(x_557, x_90);
x_559 = l_Lean_Expr_app___override(x_88, x_558);
x_560 = lean_unbox(x_37);
x_561 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_560, x_38, x_559, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_559);
x_18 = x_561;
goto block_32;
}
default: 
{
lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; uint8_t x_570; lean_object* x_571; 
x_562 = lean_ctor_get(x_96, 1);
lean_inc(x_562);
lean_dec(x_96);
x_563 = lean_ctor_get(x_103, 0);
lean_inc(x_563);
x_564 = lean_ctor_get(x_103, 1);
lean_inc(x_564);
lean_dec(x_103);
x_565 = l_Lean_Name_num___override(x_563, x_564);
x_566 = l_Lean_Name_str___override(x_565, x_562);
x_567 = l_Lean_Name_str___override(x_566, x_97);
x_568 = l_Lean_Expr_const___override(x_567, x_90);
x_569 = l_Lean_Expr_app___override(x_88, x_568);
x_570 = lean_unbox(x_37);
x_571 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_570, x_38, x_569, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_569);
x_18 = x_571;
goto block_32;
}
}
}
default: 
{
lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; lean_object* x_579; 
lean_dec(x_98);
x_572 = lean_ctor_get(x_96, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_96, 1);
lean_inc(x_573);
lean_dec(x_96);
x_574 = l_Lean_Name_num___override(x_572, x_573);
x_575 = l_Lean_Name_str___override(x_574, x_97);
x_576 = l_Lean_Expr_const___override(x_575, x_90);
x_577 = l_Lean_Expr_app___override(x_88, x_576);
x_578 = lean_unbox(x_37);
x_579 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_578, x_38, x_577, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_577);
x_18 = x_579;
goto block_32;
}
}
}
default: 
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; uint8_t x_585; lean_object* x_586; 
x_580 = lean_ctor_get(x_89, 0);
lean_inc(x_580);
x_581 = lean_ctor_get(x_89, 1);
lean_inc(x_581);
lean_dec(x_89);
x_582 = l_Lean_Name_num___override(x_580, x_581);
x_583 = l_Lean_Expr_const___override(x_582, x_90);
x_584 = l_Lean_Expr_app___override(x_88, x_583);
x_585 = lean_unbox(x_37);
x_586 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_585, x_38, x_584, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_584);
x_18 = x_586;
goto block_32;
}
}
}
case 5:
{
lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; uint8_t x_592; lean_object* x_593; 
x_587 = lean_ctor_get(x_41, 0);
lean_inc(x_587);
lean_dec(x_41);
x_588 = lean_ctor_get(x_63, 0);
lean_inc(x_588);
x_589 = lean_ctor_get(x_63, 1);
lean_inc(x_589);
lean_dec(x_63);
x_590 = l_Lean_Expr_app___override(x_588, x_589);
x_591 = l_Lean_Expr_app___override(x_587, x_590);
x_592 = lean_unbox(x_37);
x_593 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_592, x_38, x_591, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_591);
x_18 = x_593;
goto block_32;
}
case 6:
{
lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; uint8_t x_598; lean_object* x_599; lean_object* x_600; uint8_t x_601; lean_object* x_602; 
x_594 = lean_ctor_get(x_41, 0);
lean_inc(x_594);
lean_dec(x_41);
x_595 = lean_ctor_get(x_63, 0);
lean_inc(x_595);
x_596 = lean_ctor_get(x_63, 1);
lean_inc(x_596);
x_597 = lean_ctor_get(x_63, 2);
lean_inc(x_597);
x_598 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_dec(x_63);
x_599 = l_Lean_Expr_lam___override(x_595, x_596, x_597, x_598);
x_600 = l_Lean_Expr_app___override(x_594, x_599);
x_601 = lean_unbox(x_37);
x_602 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_601, x_38, x_600, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_600);
x_18 = x_602;
goto block_32;
}
case 7:
{
lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; uint8_t x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; 
x_603 = lean_ctor_get(x_41, 0);
lean_inc(x_603);
lean_dec(x_41);
x_604 = lean_ctor_get(x_63, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_63, 1);
lean_inc(x_605);
x_606 = lean_ctor_get(x_63, 2);
lean_inc(x_606);
x_607 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_dec(x_63);
x_608 = l_Lean_Expr_forallE___override(x_604, x_605, x_606, x_607);
x_609 = l_Lean_Expr_app___override(x_603, x_608);
x_610 = lean_unbox(x_37);
x_611 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_610, x_38, x_609, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_609);
x_18 = x_611;
goto block_32;
}
case 8:
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; uint8_t x_617; lean_object* x_618; lean_object* x_619; uint8_t x_620; lean_object* x_621; 
x_612 = lean_ctor_get(x_41, 0);
lean_inc(x_612);
lean_dec(x_41);
x_613 = lean_ctor_get(x_63, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_63, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_63, 2);
lean_inc(x_615);
x_616 = lean_ctor_get(x_63, 3);
lean_inc(x_616);
x_617 = lean_ctor_get_uint8(x_63, sizeof(void*)*4 + 8);
lean_dec(x_63);
x_618 = l_Lean_Expr_letE___override(x_613, x_614, x_615, x_616, x_617);
x_619 = l_Lean_Expr_app___override(x_612, x_618);
x_620 = lean_unbox(x_37);
x_621 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_620, x_38, x_619, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_619);
x_18 = x_621;
goto block_32;
}
case 9:
{
lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; uint8_t x_626; lean_object* x_627; 
x_622 = lean_ctor_get(x_41, 0);
lean_inc(x_622);
lean_dec(x_41);
x_623 = lean_ctor_get(x_63, 0);
lean_inc(x_623);
lean_dec(x_63);
x_624 = l_Lean_Expr_lit___override(x_623);
x_625 = l_Lean_Expr_app___override(x_622, x_624);
x_626 = lean_unbox(x_37);
x_627 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_626, x_38, x_625, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_625);
x_18 = x_627;
goto block_32;
}
case 10:
{
lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; uint8_t x_633; lean_object* x_634; 
x_628 = lean_ctor_get(x_41, 0);
lean_inc(x_628);
lean_dec(x_41);
x_629 = lean_ctor_get(x_63, 0);
lean_inc(x_629);
x_630 = lean_ctor_get(x_63, 1);
lean_inc(x_630);
lean_dec(x_63);
x_631 = l_Lean_Expr_mdata___override(x_629, x_630);
x_632 = l_Lean_Expr_app___override(x_628, x_631);
x_633 = lean_unbox(x_37);
x_634 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_633, x_38, x_632, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_632);
x_18 = x_634;
goto block_32;
}
default: 
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; uint8_t x_641; lean_object* x_642; 
x_635 = lean_ctor_get(x_41, 0);
lean_inc(x_635);
lean_dec(x_41);
x_636 = lean_ctor_get(x_63, 0);
lean_inc(x_636);
x_637 = lean_ctor_get(x_63, 1);
lean_inc(x_637);
x_638 = lean_ctor_get(x_63, 2);
lean_inc(x_638);
lean_dec(x_63);
x_639 = l_Lean_Expr_proj___override(x_636, x_637, x_638);
x_640 = l_Lean_Expr_app___override(x_635, x_639);
x_641 = lean_unbox(x_37);
x_642 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_641, x_38, x_640, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_640);
x_18 = x_642;
goto block_32;
}
}
}
case 6:
{
lean_object* x_643; lean_object* x_644; lean_object* x_645; uint8_t x_646; lean_object* x_647; uint8_t x_648; lean_object* x_649; 
x_643 = lean_ctor_get(x_41, 0);
lean_inc(x_643);
x_644 = lean_ctor_get(x_41, 1);
lean_inc(x_644);
x_645 = lean_ctor_get(x_41, 2);
lean_inc(x_645);
x_646 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_647 = l_Lean_Expr_lam___override(x_643, x_644, x_645, x_646);
x_648 = lean_unbox(x_37);
x_649 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_648, x_38, x_647, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_647);
x_18 = x_649;
goto block_32;
}
case 7:
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; uint8_t x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; 
x_650 = lean_ctor_get(x_41, 0);
lean_inc(x_650);
x_651 = lean_ctor_get(x_41, 1);
lean_inc(x_651);
x_652 = lean_ctor_get(x_41, 2);
lean_inc(x_652);
x_653 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_654 = l_Lean_Expr_forallE___override(x_650, x_651, x_652, x_653);
x_655 = lean_unbox(x_37);
x_656 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_655, x_38, x_654, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_654);
x_18 = x_656;
goto block_32;
}
case 8:
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; uint8_t x_661; lean_object* x_662; uint8_t x_663; lean_object* x_664; 
x_657 = lean_ctor_get(x_41, 0);
lean_inc(x_657);
x_658 = lean_ctor_get(x_41, 1);
lean_inc(x_658);
x_659 = lean_ctor_get(x_41, 2);
lean_inc(x_659);
x_660 = lean_ctor_get(x_41, 3);
lean_inc(x_660);
x_661 = lean_ctor_get_uint8(x_41, sizeof(void*)*4 + 8);
lean_dec(x_41);
x_662 = l_Lean_Expr_letE___override(x_657, x_658, x_659, x_660, x_661);
x_663 = lean_unbox(x_37);
x_664 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_663, x_38, x_662, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_662);
x_18 = x_664;
goto block_32;
}
case 9:
{
lean_object* x_665; lean_object* x_666; uint8_t x_667; lean_object* x_668; 
x_665 = lean_ctor_get(x_41, 0);
lean_inc(x_665);
lean_dec(x_41);
x_666 = l_Lean_Expr_lit___override(x_665);
x_667 = lean_unbox(x_37);
x_668 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_667, x_38, x_666, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_666);
x_18 = x_668;
goto block_32;
}
case 10:
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; uint8_t x_672; lean_object* x_673; 
x_669 = lean_ctor_get(x_41, 0);
lean_inc(x_669);
x_670 = lean_ctor_get(x_41, 1);
lean_inc(x_670);
lean_dec(x_41);
x_671 = l_Lean_Expr_mdata___override(x_669, x_670);
x_672 = lean_unbox(x_37);
x_673 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_672, x_38, x_671, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_671);
x_18 = x_673;
goto block_32;
}
default: 
{
lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; uint8_t x_678; lean_object* x_679; 
x_674 = lean_ctor_get(x_41, 0);
lean_inc(x_674);
x_675 = lean_ctor_get(x_41, 1);
lean_inc(x_675);
x_676 = lean_ctor_get(x_41, 2);
lean_inc(x_676);
lean_dec(x_41);
x_677 = l_Lean_Expr_proj___override(x_674, x_675, x_676);
x_678 = lean_unbox(x_37);
x_679 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_678, x_38, x_677, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_677);
x_18 = x_679;
goto block_32;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_5 = x_12;
x_6 = x_15;
x_11 = x_13;
goto _start;
}
block_32:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_12 = x_27;
x_13 = x_26;
goto block_17;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_array_set(x_5, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
lean_dec(x_6);
x_4 = x_12;
x_5 = x_14;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp(x_1, x_4, x_5, x_2, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_box(0);
x_29 = lean_box(0);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_28);
x_30 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(x_5, x_3, x_2, x_27, x_18, x_24, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(x_5, x_3, x_2, x_51, x_54, x_48, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_19);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_19);
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_67 = x_55;
} else {
 lean_dec_ref(x_55);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
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
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_array_set(x_5, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
x_17 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1_spec__1(x_1, x_2, x_3, x_12, x_14, x_16, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp(x_1, x_4, x_5, x_2, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_box(0);
x_29 = lean_box(0);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_28);
x_30 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(x_5, x_3, x_2, x_27, x_18, x_24, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(x_5, x_3, x_2, x_51, x_54, x_48, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_19);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_19);
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_67 = x_55;
} else {
 lean_dec_ref(x_55);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
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
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1(x_1, x_3, x_2, x_4, x_13, x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum___lam__0___boxed), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_10, x_9, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_1);
lean_dec(x_1);
x_10 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_nat_dec_lt(x_5, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = l_Lean_instInhabitedExpr;
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_add(x_5, x_30);
x_32 = lean_array_get(x_29, x_1, x_31);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = lean_infer_type(x_32, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_dec(x_4);
if (lean_obj_tag(x_35) == 7)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 2);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l_Lean_Expr_hasLooseBVars(x_42);
if (x_43 == 0)
{
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_33);
lean_dec(x_5);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Expr_bvar___override(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_47, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_47);
x_17 = x_48;
goto block_25;
}
case 1:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_33);
lean_dec(x_5);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_50 = l_Lean_Expr_fvar___override(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_52, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_52);
x_17 = x_53;
goto block_25;
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_33);
lean_dec(x_5);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Lean_Expr_mvar___override(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_57, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_57);
x_17 = x_58;
goto block_25;
}
case 3:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_33);
lean_dec(x_5);
x_59 = lean_ctor_get(x_41, 0);
lean_inc(x_59);
lean_dec(x_41);
x_60 = l_Lean_Expr_sort___override(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_42);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_62, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_62);
x_17 = x_63;
goto block_25;
}
case 4:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_41, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_dec(x_41);
x_66 = lean_box(0);
lean_inc(x_65);
x_67 = l_Lean_Expr_const___override(x_66, x_65);
switch (lean_obj_tag(x_64)) {
case 0:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
lean_free_object(x_33);
lean_dec(x_5);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_42);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_69, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_69);
x_17 = x_70;
goto block_25;
}
case 1:
{
lean_object* x_71; 
lean_dec(x_67);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
switch (lean_obj_tag(x_71)) {
case 0:
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_mk_string_unchecked("Unit", 4, 4);
x_74 = lean_string_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
lean_free_object(x_33);
lean_dec(x_5);
x_75 = l_Lean_Name_str___override(x_66, x_72);
x_76 = l_Lean_Expr_const___override(x_75, x_65);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_42);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_78, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_78);
x_17 = x_79;
goto block_25;
}
else
{
lean_dec(x_72);
if (lean_obj_tag(x_65) == 0)
{
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_33);
lean_dec(x_5);
x_80 = lean_ctor_get(x_42, 0);
lean_inc(x_80);
lean_dec(x_42);
x_81 = l_Lean_Name_str___override(x_66, x_73);
x_82 = l_Lean_Expr_const___override(x_81, x_65);
x_83 = l_Lean_Expr_bvar___override(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_85, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_85);
x_17 = x_86;
goto block_25;
}
case 1:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_33);
lean_dec(x_5);
x_87 = lean_ctor_get(x_42, 0);
lean_inc(x_87);
lean_dec(x_42);
x_88 = l_Lean_Name_str___override(x_66, x_73);
x_89 = l_Lean_Expr_const___override(x_88, x_65);
x_90 = l_Lean_Expr_fvar___override(x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_92, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_92);
x_17 = x_93;
goto block_25;
}
case 2:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_33);
lean_dec(x_5);
x_94 = lean_ctor_get(x_42, 0);
lean_inc(x_94);
lean_dec(x_42);
x_95 = l_Lean_Name_str___override(x_66, x_73);
x_96 = l_Lean_Expr_const___override(x_95, x_65);
x_97 = l_Lean_Expr_mvar___override(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_99, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_99);
x_17 = x_100;
goto block_25;
}
case 3:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_free_object(x_33);
lean_dec(x_5);
x_101 = lean_ctor_get(x_42, 0);
lean_inc(x_101);
lean_dec(x_42);
x_102 = l_Lean_Name_str___override(x_66, x_73);
x_103 = l_Lean_Expr_const___override(x_102, x_65);
x_104 = l_Lean_Expr_sort___override(x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_106, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_106);
x_17 = x_107;
goto block_25;
}
case 4:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_free_object(x_33);
lean_dec(x_5);
x_108 = lean_ctor_get(x_42, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_42, 1);
lean_inc(x_109);
lean_dec(x_42);
x_110 = l_Lean_Name_str___override(x_66, x_73);
x_111 = l_Lean_Expr_const___override(x_110, x_65);
x_112 = l_Lean_Expr_const___override(x_108, x_109);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_114, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_114);
x_17 = x_115;
goto block_25;
}
case 5:
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_42, 1);
lean_inc(x_116);
switch (lean_obj_tag(x_116)) {
case 0:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_free_object(x_33);
lean_dec(x_5);
x_117 = lean_ctor_get(x_42, 0);
lean_inc(x_117);
lean_dec(x_42);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Name_str___override(x_66, x_73);
x_120 = l_Lean_Expr_const___override(x_119, x_65);
x_121 = l_Lean_Expr_bvar___override(x_118);
x_122 = l_Lean_Expr_app___override(x_117, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_124, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_124);
x_17 = x_125;
goto block_25;
}
case 1:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_33);
lean_dec(x_5);
x_126 = lean_ctor_get(x_42, 0);
lean_inc(x_126);
lean_dec(x_42);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
lean_dec(x_116);
x_128 = l_Lean_Name_str___override(x_66, x_73);
x_129 = l_Lean_Expr_const___override(x_128, x_65);
x_130 = l_Lean_Expr_fvar___override(x_127);
x_131 = l_Lean_Expr_app___override(x_126, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_133, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_133);
x_17 = x_134;
goto block_25;
}
case 2:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_free_object(x_33);
lean_dec(x_5);
x_135 = lean_ctor_get(x_42, 0);
lean_inc(x_135);
lean_dec(x_42);
x_136 = lean_ctor_get(x_116, 0);
lean_inc(x_136);
lean_dec(x_116);
x_137 = l_Lean_Name_str___override(x_66, x_73);
x_138 = l_Lean_Expr_const___override(x_137, x_65);
x_139 = l_Lean_Expr_mvar___override(x_136);
x_140 = l_Lean_Expr_app___override(x_135, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_142, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_142);
x_17 = x_143;
goto block_25;
}
case 3:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_free_object(x_33);
lean_dec(x_5);
x_144 = lean_ctor_get(x_42, 0);
lean_inc(x_144);
lean_dec(x_42);
x_145 = lean_ctor_get(x_116, 0);
lean_inc(x_145);
lean_dec(x_116);
x_146 = l_Lean_Name_str___override(x_66, x_73);
x_147 = l_Lean_Expr_const___override(x_146, x_65);
x_148 = l_Lean_Expr_sort___override(x_145);
x_149 = l_Lean_Expr_app___override(x_144, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_151, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_151);
x_17 = x_152;
goto block_25;
}
case 4:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_116, 1);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_73);
x_154 = lean_ctor_get(x_42, 0);
lean_inc(x_154);
lean_dec(x_42);
x_155 = lean_ctor_get(x_116, 0);
lean_inc(x_155);
lean_dec(x_116);
x_156 = lean_expr_eqv(x_154, x_2);
lean_dec(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_155);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_37);
lean_ctor_set(x_33, 0, x_159);
return x_33;
}
else
{
lean_object* x_160; 
lean_free_object(x_33);
x_160 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_155, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 6)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_box(0);
x_165 = lean_array_push(x_37, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_11 = x_166;
x_12 = x_162;
goto block_16;
}
else
{
uint8_t x_167; 
lean_dec(x_161);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_160);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_160, 0);
lean_dec(x_168);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_37);
lean_ctor_set(x_160, 0, x_171);
return x_160;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_160, 1);
lean_inc(x_172);
lean_dec(x_160);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_37);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_177 = !lean_is_exclusive(x_160);
if (x_177 == 0)
{
return x_160;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_160, 0);
x_179 = lean_ctor_get(x_160, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_160);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_free_object(x_33);
lean_dec(x_5);
x_181 = lean_ctor_get(x_42, 0);
lean_inc(x_181);
lean_dec(x_42);
x_182 = lean_ctor_get(x_116, 0);
lean_inc(x_182);
lean_dec(x_116);
x_183 = l_Lean_Name_str___override(x_66, x_73);
x_184 = l_Lean_Expr_const___override(x_183, x_65);
lean_inc(x_153);
x_185 = l_Lean_Expr_const___override(x_182, x_153);
x_186 = !lean_is_exclusive(x_153);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_153, 1);
lean_dec(x_187);
x_188 = lean_ctor_get(x_153, 0);
lean_dec(x_188);
x_189 = l_Lean_Expr_app___override(x_181, x_185);
lean_ctor_set_tag(x_153, 0);
lean_ctor_set(x_153, 1, x_189);
lean_ctor_set(x_153, 0, x_184);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_153);
x_191 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_190, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_190);
x_17 = x_191;
goto block_25;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_153);
x_192 = l_Lean_Expr_app___override(x_181, x_185);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_184);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_194, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_194);
x_17 = x_195;
goto block_25;
}
}
}
case 5:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_free_object(x_33);
lean_dec(x_5);
x_196 = lean_ctor_get(x_42, 0);
lean_inc(x_196);
lean_dec(x_42);
x_197 = lean_ctor_get(x_116, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_116, 1);
lean_inc(x_198);
lean_dec(x_116);
x_199 = l_Lean_Name_str___override(x_66, x_73);
x_200 = l_Lean_Expr_const___override(x_199, x_65);
x_201 = l_Lean_Expr_app___override(x_197, x_198);
x_202 = l_Lean_Expr_app___override(x_196, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_204, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_204);
x_17 = x_205;
goto block_25;
}
case 6:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_free_object(x_33);
lean_dec(x_5);
x_206 = lean_ctor_get(x_42, 0);
lean_inc(x_206);
lean_dec(x_42);
x_207 = lean_ctor_get(x_116, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_116, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_116, 2);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_116, sizeof(void*)*3 + 8);
lean_dec(x_116);
x_211 = l_Lean_Name_str___override(x_66, x_73);
x_212 = l_Lean_Expr_const___override(x_211, x_65);
x_213 = l_Lean_Expr_lam___override(x_207, x_208, x_209, x_210);
x_214 = l_Lean_Expr_app___override(x_206, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_216, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_216);
x_17 = x_217;
goto block_25;
}
case 7:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_free_object(x_33);
lean_dec(x_5);
x_218 = lean_ctor_get(x_42, 0);
lean_inc(x_218);
lean_dec(x_42);
x_219 = lean_ctor_get(x_116, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_116, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_116, 2);
lean_inc(x_221);
x_222 = lean_ctor_get_uint8(x_116, sizeof(void*)*3 + 8);
lean_dec(x_116);
x_223 = l_Lean_Name_str___override(x_66, x_73);
x_224 = l_Lean_Expr_const___override(x_223, x_65);
x_225 = l_Lean_Expr_forallE___override(x_219, x_220, x_221, x_222);
x_226 = l_Lean_Expr_app___override(x_218, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_228, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_228);
x_17 = x_229;
goto block_25;
}
case 8:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_free_object(x_33);
lean_dec(x_5);
x_230 = lean_ctor_get(x_42, 0);
lean_inc(x_230);
lean_dec(x_42);
x_231 = lean_ctor_get(x_116, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_116, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_116, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_116, 3);
lean_inc(x_234);
x_235 = lean_ctor_get_uint8(x_116, sizeof(void*)*4 + 8);
lean_dec(x_116);
x_236 = l_Lean_Name_str___override(x_66, x_73);
x_237 = l_Lean_Expr_const___override(x_236, x_65);
x_238 = l_Lean_Expr_letE___override(x_231, x_232, x_233, x_234, x_235);
x_239 = l_Lean_Expr_app___override(x_230, x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_241, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_241);
x_17 = x_242;
goto block_25;
}
case 9:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_free_object(x_33);
lean_dec(x_5);
x_243 = lean_ctor_get(x_42, 0);
lean_inc(x_243);
lean_dec(x_42);
x_244 = lean_ctor_get(x_116, 0);
lean_inc(x_244);
lean_dec(x_116);
x_245 = l_Lean_Name_str___override(x_66, x_73);
x_246 = l_Lean_Expr_const___override(x_245, x_65);
x_247 = l_Lean_Expr_lit___override(x_244);
x_248 = l_Lean_Expr_app___override(x_243, x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_251 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_250, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_250);
x_17 = x_251;
goto block_25;
}
case 10:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_free_object(x_33);
lean_dec(x_5);
x_252 = lean_ctor_get(x_42, 0);
lean_inc(x_252);
lean_dec(x_42);
x_253 = lean_ctor_get(x_116, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_116, 1);
lean_inc(x_254);
lean_dec(x_116);
x_255 = l_Lean_Name_str___override(x_66, x_73);
x_256 = l_Lean_Expr_const___override(x_255, x_65);
x_257 = l_Lean_Expr_mdata___override(x_253, x_254);
x_258 = l_Lean_Expr_app___override(x_252, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_260, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_260);
x_17 = x_261;
goto block_25;
}
default: 
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_free_object(x_33);
lean_dec(x_5);
x_262 = lean_ctor_get(x_42, 0);
lean_inc(x_262);
lean_dec(x_42);
x_263 = lean_ctor_get(x_116, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_116, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_116, 2);
lean_inc(x_265);
lean_dec(x_116);
x_266 = l_Lean_Name_str___override(x_66, x_73);
x_267 = l_Lean_Expr_const___override(x_266, x_65);
x_268 = l_Lean_Expr_proj___override(x_263, x_264, x_265);
x_269 = l_Lean_Expr_app___override(x_262, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_271, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_271);
x_17 = x_272;
goto block_25;
}
}
}
case 6:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_free_object(x_33);
lean_dec(x_5);
x_273 = lean_ctor_get(x_42, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_42, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_42, 2);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_277 = l_Lean_Name_str___override(x_66, x_73);
x_278 = l_Lean_Expr_const___override(x_277, x_65);
x_279 = l_Lean_Expr_lam___override(x_273, x_274, x_275, x_276);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
x_282 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_281, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_281);
x_17 = x_282;
goto block_25;
}
case 7:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_free_object(x_33);
lean_dec(x_5);
x_283 = lean_ctor_get(x_42, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_42, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_42, 2);
lean_inc(x_285);
x_286 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_287 = l_Lean_Name_str___override(x_66, x_73);
x_288 = l_Lean_Expr_const___override(x_287, x_65);
x_289 = l_Lean_Expr_forallE___override(x_283, x_284, x_285, x_286);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_291, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_291);
x_17 = x_292;
goto block_25;
}
case 8:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_free_object(x_33);
lean_dec(x_5);
x_293 = lean_ctor_get(x_42, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_42, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_42, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_42, 3);
lean_inc(x_296);
x_297 = lean_ctor_get_uint8(x_42, sizeof(void*)*4 + 8);
lean_dec(x_42);
x_298 = l_Lean_Name_str___override(x_66, x_73);
x_299 = l_Lean_Expr_const___override(x_298, x_65);
x_300 = l_Lean_Expr_letE___override(x_293, x_294, x_295, x_296, x_297);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_303 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_302, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_302);
x_17 = x_303;
goto block_25;
}
case 9:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_free_object(x_33);
lean_dec(x_5);
x_304 = lean_ctor_get(x_42, 0);
lean_inc(x_304);
lean_dec(x_42);
x_305 = l_Lean_Name_str___override(x_66, x_73);
x_306 = l_Lean_Expr_const___override(x_305, x_65);
x_307 = l_Lean_Expr_lit___override(x_304);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_310 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_309, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_309);
x_17 = x_310;
goto block_25;
}
case 10:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_free_object(x_33);
lean_dec(x_5);
x_311 = lean_ctor_get(x_42, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_42, 1);
lean_inc(x_312);
lean_dec(x_42);
x_313 = l_Lean_Name_str___override(x_66, x_73);
x_314 = l_Lean_Expr_const___override(x_313, x_65);
x_315 = l_Lean_Expr_mdata___override(x_311, x_312);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_317, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_317);
x_17 = x_318;
goto block_25;
}
default: 
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_free_object(x_33);
lean_dec(x_5);
x_319 = lean_ctor_get(x_42, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_42, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_42, 2);
lean_inc(x_321);
lean_dec(x_42);
x_322 = l_Lean_Name_str___override(x_66, x_73);
x_323 = l_Lean_Expr_const___override(x_322, x_65);
x_324 = l_Lean_Expr_proj___override(x_319, x_320, x_321);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_326, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_326);
x_17 = x_327;
goto block_25;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_free_object(x_33);
lean_dec(x_5);
x_328 = l_Lean_Name_str___override(x_66, x_73);
lean_inc(x_65);
x_329 = l_Lean_Expr_const___override(x_328, x_65);
x_330 = !lean_is_exclusive(x_65);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = lean_ctor_get(x_65, 1);
lean_dec(x_331);
x_332 = lean_ctor_get(x_65, 0);
lean_dec(x_332);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 1, x_42);
lean_ctor_set(x_65, 0, x_329);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_65);
x_334 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_333, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_333);
x_17 = x_334;
goto block_25;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_65);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_329);
lean_ctor_set(x_335, 1, x_42);
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_335);
x_337 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_336, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_336);
x_17 = x_337;
goto block_25;
}
}
}
}
case 1:
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_free_object(x_33);
lean_dec(x_5);
x_338 = lean_ctor_get(x_64, 1);
lean_inc(x_338);
lean_dec(x_64);
x_339 = lean_ctor_get(x_71, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_71, 1);
lean_inc(x_340);
lean_dec(x_71);
x_341 = l_Lean_Name_str___override(x_339, x_340);
x_342 = l_Lean_Name_str___override(x_341, x_338);
x_343 = l_Lean_Expr_const___override(x_342, x_65);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_42);
x_345 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_345, 0, x_344);
x_346 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_345, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_345);
x_17 = x_346;
goto block_25;
}
default: 
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_free_object(x_33);
lean_dec(x_5);
x_347 = lean_ctor_get(x_64, 1);
lean_inc(x_347);
lean_dec(x_64);
x_348 = lean_ctor_get(x_71, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_71, 1);
lean_inc(x_349);
lean_dec(x_71);
x_350 = l_Lean_Name_num___override(x_348, x_349);
x_351 = l_Lean_Name_str___override(x_350, x_347);
x_352 = l_Lean_Expr_const___override(x_351, x_65);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_42);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_355 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_354, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_354);
x_17 = x_355;
goto block_25;
}
}
}
default: 
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_67);
lean_free_object(x_33);
lean_dec(x_5);
x_356 = lean_ctor_get(x_64, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_64, 1);
lean_inc(x_357);
lean_dec(x_64);
x_358 = l_Lean_Name_num___override(x_356, x_357);
x_359 = l_Lean_Expr_const___override(x_358, x_65);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_42);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
x_362 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_361, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_361);
x_17 = x_362;
goto block_25;
}
}
}
case 5:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_free_object(x_33);
lean_dec(x_5);
x_363 = lean_ctor_get(x_41, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_41, 1);
lean_inc(x_364);
lean_dec(x_41);
x_365 = l_Lean_Expr_app___override(x_363, x_364);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_42);
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_366);
x_368 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_367, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_367);
x_17 = x_368;
goto block_25;
}
case 6:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_free_object(x_33);
lean_dec(x_5);
x_369 = lean_ctor_get(x_41, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_41, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_41, 2);
lean_inc(x_371);
x_372 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_373 = l_Lean_Expr_lam___override(x_369, x_370, x_371, x_372);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_42);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_375, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_375);
x_17 = x_376;
goto block_25;
}
case 7:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_free_object(x_33);
lean_dec(x_5);
x_377 = lean_ctor_get(x_41, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_41, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_41, 2);
lean_inc(x_379);
x_380 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_381 = l_Lean_Expr_forallE___override(x_377, x_378, x_379, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_42);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
x_384 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_383, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_383);
x_17 = x_384;
goto block_25;
}
case 8:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_free_object(x_33);
lean_dec(x_5);
x_385 = lean_ctor_get(x_41, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_41, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_41, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_41, 3);
lean_inc(x_388);
x_389 = lean_ctor_get_uint8(x_41, sizeof(void*)*4 + 8);
lean_dec(x_41);
x_390 = l_Lean_Expr_letE___override(x_385, x_386, x_387, x_388, x_389);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_42);
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_391);
x_393 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_392, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_392);
x_17 = x_393;
goto block_25;
}
case 9:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_free_object(x_33);
lean_dec(x_5);
x_394 = lean_ctor_get(x_41, 0);
lean_inc(x_394);
lean_dec(x_41);
x_395 = l_Lean_Expr_lit___override(x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_42);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
x_398 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_397, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_397);
x_17 = x_398;
goto block_25;
}
case 10:
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_free_object(x_33);
lean_dec(x_5);
x_399 = lean_ctor_get(x_41, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_41, 1);
lean_inc(x_400);
lean_dec(x_41);
x_401 = l_Lean_Expr_mdata___override(x_399, x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_42);
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_402);
x_404 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_403, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_403);
x_17 = x_404;
goto block_25;
}
default: 
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_free_object(x_33);
lean_dec(x_5);
x_405 = lean_ctor_get(x_41, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_41, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_41, 2);
lean_inc(x_407);
lean_dec(x_41);
x_408 = l_Lean_Expr_proj___override(x_405, x_406, x_407);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_42);
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_411 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_410, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_410);
x_17 = x_411;
goto block_25;
}
}
}
else
{
lean_object* x_412; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_33);
lean_dec(x_5);
x_412 = lean_box(0);
x_38 = x_412;
goto block_40;
}
}
else
{
lean_object* x_413; 
lean_free_object(x_33);
lean_dec(x_35);
lean_dec(x_5);
x_413 = lean_box(0);
x_38 = x_413;
goto block_40;
}
block_40:
{
lean_object* x_39; 
x_39 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_38, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
x_17 = x_39;
goto block_25;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = lean_ctor_get(x_33, 0);
x_415 = lean_ctor_get(x_33, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_33);
x_416 = lean_ctor_get(x_4, 1);
lean_inc(x_416);
lean_dec(x_4);
if (lean_obj_tag(x_414) == 7)
{
lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_414, 2);
lean_inc(x_421);
lean_dec(x_414);
x_422 = l_Lean_Expr_hasLooseBVars(x_421);
if (x_422 == 0)
{
switch (lean_obj_tag(x_420)) {
case 0:
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_5);
x_423 = lean_ctor_get(x_420, 0);
lean_inc(x_423);
lean_dec(x_420);
x_424 = l_Lean_Expr_bvar___override(x_423);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_421);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_425);
x_427 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_426, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_426);
x_17 = x_427;
goto block_25;
}
case 1:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_5);
x_428 = lean_ctor_get(x_420, 0);
lean_inc(x_428);
lean_dec(x_420);
x_429 = l_Lean_Expr_fvar___override(x_428);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_421);
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_430);
x_432 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_431, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_431);
x_17 = x_432;
goto block_25;
}
case 2:
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_5);
x_433 = lean_ctor_get(x_420, 0);
lean_inc(x_433);
lean_dec(x_420);
x_434 = l_Lean_Expr_mvar___override(x_433);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_421);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
x_437 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_436, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_436);
x_17 = x_437;
goto block_25;
}
case 3:
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_5);
x_438 = lean_ctor_get(x_420, 0);
lean_inc(x_438);
lean_dec(x_420);
x_439 = l_Lean_Expr_sort___override(x_438);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_421);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_440);
x_442 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_441, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_441);
x_17 = x_442;
goto block_25;
}
case 4:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_420, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_420, 1);
lean_inc(x_444);
lean_dec(x_420);
x_445 = lean_box(0);
lean_inc(x_444);
x_446 = l_Lean_Expr_const___override(x_445, x_444);
switch (lean_obj_tag(x_443)) {
case 0:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_444);
lean_dec(x_5);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_421);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
x_449 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_448, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_448);
x_17 = x_449;
goto block_25;
}
case 1:
{
lean_object* x_450; 
lean_dec(x_446);
x_450 = lean_ctor_get(x_443, 0);
lean_inc(x_450);
switch (lean_obj_tag(x_450)) {
case 0:
{
lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_451 = lean_ctor_get(x_443, 1);
lean_inc(x_451);
lean_dec(x_443);
x_452 = lean_mk_string_unchecked("Unit", 4, 4);
x_453 = lean_string_dec_eq(x_451, x_452);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_452);
lean_dec(x_5);
x_454 = l_Lean_Name_str___override(x_445, x_451);
x_455 = l_Lean_Expr_const___override(x_454, x_444);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_421);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_456);
x_458 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_457, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_457);
x_17 = x_458;
goto block_25;
}
else
{
lean_dec(x_451);
if (lean_obj_tag(x_444) == 0)
{
switch (lean_obj_tag(x_421)) {
case 0:
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_5);
x_459 = lean_ctor_get(x_421, 0);
lean_inc(x_459);
lean_dec(x_421);
x_460 = l_Lean_Name_str___override(x_445, x_452);
x_461 = l_Lean_Expr_const___override(x_460, x_444);
x_462 = l_Lean_Expr_bvar___override(x_459);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_463);
x_465 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_464, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_464);
x_17 = x_465;
goto block_25;
}
case 1:
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_5);
x_466 = lean_ctor_get(x_421, 0);
lean_inc(x_466);
lean_dec(x_421);
x_467 = l_Lean_Name_str___override(x_445, x_452);
x_468 = l_Lean_Expr_const___override(x_467, x_444);
x_469 = l_Lean_Expr_fvar___override(x_466);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_471, 0, x_470);
x_472 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_471, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_471);
x_17 = x_472;
goto block_25;
}
case 2:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_5);
x_473 = lean_ctor_get(x_421, 0);
lean_inc(x_473);
lean_dec(x_421);
x_474 = l_Lean_Name_str___override(x_445, x_452);
x_475 = l_Lean_Expr_const___override(x_474, x_444);
x_476 = l_Lean_Expr_mvar___override(x_473);
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
x_479 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_478, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_478);
x_17 = x_479;
goto block_25;
}
case 3:
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_5);
x_480 = lean_ctor_get(x_421, 0);
lean_inc(x_480);
lean_dec(x_421);
x_481 = l_Lean_Name_str___override(x_445, x_452);
x_482 = l_Lean_Expr_const___override(x_481, x_444);
x_483 = l_Lean_Expr_sort___override(x_480);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_484);
x_486 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_485, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_485);
x_17 = x_486;
goto block_25;
}
case 4:
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_5);
x_487 = lean_ctor_get(x_421, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_421, 1);
lean_inc(x_488);
lean_dec(x_421);
x_489 = l_Lean_Name_str___override(x_445, x_452);
x_490 = l_Lean_Expr_const___override(x_489, x_444);
x_491 = l_Lean_Expr_const___override(x_487, x_488);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_493, 0, x_492);
x_494 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_493, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_493);
x_17 = x_494;
goto block_25;
}
case 5:
{
lean_object* x_495; 
x_495 = lean_ctor_get(x_421, 1);
lean_inc(x_495);
switch (lean_obj_tag(x_495)) {
case 0:
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_5);
x_496 = lean_ctor_get(x_421, 0);
lean_inc(x_496);
lean_dec(x_421);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
lean_dec(x_495);
x_498 = l_Lean_Name_str___override(x_445, x_452);
x_499 = l_Lean_Expr_const___override(x_498, x_444);
x_500 = l_Lean_Expr_bvar___override(x_497);
x_501 = l_Lean_Expr_app___override(x_496, x_500);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_501);
x_503 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_503, 0, x_502);
x_504 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_503, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_503);
x_17 = x_504;
goto block_25;
}
case 1:
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_5);
x_505 = lean_ctor_get(x_421, 0);
lean_inc(x_505);
lean_dec(x_421);
x_506 = lean_ctor_get(x_495, 0);
lean_inc(x_506);
lean_dec(x_495);
x_507 = l_Lean_Name_str___override(x_445, x_452);
x_508 = l_Lean_Expr_const___override(x_507, x_444);
x_509 = l_Lean_Expr_fvar___override(x_506);
x_510 = l_Lean_Expr_app___override(x_505, x_509);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_512, 0, x_511);
x_513 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_512, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_512);
x_17 = x_513;
goto block_25;
}
case 2:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_5);
x_514 = lean_ctor_get(x_421, 0);
lean_inc(x_514);
lean_dec(x_421);
x_515 = lean_ctor_get(x_495, 0);
lean_inc(x_515);
lean_dec(x_495);
x_516 = l_Lean_Name_str___override(x_445, x_452);
x_517 = l_Lean_Expr_const___override(x_516, x_444);
x_518 = l_Lean_Expr_mvar___override(x_515);
x_519 = l_Lean_Expr_app___override(x_514, x_518);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
x_522 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_521, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_521);
x_17 = x_522;
goto block_25;
}
case 3:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_5);
x_523 = lean_ctor_get(x_421, 0);
lean_inc(x_523);
lean_dec(x_421);
x_524 = lean_ctor_get(x_495, 0);
lean_inc(x_524);
lean_dec(x_495);
x_525 = l_Lean_Name_str___override(x_445, x_452);
x_526 = l_Lean_Expr_const___override(x_525, x_444);
x_527 = l_Lean_Expr_sort___override(x_524);
x_528 = l_Lean_Expr_app___override(x_523, x_527);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_526);
lean_ctor_set(x_529, 1, x_528);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_529);
x_531 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_530, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_530);
x_17 = x_531;
goto block_25;
}
case 4:
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_495, 1);
lean_inc(x_532);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; uint8_t x_535; 
lean_dec(x_452);
x_533 = lean_ctor_get(x_421, 0);
lean_inc(x_533);
lean_dec(x_421);
x_534 = lean_ctor_get(x_495, 0);
lean_inc(x_534);
lean_dec(x_495);
x_535 = lean_expr_eqv(x_533, x_2);
lean_dec(x_533);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_534);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_536 = lean_box(0);
x_537 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_537, 0, x_536);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_416);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_415);
return x_539;
}
else
{
lean_object* x_540; 
x_540 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_534, x_6, x_7, x_8, x_9, x_415);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
if (lean_obj_tag(x_541) == 6)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
lean_dec(x_541);
x_544 = lean_box(0);
x_545 = lean_array_push(x_416, x_543);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
x_11 = x_546;
x_12 = x_542;
goto block_16;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_541);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_547 = lean_ctor_get(x_540, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_548 = x_540;
} else {
 lean_dec_ref(x_540);
 x_548 = lean_box(0);
}
x_549 = lean_box(0);
x_550 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_550, 0, x_549);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_416);
if (lean_is_scalar(x_548)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_548;
}
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_547);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_416);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_553 = lean_ctor_get(x_540, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_540, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_555 = x_540;
} else {
 lean_dec_ref(x_540);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_553);
lean_ctor_set(x_556, 1, x_554);
return x_556;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_5);
x_557 = lean_ctor_get(x_421, 0);
lean_inc(x_557);
lean_dec(x_421);
x_558 = lean_ctor_get(x_495, 0);
lean_inc(x_558);
lean_dec(x_495);
x_559 = l_Lean_Name_str___override(x_445, x_452);
x_560 = l_Lean_Expr_const___override(x_559, x_444);
lean_inc(x_532);
x_561 = l_Lean_Expr_const___override(x_558, x_532);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_562 = x_532;
} else {
 lean_dec_ref(x_532);
 x_562 = lean_box(0);
}
x_563 = l_Lean_Expr_app___override(x_557, x_561);
if (lean_is_scalar(x_562)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_562;
 lean_ctor_set_tag(x_564, 0);
}
lean_ctor_set(x_564, 0, x_560);
lean_ctor_set(x_564, 1, x_563);
x_565 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_565, 0, x_564);
x_566 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_565, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_565);
x_17 = x_566;
goto block_25;
}
}
case 5:
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_5);
x_567 = lean_ctor_get(x_421, 0);
lean_inc(x_567);
lean_dec(x_421);
x_568 = lean_ctor_get(x_495, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_495, 1);
lean_inc(x_569);
lean_dec(x_495);
x_570 = l_Lean_Name_str___override(x_445, x_452);
x_571 = l_Lean_Expr_const___override(x_570, x_444);
x_572 = l_Lean_Expr_app___override(x_568, x_569);
x_573 = l_Lean_Expr_app___override(x_567, x_572);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_575, 0, x_574);
x_576 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_575, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_575);
x_17 = x_576;
goto block_25;
}
case 6:
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_5);
x_577 = lean_ctor_get(x_421, 0);
lean_inc(x_577);
lean_dec(x_421);
x_578 = lean_ctor_get(x_495, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_495, 1);
lean_inc(x_579);
x_580 = lean_ctor_get(x_495, 2);
lean_inc(x_580);
x_581 = lean_ctor_get_uint8(x_495, sizeof(void*)*3 + 8);
lean_dec(x_495);
x_582 = l_Lean_Name_str___override(x_445, x_452);
x_583 = l_Lean_Expr_const___override(x_582, x_444);
x_584 = l_Lean_Expr_lam___override(x_578, x_579, x_580, x_581);
x_585 = l_Lean_Expr_app___override(x_577, x_584);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_585);
x_587 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_587, 0, x_586);
x_588 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_587, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_587);
x_17 = x_588;
goto block_25;
}
case 7:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_5);
x_589 = lean_ctor_get(x_421, 0);
lean_inc(x_589);
lean_dec(x_421);
x_590 = lean_ctor_get(x_495, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_495, 1);
lean_inc(x_591);
x_592 = lean_ctor_get(x_495, 2);
lean_inc(x_592);
x_593 = lean_ctor_get_uint8(x_495, sizeof(void*)*3 + 8);
lean_dec(x_495);
x_594 = l_Lean_Name_str___override(x_445, x_452);
x_595 = l_Lean_Expr_const___override(x_594, x_444);
x_596 = l_Lean_Expr_forallE___override(x_590, x_591, x_592, x_593);
x_597 = l_Lean_Expr_app___override(x_589, x_596);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_595);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_599, 0, x_598);
x_600 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_599, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_599);
x_17 = x_600;
goto block_25;
}
case 8:
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_5);
x_601 = lean_ctor_get(x_421, 0);
lean_inc(x_601);
lean_dec(x_421);
x_602 = lean_ctor_get(x_495, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_495, 1);
lean_inc(x_603);
x_604 = lean_ctor_get(x_495, 2);
lean_inc(x_604);
x_605 = lean_ctor_get(x_495, 3);
lean_inc(x_605);
x_606 = lean_ctor_get_uint8(x_495, sizeof(void*)*4 + 8);
lean_dec(x_495);
x_607 = l_Lean_Name_str___override(x_445, x_452);
x_608 = l_Lean_Expr_const___override(x_607, x_444);
x_609 = l_Lean_Expr_letE___override(x_602, x_603, x_604, x_605, x_606);
x_610 = l_Lean_Expr_app___override(x_601, x_609);
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_610);
x_612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_612, 0, x_611);
x_613 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_612, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_612);
x_17 = x_613;
goto block_25;
}
case 9:
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_5);
x_614 = lean_ctor_get(x_421, 0);
lean_inc(x_614);
lean_dec(x_421);
x_615 = lean_ctor_get(x_495, 0);
lean_inc(x_615);
lean_dec(x_495);
x_616 = l_Lean_Name_str___override(x_445, x_452);
x_617 = l_Lean_Expr_const___override(x_616, x_444);
x_618 = l_Lean_Expr_lit___override(x_615);
x_619 = l_Lean_Expr_app___override(x_614, x_618);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_619);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_620);
x_622 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_621, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_621);
x_17 = x_622;
goto block_25;
}
case 10:
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_5);
x_623 = lean_ctor_get(x_421, 0);
lean_inc(x_623);
lean_dec(x_421);
x_624 = lean_ctor_get(x_495, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_495, 1);
lean_inc(x_625);
lean_dec(x_495);
x_626 = l_Lean_Name_str___override(x_445, x_452);
x_627 = l_Lean_Expr_const___override(x_626, x_444);
x_628 = l_Lean_Expr_mdata___override(x_624, x_625);
x_629 = l_Lean_Expr_app___override(x_623, x_628);
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_629);
x_631 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_631, 0, x_630);
x_632 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_631, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_631);
x_17 = x_632;
goto block_25;
}
default: 
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_5);
x_633 = lean_ctor_get(x_421, 0);
lean_inc(x_633);
lean_dec(x_421);
x_634 = lean_ctor_get(x_495, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_495, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_495, 2);
lean_inc(x_636);
lean_dec(x_495);
x_637 = l_Lean_Name_str___override(x_445, x_452);
x_638 = l_Lean_Expr_const___override(x_637, x_444);
x_639 = l_Lean_Expr_proj___override(x_634, x_635, x_636);
x_640 = l_Lean_Expr_app___override(x_633, x_639);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_638);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_642, 0, x_641);
x_643 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_642, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_642);
x_17 = x_643;
goto block_25;
}
}
}
case 6:
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_5);
x_644 = lean_ctor_get(x_421, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_421, 1);
lean_inc(x_645);
x_646 = lean_ctor_get(x_421, 2);
lean_inc(x_646);
x_647 = lean_ctor_get_uint8(x_421, sizeof(void*)*3 + 8);
lean_dec(x_421);
x_648 = l_Lean_Name_str___override(x_445, x_452);
x_649 = l_Lean_Expr_const___override(x_648, x_444);
x_650 = l_Lean_Expr_lam___override(x_644, x_645, x_646, x_647);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_652, 0, x_651);
x_653 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_652, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_652);
x_17 = x_653;
goto block_25;
}
case 7:
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_5);
x_654 = lean_ctor_get(x_421, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_421, 1);
lean_inc(x_655);
x_656 = lean_ctor_get(x_421, 2);
lean_inc(x_656);
x_657 = lean_ctor_get_uint8(x_421, sizeof(void*)*3 + 8);
lean_dec(x_421);
x_658 = l_Lean_Name_str___override(x_445, x_452);
x_659 = l_Lean_Expr_const___override(x_658, x_444);
x_660 = l_Lean_Expr_forallE___override(x_654, x_655, x_656, x_657);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
x_662 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_662, 0, x_661);
x_663 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_662, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_662);
x_17 = x_663;
goto block_25;
}
case 8:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_5);
x_664 = lean_ctor_get(x_421, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_421, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_421, 2);
lean_inc(x_666);
x_667 = lean_ctor_get(x_421, 3);
lean_inc(x_667);
x_668 = lean_ctor_get_uint8(x_421, sizeof(void*)*4 + 8);
lean_dec(x_421);
x_669 = l_Lean_Name_str___override(x_445, x_452);
x_670 = l_Lean_Expr_const___override(x_669, x_444);
x_671 = l_Lean_Expr_letE___override(x_664, x_665, x_666, x_667, x_668);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
x_673 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_673, 0, x_672);
x_674 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_673, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_673);
x_17 = x_674;
goto block_25;
}
case 9:
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_5);
x_675 = lean_ctor_get(x_421, 0);
lean_inc(x_675);
lean_dec(x_421);
x_676 = l_Lean_Name_str___override(x_445, x_452);
x_677 = l_Lean_Expr_const___override(x_676, x_444);
x_678 = l_Lean_Expr_lit___override(x_675);
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
x_680 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_680, 0, x_679);
x_681 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_680, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_680);
x_17 = x_681;
goto block_25;
}
case 10:
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_5);
x_682 = lean_ctor_get(x_421, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_421, 1);
lean_inc(x_683);
lean_dec(x_421);
x_684 = l_Lean_Name_str___override(x_445, x_452);
x_685 = l_Lean_Expr_const___override(x_684, x_444);
x_686 = l_Lean_Expr_mdata___override(x_682, x_683);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
x_688 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_688, 0, x_687);
x_689 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_688, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_688);
x_17 = x_689;
goto block_25;
}
default: 
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_5);
x_690 = lean_ctor_get(x_421, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_421, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_421, 2);
lean_inc(x_692);
lean_dec(x_421);
x_693 = l_Lean_Name_str___override(x_445, x_452);
x_694 = l_Lean_Expr_const___override(x_693, x_444);
x_695 = l_Lean_Expr_proj___override(x_690, x_691, x_692);
x_696 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
x_697 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_697, 0, x_696);
x_698 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_697, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_697);
x_17 = x_698;
goto block_25;
}
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_5);
x_699 = l_Lean_Name_str___override(x_445, x_452);
lean_inc(x_444);
x_700 = l_Lean_Expr_const___override(x_699, x_444);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_701 = x_444;
} else {
 lean_dec_ref(x_444);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(0, 2, 0);
} else {
 x_702 = x_701;
 lean_ctor_set_tag(x_702, 0);
}
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_421);
x_703 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_703, 0, x_702);
x_704 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_703, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_703);
x_17 = x_704;
goto block_25;
}
}
}
case 1:
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_5);
x_705 = lean_ctor_get(x_443, 1);
lean_inc(x_705);
lean_dec(x_443);
x_706 = lean_ctor_get(x_450, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_450, 1);
lean_inc(x_707);
lean_dec(x_450);
x_708 = l_Lean_Name_str___override(x_706, x_707);
x_709 = l_Lean_Name_str___override(x_708, x_705);
x_710 = l_Lean_Expr_const___override(x_709, x_444);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_421);
x_712 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_712, 0, x_711);
x_713 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_712, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_712);
x_17 = x_713;
goto block_25;
}
default: 
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
lean_dec(x_5);
x_714 = lean_ctor_get(x_443, 1);
lean_inc(x_714);
lean_dec(x_443);
x_715 = lean_ctor_get(x_450, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_450, 1);
lean_inc(x_716);
lean_dec(x_450);
x_717 = l_Lean_Name_num___override(x_715, x_716);
x_718 = l_Lean_Name_str___override(x_717, x_714);
x_719 = l_Lean_Expr_const___override(x_718, x_444);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_421);
x_721 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_721, 0, x_720);
x_722 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_721, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_721);
x_17 = x_722;
goto block_25;
}
}
}
default: 
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_446);
lean_dec(x_5);
x_723 = lean_ctor_get(x_443, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_443, 1);
lean_inc(x_724);
lean_dec(x_443);
x_725 = l_Lean_Name_num___override(x_723, x_724);
x_726 = l_Lean_Expr_const___override(x_725, x_444);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_421);
x_728 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_728, 0, x_727);
x_729 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_728, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_728);
x_17 = x_729;
goto block_25;
}
}
}
case 5:
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_5);
x_730 = lean_ctor_get(x_420, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_420, 1);
lean_inc(x_731);
lean_dec(x_420);
x_732 = l_Lean_Expr_app___override(x_730, x_731);
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_421);
x_734 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_734, 0, x_733);
x_735 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_734, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_734);
x_17 = x_735;
goto block_25;
}
case 6:
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_5);
x_736 = lean_ctor_get(x_420, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_420, 1);
lean_inc(x_737);
x_738 = lean_ctor_get(x_420, 2);
lean_inc(x_738);
x_739 = lean_ctor_get_uint8(x_420, sizeof(void*)*3 + 8);
lean_dec(x_420);
x_740 = l_Lean_Expr_lam___override(x_736, x_737, x_738, x_739);
x_741 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_421);
x_742 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_742, 0, x_741);
x_743 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_742, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_742);
x_17 = x_743;
goto block_25;
}
case 7:
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_5);
x_744 = lean_ctor_get(x_420, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_420, 1);
lean_inc(x_745);
x_746 = lean_ctor_get(x_420, 2);
lean_inc(x_746);
x_747 = lean_ctor_get_uint8(x_420, sizeof(void*)*3 + 8);
lean_dec(x_420);
x_748 = l_Lean_Expr_forallE___override(x_744, x_745, x_746, x_747);
x_749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_421);
x_750 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_750, 0, x_749);
x_751 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_750, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_750);
x_17 = x_751;
goto block_25;
}
case 8:
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_5);
x_752 = lean_ctor_get(x_420, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_420, 1);
lean_inc(x_753);
x_754 = lean_ctor_get(x_420, 2);
lean_inc(x_754);
x_755 = lean_ctor_get(x_420, 3);
lean_inc(x_755);
x_756 = lean_ctor_get_uint8(x_420, sizeof(void*)*4 + 8);
lean_dec(x_420);
x_757 = l_Lean_Expr_letE___override(x_752, x_753, x_754, x_755, x_756);
x_758 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_421);
x_759 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_759, 0, x_758);
x_760 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_759, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_759);
x_17 = x_760;
goto block_25;
}
case 9:
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_5);
x_761 = lean_ctor_get(x_420, 0);
lean_inc(x_761);
lean_dec(x_420);
x_762 = l_Lean_Expr_lit___override(x_761);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_421);
x_764 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_764, 0, x_763);
x_765 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_764, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_764);
x_17 = x_765;
goto block_25;
}
case 10:
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_5);
x_766 = lean_ctor_get(x_420, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_420, 1);
lean_inc(x_767);
lean_dec(x_420);
x_768 = l_Lean_Expr_mdata___override(x_766, x_767);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_421);
x_770 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_770, 0, x_769);
x_771 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_770, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_770);
x_17 = x_771;
goto block_25;
}
default: 
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_5);
x_772 = lean_ctor_get(x_420, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_420, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_420, 2);
lean_inc(x_774);
lean_dec(x_420);
x_775 = l_Lean_Expr_proj___override(x_772, x_773, x_774);
x_776 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_421);
x_777 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_777, 0, x_776);
x_778 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_777, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_777);
x_17 = x_778;
goto block_25;
}
}
}
else
{
lean_object* x_779; 
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_5);
x_779 = lean_box(0);
x_417 = x_779;
goto block_419;
}
}
else
{
lean_object* x_780; 
lean_dec(x_414);
lean_dec(x_5);
x_780 = lean_box(0);
x_417 = x_780;
goto block_419;
}
block_419:
{
lean_object* x_418; 
x_418 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_417, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_417);
x_17 = x_418;
goto block_25;
}
}
}
else
{
uint8_t x_781; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_781 = !lean_is_exclusive(x_33);
if (x_781 == 0)
{
return x_33;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_33, 0);
x_783 = lean_ctor_get(x_33, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_33);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
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
block_25:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
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
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_mk_empty_array_with_capacity(x_4);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_13);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg(x_3, x_5, x_14, x_16, x_12, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
lean_inc(x_21);
lean_inc(x_2);
x_22 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum(x_1, x_2, x_21, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_21);
lean_dec(x_2);
x_25 = !lean_is_exclusive(x_22);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_22, 0);
lean_dec(x_26);
x_27 = lean_box(0);
lean_ctor_set(x_22, 0, x_27);
return x_22;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_22, 1);
lean_inc(x_28);
lean_dec(x_22);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_22);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_22, 0);
lean_dec(x_32);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_21);
x_34 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_22, 0, x_34);
return x_22;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_22, 1);
lean_inc(x_35);
lean_dec(x_22);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_2);
lean_ctor_set(x_36, 1, x_21);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_21);
lean_dec(x_2);
x_39 = !lean_is_exclusive(x_22);
if (x_39 == 0)
{
return x_22;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_22, 0);
x_41 = lean_ctor_get(x_22, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_22);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_18);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_17);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_17, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_19, 0);
lean_inc(x_45);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_45);
return x_17;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_17, 1);
lean_inc(x_46);
lean_dec(x_17);
x_47 = lean_ctor_get(x_19, 0);
lean_inc(x_47);
lean_dec(x_19);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_8 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_9 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifyEnumWithDefault", 83, 83);
x_10 = lean_unsigned_to_nat(162u);
x_11 = lean_unsigned_to_nat(87u);
x_12 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_13 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
x_14 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_13, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 1);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_1);
x_21 = !lean_is_exclusive(x_14);
if (x_21 == 0)
{
return x_14;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_14, 0);
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_14);
x_24 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_4, 1);
x_34 = lean_nat_dec_lt(x_6, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_36 = l_Lean_instInhabitedExpr;
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_add(x_6, x_39);
x_41 = lean_array_get(x_36, x_1, x_40);
lean_dec(x_40);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Expr_bvar___override(x_42);
x_44 = lean_unbox(x_37);
x_45 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_44, x_38, x_43, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_43);
x_18 = x_45;
goto block_32;
}
case 1:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Expr_fvar___override(x_46);
x_48 = lean_unbox(x_37);
x_49 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_48, x_38, x_47, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_47);
x_18 = x_49;
goto block_32;
}
case 2:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec(x_41);
x_51 = l_Lean_Expr_mvar___override(x_50);
x_52 = lean_unbox(x_37);
x_53 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_52, x_38, x_51, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_51);
x_18 = x_53;
goto block_32;
}
case 3:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Lean_Expr_sort___override(x_54);
x_56 = lean_unbox(x_37);
x_57 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_56, x_38, x_55, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_55);
x_18 = x_57;
goto block_32;
}
case 4:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_41, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_dec(x_41);
x_60 = l_Lean_Expr_const___override(x_58, x_59);
x_61 = lean_unbox(x_37);
x_62 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_61, x_38, x_60, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_60);
x_18 = x_62;
goto block_32;
}
case 5:
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_41, 0);
lean_inc(x_64);
lean_dec(x_41);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Expr_bvar___override(x_65);
x_67 = l_Lean_Expr_app___override(x_64, x_66);
x_68 = lean_unbox(x_37);
x_69 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_68, x_38, x_67, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_67);
x_18 = x_69;
goto block_32;
}
case 1:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_41, 0);
lean_inc(x_70);
lean_dec(x_41);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_72 = l_Lean_Expr_fvar___override(x_71);
x_73 = l_Lean_Expr_app___override(x_70, x_72);
x_74 = lean_unbox(x_37);
x_75 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_74, x_38, x_73, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_73);
x_18 = x_75;
goto block_32;
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_41, 0);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
lean_dec(x_63);
x_78 = l_Lean_Expr_mvar___override(x_77);
x_79 = l_Lean_Expr_app___override(x_76, x_78);
x_80 = lean_unbox(x_37);
x_81 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_80, x_38, x_79, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_79);
x_18 = x_81;
goto block_32;
}
case 3:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_41, 0);
lean_inc(x_82);
lean_dec(x_41);
x_83 = lean_ctor_get(x_63, 0);
lean_inc(x_83);
lean_dec(x_63);
x_84 = l_Lean_Expr_sort___override(x_83);
x_85 = l_Lean_Expr_app___override(x_82, x_84);
x_86 = lean_unbox(x_37);
x_87 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_86, x_38, x_85, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_85);
x_18 = x_87;
goto block_32;
}
case 4:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_89 = lean_ctor_get(x_41, 0);
lean_inc(x_89);
lean_dec(x_41);
x_90 = lean_ctor_get(x_63, 0);
lean_inc(x_90);
lean_dec(x_63);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_38);
x_93 = lean_mk_string_unchecked("Unit", 4, 4);
x_94 = lean_mk_string_unchecked("unit", 4, 4);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = lean_name_eq(x_90, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_90, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
if (lean_obj_tag(x_98) == 6)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_nat_dec_eq(x_108, x_6);
lean_dec(x_108);
if (x_109 == 0)
{
lean_free_object(x_98);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
goto block_105;
}
else
{
if (x_96 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_100);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_array_get_size(x_2);
x_112 = lean_nat_sub(x_111, x_110);
lean_dec(x_111);
x_113 = lean_array_get(x_36, x_2, x_112);
lean_dec(x_112);
x_114 = lean_expr_eqv(x_89, x_113);
lean_dec(x_113);
lean_dec(x_89);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_115 = lean_box(x_96);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 0, x_115);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_98);
lean_ctor_set(x_116, 1, x_38);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_99);
return x_117;
}
else
{
lean_free_object(x_98);
x_12 = x_92;
x_13 = x_99;
goto block_17;
}
}
else
{
lean_free_object(x_98);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
goto block_105;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
lean_dec(x_98);
x_119 = lean_ctor_get(x_118, 2);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_nat_dec_eq(x_119, x_6);
lean_dec(x_119);
if (x_120 == 0)
{
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
goto block_105;
}
else
{
if (x_96 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_100);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_array_get_size(x_2);
x_123 = lean_nat_sub(x_122, x_121);
lean_dec(x_122);
x_124 = lean_array_get(x_36, x_2, x_123);
lean_dec(x_123);
x_125 = lean_expr_eqv(x_89, x_124);
lean_dec(x_124);
lean_dec(x_89);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_126 = lean_box(x_96);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_38);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_99);
return x_129;
}
else
{
x_12 = x_92;
x_13 = x_99;
goto block_17;
}
}
else
{
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
goto block_105;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_130 = lean_box(x_96);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_38);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_99);
return x_133;
}
block_105:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_box(x_96);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_38);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
return x_104;
}
}
else
{
uint8_t x_134; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_134 = !lean_is_exclusive(x_97);
if (x_134 == 0)
{
return x_97;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_97, 0);
x_136 = lean_ctor_get(x_97, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_97);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_89);
x_138 = lean_infer_type(x_89, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 7)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_141 = lean_ctor_get(x_138, 1);
x_142 = lean_ctor_get(x_138, 0);
lean_dec(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_139, 2);
lean_inc(x_144);
lean_dec(x_139);
x_145 = l_Lean_Expr_hasLooseBVars(x_144);
if (x_145 == 0)
{
switch (lean_obj_tag(x_144)) {
case 0:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_free_object(x_138);
lean_dec(x_89);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Expr_bvar___override(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_150 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_149, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_149);
x_18 = x_150;
goto block_32;
}
case 1:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_free_object(x_138);
lean_dec(x_89);
x_151 = lean_ctor_get(x_144, 0);
lean_inc(x_151);
lean_dec(x_144);
x_152 = l_Lean_Expr_fvar___override(x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_155 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_154, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_154);
x_18 = x_155;
goto block_32;
}
case 2:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_free_object(x_138);
lean_dec(x_89);
x_156 = lean_ctor_get(x_144, 0);
lean_inc(x_156);
lean_dec(x_144);
x_157 = l_Lean_Expr_mvar___override(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_143);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_160 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_159, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_159);
x_18 = x_160;
goto block_32;
}
case 3:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_138);
lean_dec(x_89);
x_161 = lean_ctor_get(x_144, 0);
lean_inc(x_161);
lean_dec(x_144);
x_162 = l_Lean_Expr_sort___override(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_143);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_165 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_164, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_164);
x_18 = x_165;
goto block_32;
}
case 4:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_free_object(x_138);
lean_dec(x_89);
x_166 = lean_ctor_get(x_144, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_144, 1);
lean_inc(x_167);
lean_dec(x_144);
x_168 = l_Lean_Expr_const___override(x_166, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_143);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_171 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_170, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_170);
x_18 = x_171;
goto block_32;
}
case 5:
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_144, 1);
lean_inc(x_172);
switch (lean_obj_tag(x_172)) {
case 0:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_free_object(x_138);
lean_dec(x_89);
x_173 = lean_ctor_get(x_144, 0);
lean_inc(x_173);
lean_dec(x_144);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_Expr_bvar___override(x_174);
x_176 = l_Lean_Expr_app___override(x_173, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_143);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_179 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_178, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_178);
x_18 = x_179;
goto block_32;
}
case 1:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_free_object(x_138);
lean_dec(x_89);
x_180 = lean_ctor_get(x_144, 0);
lean_inc(x_180);
lean_dec(x_144);
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
lean_dec(x_172);
x_182 = l_Lean_Expr_fvar___override(x_181);
x_183 = l_Lean_Expr_app___override(x_180, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_143);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_186 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_185, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_185);
x_18 = x_186;
goto block_32;
}
case 2:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_138);
lean_dec(x_89);
x_187 = lean_ctor_get(x_144, 0);
lean_inc(x_187);
lean_dec(x_144);
x_188 = lean_ctor_get(x_172, 0);
lean_inc(x_188);
lean_dec(x_172);
x_189 = l_Lean_Expr_mvar___override(x_188);
x_190 = l_Lean_Expr_app___override(x_187, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_143);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_193 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_192, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_192);
x_18 = x_193;
goto block_32;
}
case 3:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_free_object(x_138);
lean_dec(x_89);
x_194 = lean_ctor_get(x_144, 0);
lean_inc(x_194);
lean_dec(x_144);
x_195 = lean_ctor_get(x_172, 0);
lean_inc(x_195);
lean_dec(x_172);
x_196 = l_Lean_Expr_sort___override(x_195);
x_197 = l_Lean_Expr_app___override(x_194, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_143);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_200 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_199, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_199);
x_18 = x_200;
goto block_32;
}
case 4:
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_172, 1);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_144);
lean_dec(x_143);
x_202 = lean_ctor_get(x_172, 0);
lean_inc(x_202);
lean_dec(x_172);
x_203 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_203, 0, x_202);
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_Array_findIdx_x3f_loop___redArg(x_203, x_3, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_free_object(x_138);
lean_dec(x_89);
x_206 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_207 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifyEnumWithDefault", 83, 83);
x_208 = lean_unsigned_to_nat(163u);
x_209 = lean_unsigned_to_nat(74u);
x_210 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_211 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_206, x_207, x_208, x_209, x_210);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_212 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_211, x_7, x_8, x_9, x_10, x_141);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_12 = x_92;
x_13 = x_213;
goto block_17;
}
else
{
uint8_t x_214; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
return x_212;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_212, 0);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_212);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_205);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_205, 0);
x_220 = lean_nat_add(x_219, x_39);
lean_dec(x_219);
x_221 = lean_array_get(x_36, x_2, x_220);
lean_dec(x_220);
x_222 = lean_expr_eqv(x_89, x_221);
lean_dec(x_221);
lean_dec(x_89);
if (x_222 == 0)
{
if (x_96 == 0)
{
lean_free_object(x_205);
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
else
{
lean_object* x_223; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_ctor_set(x_205, 0, x_37);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_205);
lean_ctor_set(x_223, 1, x_38);
lean_ctor_set(x_138, 0, x_223);
return x_138;
}
}
else
{
lean_free_object(x_205);
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_224 = lean_ctor_get(x_205, 0);
lean_inc(x_224);
lean_dec(x_205);
x_225 = lean_nat_add(x_224, x_39);
lean_dec(x_224);
x_226 = lean_array_get(x_36, x_2, x_225);
lean_dec(x_225);
x_227 = lean_expr_eqv(x_89, x_226);
lean_dec(x_226);
lean_dec(x_89);
if (x_227 == 0)
{
if (x_96 == 0)
{
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_37);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_38);
lean_ctor_set(x_138, 0, x_229);
return x_138;
}
}
else
{
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_free_object(x_138);
lean_dec(x_89);
x_230 = lean_ctor_get(x_144, 0);
lean_inc(x_230);
lean_dec(x_144);
x_231 = lean_ctor_get(x_172, 0);
lean_inc(x_231);
lean_dec(x_172);
lean_inc(x_201);
x_232 = l_Lean_Expr_const___override(x_231, x_201);
x_233 = !lean_is_exclusive(x_201);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_201, 1);
lean_dec(x_234);
x_235 = lean_ctor_get(x_201, 0);
lean_dec(x_235);
x_236 = l_Lean_Expr_app___override(x_230, x_232);
lean_ctor_set_tag(x_201, 0);
lean_ctor_set(x_201, 1, x_236);
lean_ctor_set(x_201, 0, x_143);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_201);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_238 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_237, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_237);
x_18 = x_238;
goto block_32;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_201);
x_239 = l_Lean_Expr_app___override(x_230, x_232);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_143);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_242 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_241, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_241);
x_18 = x_242;
goto block_32;
}
}
}
case 5:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_free_object(x_138);
lean_dec(x_89);
x_243 = lean_ctor_get(x_144, 0);
lean_inc(x_243);
lean_dec(x_144);
x_244 = lean_ctor_get(x_172, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_172, 1);
lean_inc(x_245);
lean_dec(x_172);
x_246 = l_Lean_Expr_app___override(x_244, x_245);
x_247 = l_Lean_Expr_app___override(x_243, x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_143);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_250 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_249, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_249);
x_18 = x_250;
goto block_32;
}
case 6:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_free_object(x_138);
lean_dec(x_89);
x_251 = lean_ctor_get(x_144, 0);
lean_inc(x_251);
lean_dec(x_144);
x_252 = lean_ctor_get(x_172, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_172, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_172, 2);
lean_inc(x_254);
x_255 = lean_ctor_get_uint8(x_172, sizeof(void*)*3 + 8);
lean_dec(x_172);
x_256 = l_Lean_Expr_lam___override(x_252, x_253, x_254, x_255);
x_257 = l_Lean_Expr_app___override(x_251, x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_143);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_260 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_259, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_259);
x_18 = x_260;
goto block_32;
}
case 7:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_free_object(x_138);
lean_dec(x_89);
x_261 = lean_ctor_get(x_144, 0);
lean_inc(x_261);
lean_dec(x_144);
x_262 = lean_ctor_get(x_172, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_172, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_172, 2);
lean_inc(x_264);
x_265 = lean_ctor_get_uint8(x_172, sizeof(void*)*3 + 8);
lean_dec(x_172);
x_266 = l_Lean_Expr_forallE___override(x_262, x_263, x_264, x_265);
x_267 = l_Lean_Expr_app___override(x_261, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_143);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_270 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_269, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_269);
x_18 = x_270;
goto block_32;
}
case 8:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_free_object(x_138);
lean_dec(x_89);
x_271 = lean_ctor_get(x_144, 0);
lean_inc(x_271);
lean_dec(x_144);
x_272 = lean_ctor_get(x_172, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_172, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_172, 2);
lean_inc(x_274);
x_275 = lean_ctor_get(x_172, 3);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_172, sizeof(void*)*4 + 8);
lean_dec(x_172);
x_277 = l_Lean_Expr_letE___override(x_272, x_273, x_274, x_275, x_276);
x_278 = l_Lean_Expr_app___override(x_271, x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_143);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_281 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_280, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_280);
x_18 = x_281;
goto block_32;
}
case 9:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_free_object(x_138);
lean_dec(x_89);
x_282 = lean_ctor_get(x_144, 0);
lean_inc(x_282);
lean_dec(x_144);
x_283 = lean_ctor_get(x_172, 0);
lean_inc(x_283);
lean_dec(x_172);
x_284 = l_Lean_Expr_lit___override(x_283);
x_285 = l_Lean_Expr_app___override(x_282, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_143);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_288 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_287, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_287);
x_18 = x_288;
goto block_32;
}
case 10:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_free_object(x_138);
lean_dec(x_89);
x_289 = lean_ctor_get(x_144, 0);
lean_inc(x_289);
lean_dec(x_144);
x_290 = lean_ctor_get(x_172, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_172, 1);
lean_inc(x_291);
lean_dec(x_172);
x_292 = l_Lean_Expr_mdata___override(x_290, x_291);
x_293 = l_Lean_Expr_app___override(x_289, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_143);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_294);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_296 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_295, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_295);
x_18 = x_296;
goto block_32;
}
default: 
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_free_object(x_138);
lean_dec(x_89);
x_297 = lean_ctor_get(x_144, 0);
lean_inc(x_297);
lean_dec(x_144);
x_298 = lean_ctor_get(x_172, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_172, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_172, 2);
lean_inc(x_300);
lean_dec(x_172);
x_301 = l_Lean_Expr_proj___override(x_298, x_299, x_300);
x_302 = l_Lean_Expr_app___override(x_297, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_143);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_305 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_304, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_304);
x_18 = x_305;
goto block_32;
}
}
}
case 6:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_free_object(x_138);
lean_dec(x_89);
x_306 = lean_ctor_get(x_144, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_144, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_144, 2);
lean_inc(x_308);
x_309 = lean_ctor_get_uint8(x_144, sizeof(void*)*3 + 8);
lean_dec(x_144);
x_310 = l_Lean_Expr_lam___override(x_306, x_307, x_308, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_143);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_313 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_312, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_312);
x_18 = x_313;
goto block_32;
}
case 7:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_free_object(x_138);
lean_dec(x_89);
x_314 = lean_ctor_get(x_144, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_144, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_144, 2);
lean_inc(x_316);
x_317 = lean_ctor_get_uint8(x_144, sizeof(void*)*3 + 8);
lean_dec(x_144);
x_318 = l_Lean_Expr_forallE___override(x_314, x_315, x_316, x_317);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_143);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_319);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_321 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_320, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_320);
x_18 = x_321;
goto block_32;
}
case 8:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_free_object(x_138);
lean_dec(x_89);
x_322 = lean_ctor_get(x_144, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_144, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_144, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_144, 3);
lean_inc(x_325);
x_326 = lean_ctor_get_uint8(x_144, sizeof(void*)*4 + 8);
lean_dec(x_144);
x_327 = l_Lean_Expr_letE___override(x_322, x_323, x_324, x_325, x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_143);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_330 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_329, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_329);
x_18 = x_330;
goto block_32;
}
case 9:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_free_object(x_138);
lean_dec(x_89);
x_331 = lean_ctor_get(x_144, 0);
lean_inc(x_331);
lean_dec(x_144);
x_332 = l_Lean_Expr_lit___override(x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_143);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_333);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_335 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_334, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_334);
x_18 = x_335;
goto block_32;
}
case 10:
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_free_object(x_138);
lean_dec(x_89);
x_336 = lean_ctor_get(x_144, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_144, 1);
lean_inc(x_337);
lean_dec(x_144);
x_338 = l_Lean_Expr_mdata___override(x_336, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_143);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_339);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_341 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_340, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_340);
x_18 = x_341;
goto block_32;
}
default: 
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_free_object(x_138);
lean_dec(x_89);
x_342 = lean_ctor_get(x_144, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_144, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_144, 2);
lean_inc(x_344);
lean_dec(x_144);
x_345 = l_Lean_Expr_proj___override(x_342, x_343, x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_143);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_346);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_348 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_347, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_347);
x_18 = x_348;
goto block_32;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_144);
lean_dec(x_143);
lean_free_object(x_138);
lean_dec(x_89);
x_349 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_350 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_349, x_7, x_8, x_9, x_10, x_141);
x_18 = x_350;
goto block_32;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_351 = lean_ctor_get(x_138, 1);
lean_inc(x_351);
lean_dec(x_138);
x_352 = lean_ctor_get(x_139, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_139, 2);
lean_inc(x_353);
lean_dec(x_139);
x_354 = l_Lean_Expr_hasLooseBVars(x_353);
if (x_354 == 0)
{
switch (lean_obj_tag(x_353)) {
case 0:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_89);
x_355 = lean_ctor_get(x_353, 0);
lean_inc(x_355);
lean_dec(x_353);
x_356 = l_Lean_Expr_bvar___override(x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_357);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_359 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_358, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_358);
x_18 = x_359;
goto block_32;
}
case 1:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_89);
x_360 = lean_ctor_get(x_353, 0);
lean_inc(x_360);
lean_dec(x_353);
x_361 = l_Lean_Expr_fvar___override(x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_352);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_362);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_364 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_363, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_363);
x_18 = x_364;
goto block_32;
}
case 2:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_89);
x_365 = lean_ctor_get(x_353, 0);
lean_inc(x_365);
lean_dec(x_353);
x_366 = l_Lean_Expr_mvar___override(x_365);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_352);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_369 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_368, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_368);
x_18 = x_369;
goto block_32;
}
case 3:
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_89);
x_370 = lean_ctor_get(x_353, 0);
lean_inc(x_370);
lean_dec(x_353);
x_371 = l_Lean_Expr_sort___override(x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_352);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_374 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_373, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_373);
x_18 = x_374;
goto block_32;
}
case 4:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_89);
x_375 = lean_ctor_get(x_353, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_353, 1);
lean_inc(x_376);
lean_dec(x_353);
x_377 = l_Lean_Expr_const___override(x_375, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_352);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_378);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_380 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_379, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_379);
x_18 = x_380;
goto block_32;
}
case 5:
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_353, 1);
lean_inc(x_381);
switch (lean_obj_tag(x_381)) {
case 0:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_89);
x_382 = lean_ctor_get(x_353, 0);
lean_inc(x_382);
lean_dec(x_353);
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec(x_381);
x_384 = l_Lean_Expr_bvar___override(x_383);
x_385 = l_Lean_Expr_app___override(x_382, x_384);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_352);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_386);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_388 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_387, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_387);
x_18 = x_388;
goto block_32;
}
case 1:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_89);
x_389 = lean_ctor_get(x_353, 0);
lean_inc(x_389);
lean_dec(x_353);
x_390 = lean_ctor_get(x_381, 0);
lean_inc(x_390);
lean_dec(x_381);
x_391 = l_Lean_Expr_fvar___override(x_390);
x_392 = l_Lean_Expr_app___override(x_389, x_391);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_352);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_393);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_395 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_394, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_394);
x_18 = x_395;
goto block_32;
}
case 2:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_89);
x_396 = lean_ctor_get(x_353, 0);
lean_inc(x_396);
lean_dec(x_353);
x_397 = lean_ctor_get(x_381, 0);
lean_inc(x_397);
lean_dec(x_381);
x_398 = l_Lean_Expr_mvar___override(x_397);
x_399 = l_Lean_Expr_app___override(x_396, x_398);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_352);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_400);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_402 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_401, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_401);
x_18 = x_402;
goto block_32;
}
case 3:
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_89);
x_403 = lean_ctor_get(x_353, 0);
lean_inc(x_403);
lean_dec(x_353);
x_404 = lean_ctor_get(x_381, 0);
lean_inc(x_404);
lean_dec(x_381);
x_405 = l_Lean_Expr_sort___override(x_404);
x_406 = l_Lean_Expr_app___override(x_403, x_405);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_352);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_408, 0, x_407);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_409 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_408, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_408);
x_18 = x_409;
goto block_32;
}
case 4:
{
lean_object* x_410; 
x_410 = lean_ctor_get(x_381, 1);
lean_inc(x_410);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_353);
lean_dec(x_352);
x_411 = lean_ctor_get(x_381, 0);
lean_inc(x_411);
lean_dec(x_381);
x_412 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_412, 0, x_411);
x_413 = lean_unsigned_to_nat(0u);
x_414 = l_Array_findIdx_x3f_loop___redArg(x_412, x_3, x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_89);
x_415 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_416 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifyEnumWithDefault", 83, 83);
x_417 = lean_unsigned_to_nat(163u);
x_418 = lean_unsigned_to_nat(74u);
x_419 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_420 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_415, x_416, x_417, x_418, x_419);
lean_dec(x_419);
lean_dec(x_416);
lean_dec(x_415);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_421 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_420, x_7, x_8, x_9, x_10, x_351);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_12 = x_92;
x_13 = x_422;
goto block_17;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_423 = lean_ctor_get(x_421, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_421, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_425 = x_421;
} else {
 lean_dec_ref(x_421);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
x_427 = lean_ctor_get(x_414, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 x_428 = x_414;
} else {
 lean_dec_ref(x_414);
 x_428 = lean_box(0);
}
x_429 = lean_nat_add(x_427, x_39);
lean_dec(x_427);
x_430 = lean_array_get(x_36, x_2, x_429);
lean_dec(x_429);
x_431 = lean_expr_eqv(x_89, x_430);
lean_dec(x_430);
lean_dec(x_89);
if (x_431 == 0)
{
if (x_96 == 0)
{
lean_dec(x_428);
x_12 = x_92;
x_13 = x_351;
goto block_17;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
if (lean_is_scalar(x_428)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_428;
}
lean_ctor_set(x_432, 0, x_37);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_38);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_351);
return x_434;
}
}
else
{
lean_dec(x_428);
x_12 = x_92;
x_13 = x_351;
goto block_17;
}
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_89);
x_435 = lean_ctor_get(x_353, 0);
lean_inc(x_435);
lean_dec(x_353);
x_436 = lean_ctor_get(x_381, 0);
lean_inc(x_436);
lean_dec(x_381);
lean_inc(x_410);
x_437 = l_Lean_Expr_const___override(x_436, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_438 = x_410;
} else {
 lean_dec_ref(x_410);
 x_438 = lean_box(0);
}
x_439 = l_Lean_Expr_app___override(x_435, x_437);
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_438;
 lean_ctor_set_tag(x_440, 0);
}
lean_ctor_set(x_440, 0, x_352);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_440);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_442 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_441, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_441);
x_18 = x_442;
goto block_32;
}
}
case 5:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_89);
x_443 = lean_ctor_get(x_353, 0);
lean_inc(x_443);
lean_dec(x_353);
x_444 = lean_ctor_get(x_381, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_381, 1);
lean_inc(x_445);
lean_dec(x_381);
x_446 = l_Lean_Expr_app___override(x_444, x_445);
x_447 = l_Lean_Expr_app___override(x_443, x_446);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_352);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_449, 0, x_448);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_450 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_449, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_449);
x_18 = x_450;
goto block_32;
}
case 6:
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_89);
x_451 = lean_ctor_get(x_353, 0);
lean_inc(x_451);
lean_dec(x_353);
x_452 = lean_ctor_get(x_381, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_381, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_381, 2);
lean_inc(x_454);
x_455 = lean_ctor_get_uint8(x_381, sizeof(void*)*3 + 8);
lean_dec(x_381);
x_456 = l_Lean_Expr_lam___override(x_452, x_453, x_454, x_455);
x_457 = l_Lean_Expr_app___override(x_451, x_456);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_352);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_458);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_460 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_459, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_459);
x_18 = x_460;
goto block_32;
}
case 7:
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_89);
x_461 = lean_ctor_get(x_353, 0);
lean_inc(x_461);
lean_dec(x_353);
x_462 = lean_ctor_get(x_381, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_381, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_381, 2);
lean_inc(x_464);
x_465 = lean_ctor_get_uint8(x_381, sizeof(void*)*3 + 8);
lean_dec(x_381);
x_466 = l_Lean_Expr_forallE___override(x_462, x_463, x_464, x_465);
x_467 = l_Lean_Expr_app___override(x_461, x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_352);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_468);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_470 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_469, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_469);
x_18 = x_470;
goto block_32;
}
case 8:
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_89);
x_471 = lean_ctor_get(x_353, 0);
lean_inc(x_471);
lean_dec(x_353);
x_472 = lean_ctor_get(x_381, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_381, 1);
lean_inc(x_473);
x_474 = lean_ctor_get(x_381, 2);
lean_inc(x_474);
x_475 = lean_ctor_get(x_381, 3);
lean_inc(x_475);
x_476 = lean_ctor_get_uint8(x_381, sizeof(void*)*4 + 8);
lean_dec(x_381);
x_477 = l_Lean_Expr_letE___override(x_472, x_473, x_474, x_475, x_476);
x_478 = l_Lean_Expr_app___override(x_471, x_477);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_352);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_479);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_481 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_480, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_480);
x_18 = x_481;
goto block_32;
}
case 9:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_89);
x_482 = lean_ctor_get(x_353, 0);
lean_inc(x_482);
lean_dec(x_353);
x_483 = lean_ctor_get(x_381, 0);
lean_inc(x_483);
lean_dec(x_381);
x_484 = l_Lean_Expr_lit___override(x_483);
x_485 = l_Lean_Expr_app___override(x_482, x_484);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_352);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_487, 0, x_486);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_488 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_487, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_487);
x_18 = x_488;
goto block_32;
}
case 10:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_89);
x_489 = lean_ctor_get(x_353, 0);
lean_inc(x_489);
lean_dec(x_353);
x_490 = lean_ctor_get(x_381, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_381, 1);
lean_inc(x_491);
lean_dec(x_381);
x_492 = l_Lean_Expr_mdata___override(x_490, x_491);
x_493 = l_Lean_Expr_app___override(x_489, x_492);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_352);
lean_ctor_set(x_494, 1, x_493);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_494);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_496 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_495, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_495);
x_18 = x_496;
goto block_32;
}
default: 
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_89);
x_497 = lean_ctor_get(x_353, 0);
lean_inc(x_497);
lean_dec(x_353);
x_498 = lean_ctor_get(x_381, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_381, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_381, 2);
lean_inc(x_500);
lean_dec(x_381);
x_501 = l_Lean_Expr_proj___override(x_498, x_499, x_500);
x_502 = l_Lean_Expr_app___override(x_497, x_501);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_352);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_504, 0, x_503);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_505 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_504, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_504);
x_18 = x_505;
goto block_32;
}
}
}
case 6:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_89);
x_506 = lean_ctor_get(x_353, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_353, 1);
lean_inc(x_507);
x_508 = lean_ctor_get(x_353, 2);
lean_inc(x_508);
x_509 = lean_ctor_get_uint8(x_353, sizeof(void*)*3 + 8);
lean_dec(x_353);
x_510 = l_Lean_Expr_lam___override(x_506, x_507, x_508, x_509);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_352);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_512, 0, x_511);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_513 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_512, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_512);
x_18 = x_513;
goto block_32;
}
case 7:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_89);
x_514 = lean_ctor_get(x_353, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_353, 1);
lean_inc(x_515);
x_516 = lean_ctor_get(x_353, 2);
lean_inc(x_516);
x_517 = lean_ctor_get_uint8(x_353, sizeof(void*)*3 + 8);
lean_dec(x_353);
x_518 = l_Lean_Expr_forallE___override(x_514, x_515, x_516, x_517);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_352);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_519);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_521 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_520, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_520);
x_18 = x_521;
goto block_32;
}
case 8:
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_89);
x_522 = lean_ctor_get(x_353, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_353, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_353, 2);
lean_inc(x_524);
x_525 = lean_ctor_get(x_353, 3);
lean_inc(x_525);
x_526 = lean_ctor_get_uint8(x_353, sizeof(void*)*4 + 8);
lean_dec(x_353);
x_527 = l_Lean_Expr_letE___override(x_522, x_523, x_524, x_525, x_526);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_352);
lean_ctor_set(x_528, 1, x_527);
x_529 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_529, 0, x_528);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_530 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_529, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_529);
x_18 = x_530;
goto block_32;
}
case 9:
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_89);
x_531 = lean_ctor_get(x_353, 0);
lean_inc(x_531);
lean_dec(x_353);
x_532 = l_Lean_Expr_lit___override(x_531);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_352);
lean_ctor_set(x_533, 1, x_532);
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_533);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_535 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_534, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_534);
x_18 = x_535;
goto block_32;
}
case 10:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_89);
x_536 = lean_ctor_get(x_353, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_353, 1);
lean_inc(x_537);
lean_dec(x_353);
x_538 = l_Lean_Expr_mdata___override(x_536, x_537);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_352);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_540, 0, x_539);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_541 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_540, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_540);
x_18 = x_541;
goto block_32;
}
default: 
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_89);
x_542 = lean_ctor_get(x_353, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_353, 1);
lean_inc(x_543);
x_544 = lean_ctor_get(x_353, 2);
lean_inc(x_544);
lean_dec(x_353);
x_545 = l_Lean_Expr_proj___override(x_542, x_543, x_544);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_352);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_547, 0, x_546);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_548 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_547, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_547);
x_18 = x_548;
goto block_32;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_89);
x_549 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_550 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_549, x_7, x_8, x_9, x_10, x_351);
x_18 = x_550;
goto block_32;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_139);
lean_dec(x_89);
x_551 = lean_ctor_get(x_138, 1);
lean_inc(x_551);
lean_dec(x_138);
x_552 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_553 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_552, x_7, x_8, x_9, x_10, x_551);
x_18 = x_553;
goto block_32;
}
}
else
{
uint8_t x_554; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_554 = !lean_is_exclusive(x_138);
if (x_554 == 0)
{
return x_138;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_138, 0);
x_556 = lean_ctor_get(x_138, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_138);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; lean_object* x_563; 
x_558 = lean_ctor_get(x_41, 0);
lean_inc(x_558);
lean_dec(x_41);
x_559 = lean_ctor_get(x_63, 0);
lean_inc(x_559);
lean_dec(x_63);
x_560 = l_Lean_Expr_const___override(x_559, x_88);
x_561 = l_Lean_Expr_app___override(x_558, x_560);
x_562 = lean_unbox(x_37);
x_563 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_562, x_38, x_561, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_561);
x_18 = x_563;
goto block_32;
}
}
case 5:
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; 
x_564 = lean_ctor_get(x_41, 0);
lean_inc(x_564);
lean_dec(x_41);
x_565 = lean_ctor_get(x_63, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_63, 1);
lean_inc(x_566);
lean_dec(x_63);
x_567 = l_Lean_Expr_app___override(x_565, x_566);
x_568 = l_Lean_Expr_app___override(x_564, x_567);
x_569 = lean_unbox(x_37);
x_570 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_569, x_38, x_568, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_568);
x_18 = x_570;
goto block_32;
}
case 6:
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; lean_object* x_579; 
x_571 = lean_ctor_get(x_41, 0);
lean_inc(x_571);
lean_dec(x_41);
x_572 = lean_ctor_get(x_63, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_63, 1);
lean_inc(x_573);
x_574 = lean_ctor_get(x_63, 2);
lean_inc(x_574);
x_575 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_dec(x_63);
x_576 = l_Lean_Expr_lam___override(x_572, x_573, x_574, x_575);
x_577 = l_Lean_Expr_app___override(x_571, x_576);
x_578 = lean_unbox(x_37);
x_579 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_578, x_38, x_577, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_577);
x_18 = x_579;
goto block_32;
}
case 7:
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; lean_object* x_588; 
x_580 = lean_ctor_get(x_41, 0);
lean_inc(x_580);
lean_dec(x_41);
x_581 = lean_ctor_get(x_63, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_63, 1);
lean_inc(x_582);
x_583 = lean_ctor_get(x_63, 2);
lean_inc(x_583);
x_584 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_dec(x_63);
x_585 = l_Lean_Expr_forallE___override(x_581, x_582, x_583, x_584);
x_586 = l_Lean_Expr_app___override(x_580, x_585);
x_587 = lean_unbox(x_37);
x_588 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_587, x_38, x_586, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_586);
x_18 = x_588;
goto block_32;
}
case 8:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; 
x_589 = lean_ctor_get(x_41, 0);
lean_inc(x_589);
lean_dec(x_41);
x_590 = lean_ctor_get(x_63, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_63, 1);
lean_inc(x_591);
x_592 = lean_ctor_get(x_63, 2);
lean_inc(x_592);
x_593 = lean_ctor_get(x_63, 3);
lean_inc(x_593);
x_594 = lean_ctor_get_uint8(x_63, sizeof(void*)*4 + 8);
lean_dec(x_63);
x_595 = l_Lean_Expr_letE___override(x_590, x_591, x_592, x_593, x_594);
x_596 = l_Lean_Expr_app___override(x_589, x_595);
x_597 = lean_unbox(x_37);
x_598 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_597, x_38, x_596, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_596);
x_18 = x_598;
goto block_32;
}
case 9:
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_604; 
x_599 = lean_ctor_get(x_41, 0);
lean_inc(x_599);
lean_dec(x_41);
x_600 = lean_ctor_get(x_63, 0);
lean_inc(x_600);
lean_dec(x_63);
x_601 = l_Lean_Expr_lit___override(x_600);
x_602 = l_Lean_Expr_app___override(x_599, x_601);
x_603 = lean_unbox(x_37);
x_604 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_603, x_38, x_602, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_602);
x_18 = x_604;
goto block_32;
}
case 10:
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; 
x_605 = lean_ctor_get(x_41, 0);
lean_inc(x_605);
lean_dec(x_41);
x_606 = lean_ctor_get(x_63, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_63, 1);
lean_inc(x_607);
lean_dec(x_63);
x_608 = l_Lean_Expr_mdata___override(x_606, x_607);
x_609 = l_Lean_Expr_app___override(x_605, x_608);
x_610 = lean_unbox(x_37);
x_611 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_610, x_38, x_609, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_609);
x_18 = x_611;
goto block_32;
}
default: 
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; lean_object* x_619; 
x_612 = lean_ctor_get(x_41, 0);
lean_inc(x_612);
lean_dec(x_41);
x_613 = lean_ctor_get(x_63, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_63, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_63, 2);
lean_inc(x_615);
lean_dec(x_63);
x_616 = l_Lean_Expr_proj___override(x_613, x_614, x_615);
x_617 = l_Lean_Expr_app___override(x_612, x_616);
x_618 = lean_unbox(x_37);
x_619 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_618, x_38, x_617, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_617);
x_18 = x_619;
goto block_32;
}
}
}
case 6:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; 
x_620 = lean_ctor_get(x_41, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_41, 1);
lean_inc(x_621);
x_622 = lean_ctor_get(x_41, 2);
lean_inc(x_622);
x_623 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_624 = l_Lean_Expr_lam___override(x_620, x_621, x_622, x_623);
x_625 = lean_unbox(x_37);
x_626 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_625, x_38, x_624, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_624);
x_18 = x_626;
goto block_32;
}
case 7:
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; lean_object* x_631; uint8_t x_632; lean_object* x_633; 
x_627 = lean_ctor_get(x_41, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_41, 1);
lean_inc(x_628);
x_629 = lean_ctor_get(x_41, 2);
lean_inc(x_629);
x_630 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_631 = l_Lean_Expr_forallE___override(x_627, x_628, x_629, x_630);
x_632 = lean_unbox(x_37);
x_633 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_632, x_38, x_631, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_631);
x_18 = x_633;
goto block_32;
}
case 8:
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; lean_object* x_639; uint8_t x_640; lean_object* x_641; 
x_634 = lean_ctor_get(x_41, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_41, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_41, 2);
lean_inc(x_636);
x_637 = lean_ctor_get(x_41, 3);
lean_inc(x_637);
x_638 = lean_ctor_get_uint8(x_41, sizeof(void*)*4 + 8);
lean_dec(x_41);
x_639 = l_Lean_Expr_letE___override(x_634, x_635, x_636, x_637, x_638);
x_640 = lean_unbox(x_37);
x_641 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_640, x_38, x_639, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_639);
x_18 = x_641;
goto block_32;
}
case 9:
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; 
x_642 = lean_ctor_get(x_41, 0);
lean_inc(x_642);
lean_dec(x_41);
x_643 = l_Lean_Expr_lit___override(x_642);
x_644 = lean_unbox(x_37);
x_645 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_644, x_38, x_643, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_643);
x_18 = x_645;
goto block_32;
}
case 10:
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; 
x_646 = lean_ctor_get(x_41, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_41, 1);
lean_inc(x_647);
lean_dec(x_41);
x_648 = l_Lean_Expr_mdata___override(x_646, x_647);
x_649 = lean_unbox(x_37);
x_650 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_649, x_38, x_648, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_648);
x_18 = x_650;
goto block_32;
}
default: 
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; 
x_651 = lean_ctor_get(x_41, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_41, 1);
lean_inc(x_652);
x_653 = lean_ctor_get(x_41, 2);
lean_inc(x_653);
lean_dec(x_41);
x_654 = l_Lean_Expr_proj___override(x_651, x_652, x_653);
x_655 = lean_unbox(x_37);
x_656 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_655, x_38, x_654, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_654);
x_18 = x_656;
goto block_32;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_nat_add(x_6, x_14);
lean_dec(x_6);
x_5 = x_12;
x_6 = x_15;
x_11 = x_13;
goto _start;
}
block_32:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_12 = x_27;
x_13 = x_26;
goto block_17;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_18; lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_4, 1);
x_34 = lean_nat_dec_lt(x_6, x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_5);
lean_ctor_set(x_35, 1, x_11);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_36 = l_Lean_instInhabitedExpr;
x_37 = lean_box(0);
x_38 = lean_box(0);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_add(x_6, x_39);
x_41 = lean_array_get(x_36, x_1, x_40);
lean_dec(x_40);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Expr_bvar___override(x_42);
x_44 = lean_unbox(x_37);
x_45 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_44, x_38, x_43, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_43);
x_18 = x_45;
goto block_32;
}
case 1:
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_41, 0);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Expr_fvar___override(x_46);
x_48 = lean_unbox(x_37);
x_49 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_48, x_38, x_47, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_47);
x_18 = x_49;
goto block_32;
}
case 2:
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_41, 0);
lean_inc(x_50);
lean_dec(x_41);
x_51 = l_Lean_Expr_mvar___override(x_50);
x_52 = lean_unbox(x_37);
x_53 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_52, x_38, x_51, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_51);
x_18 = x_53;
goto block_32;
}
case 3:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Lean_Expr_sort___override(x_54);
x_56 = lean_unbox(x_37);
x_57 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_56, x_38, x_55, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_55);
x_18 = x_57;
goto block_32;
}
case 4:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_41, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_41, 1);
lean_inc(x_59);
lean_dec(x_41);
x_60 = l_Lean_Expr_const___override(x_58, x_59);
x_61 = lean_unbox(x_37);
x_62 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_61, x_38, x_60, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_60);
x_18 = x_62;
goto block_32;
}
case 5:
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_41, 1);
lean_inc(x_63);
switch (lean_obj_tag(x_63)) {
case 0:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_41, 0);
lean_inc(x_64);
lean_dec(x_41);
x_65 = lean_ctor_get(x_63, 0);
lean_inc(x_65);
lean_dec(x_63);
x_66 = l_Lean_Expr_bvar___override(x_65);
x_67 = l_Lean_Expr_app___override(x_64, x_66);
x_68 = lean_unbox(x_37);
x_69 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_68, x_38, x_67, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_67);
x_18 = x_69;
goto block_32;
}
case 1:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_70 = lean_ctor_get(x_41, 0);
lean_inc(x_70);
lean_dec(x_41);
x_71 = lean_ctor_get(x_63, 0);
lean_inc(x_71);
lean_dec(x_63);
x_72 = l_Lean_Expr_fvar___override(x_71);
x_73 = l_Lean_Expr_app___override(x_70, x_72);
x_74 = lean_unbox(x_37);
x_75 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_74, x_38, x_73, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_73);
x_18 = x_75;
goto block_32;
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_41, 0);
lean_inc(x_76);
lean_dec(x_41);
x_77 = lean_ctor_get(x_63, 0);
lean_inc(x_77);
lean_dec(x_63);
x_78 = l_Lean_Expr_mvar___override(x_77);
x_79 = l_Lean_Expr_app___override(x_76, x_78);
x_80 = lean_unbox(x_37);
x_81 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_80, x_38, x_79, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_79);
x_18 = x_81;
goto block_32;
}
case 3:
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_82 = lean_ctor_get(x_41, 0);
lean_inc(x_82);
lean_dec(x_41);
x_83 = lean_ctor_get(x_63, 0);
lean_inc(x_83);
lean_dec(x_63);
x_84 = l_Lean_Expr_sort___override(x_83);
x_85 = l_Lean_Expr_app___override(x_82, x_84);
x_86 = lean_unbox(x_37);
x_87 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_86, x_38, x_85, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_85);
x_18 = x_87;
goto block_32;
}
case 4:
{
lean_object* x_88; 
x_88 = lean_ctor_get(x_63, 1);
lean_inc(x_88);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; uint8_t x_96; 
x_89 = lean_ctor_get(x_41, 0);
lean_inc(x_89);
lean_dec(x_41);
x_90 = lean_ctor_get(x_63, 0);
lean_inc(x_90);
lean_dec(x_63);
x_91 = lean_box(0);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_38);
x_93 = lean_mk_string_unchecked("Unit", 4, 4);
x_94 = lean_mk_string_unchecked("unit", 4, 4);
x_95 = l_Lean_Name_mkStr2(x_93, x_94);
x_96 = lean_name_eq(x_90, x_95);
lean_dec(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_90, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_ctor_get(x_97, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_97)) {
 lean_ctor_release(x_97, 0);
 lean_ctor_release(x_97, 1);
 x_100 = x_97;
} else {
 lean_dec_ref(x_97);
 x_100 = lean_box(0);
}
if (lean_obj_tag(x_98) == 6)
{
uint8_t x_106; 
x_106 = !lean_is_exclusive(x_98);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_107 = lean_ctor_get(x_98, 0);
x_108 = lean_ctor_get(x_107, 2);
lean_inc(x_108);
lean_dec(x_107);
x_109 = lean_nat_dec_eq(x_108, x_6);
lean_dec(x_108);
if (x_109 == 0)
{
lean_free_object(x_98);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_105;
}
else
{
if (x_96 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; 
lean_dec(x_100);
x_110 = lean_unsigned_to_nat(1u);
x_111 = lean_array_get_size(x_2);
x_112 = lean_nat_sub(x_111, x_110);
lean_dec(x_111);
x_113 = lean_array_get(x_36, x_2, x_112);
lean_dec(x_112);
x_114 = lean_expr_eqv(x_89, x_113);
lean_dec(x_113);
lean_dec(x_89);
if (x_114 == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_115 = lean_box(x_96);
lean_ctor_set_tag(x_98, 1);
lean_ctor_set(x_98, 0, x_115);
x_116 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_116, 0, x_98);
lean_ctor_set(x_116, 1, x_38);
x_117 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_117, 0, x_116);
lean_ctor_set(x_117, 1, x_99);
return x_117;
}
else
{
lean_free_object(x_98);
x_12 = x_92;
x_13 = x_99;
goto block_17;
}
}
else
{
lean_free_object(x_98);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_105;
}
}
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_98, 0);
lean_inc(x_118);
lean_dec(x_98);
x_119 = lean_ctor_get(x_118, 2);
lean_inc(x_119);
lean_dec(x_118);
x_120 = lean_nat_dec_eq(x_119, x_6);
lean_dec(x_119);
if (x_120 == 0)
{
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_105;
}
else
{
if (x_96 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_dec(x_100);
x_121 = lean_unsigned_to_nat(1u);
x_122 = lean_array_get_size(x_2);
x_123 = lean_nat_sub(x_122, x_121);
lean_dec(x_122);
x_124 = lean_array_get(x_36, x_2, x_123);
lean_dec(x_123);
x_125 = lean_expr_eqv(x_89, x_124);
lean_dec(x_124);
lean_dec(x_89);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_126 = lean_box(x_96);
x_127 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_127, 0, x_126);
x_128 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_128, 0, x_127);
lean_ctor_set(x_128, 1, x_38);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_99);
return x_129;
}
else
{
x_12 = x_92;
x_13 = x_99;
goto block_17;
}
}
else
{
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
goto block_105;
}
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; 
lean_dec(x_100);
lean_dec(x_98);
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_130 = lean_box(x_96);
x_131 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_131);
lean_ctor_set(x_132, 1, x_38);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_99);
return x_133;
}
block_105:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_box(x_96);
x_102 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_38);
if (lean_is_scalar(x_100)) {
 x_104 = lean_alloc_ctor(0, 2, 0);
} else {
 x_104 = x_100;
}
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_99);
return x_104;
}
}
else
{
uint8_t x_134; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_134 = !lean_is_exclusive(x_97);
if (x_134 == 0)
{
return x_97;
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_135 = lean_ctor_get(x_97, 0);
x_136 = lean_ctor_get(x_97, 1);
lean_inc(x_136);
lean_inc(x_135);
lean_dec(x_97);
x_137 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
return x_137;
}
}
}
else
{
lean_object* x_138; 
lean_dec(x_90);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_89);
x_138 = lean_infer_type(x_89, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
if (lean_obj_tag(x_139) == 7)
{
uint8_t x_140; 
x_140 = !lean_is_exclusive(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_141 = lean_ctor_get(x_138, 1);
x_142 = lean_ctor_get(x_138, 0);
lean_dec(x_142);
x_143 = lean_ctor_get(x_139, 1);
lean_inc(x_143);
x_144 = lean_ctor_get(x_139, 2);
lean_inc(x_144);
lean_dec(x_139);
x_145 = l_Lean_Expr_hasLooseBVars(x_144);
if (x_145 == 0)
{
switch (lean_obj_tag(x_144)) {
case 0:
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_free_object(x_138);
lean_dec(x_89);
x_146 = lean_ctor_get(x_144, 0);
lean_inc(x_146);
lean_dec(x_144);
x_147 = l_Lean_Expr_bvar___override(x_146);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_143);
lean_ctor_set(x_148, 1, x_147);
x_149 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_149, 0, x_148);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_150 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_149, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_149);
x_18 = x_150;
goto block_32;
}
case 1:
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_free_object(x_138);
lean_dec(x_89);
x_151 = lean_ctor_get(x_144, 0);
lean_inc(x_151);
lean_dec(x_144);
x_152 = l_Lean_Expr_fvar___override(x_151);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_143);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_154, 0, x_153);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_155 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_154, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_154);
x_18 = x_155;
goto block_32;
}
case 2:
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_free_object(x_138);
lean_dec(x_89);
x_156 = lean_ctor_get(x_144, 0);
lean_inc(x_156);
lean_dec(x_144);
x_157 = l_Lean_Expr_mvar___override(x_156);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_143);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_159, 0, x_158);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_160 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_159, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_159);
x_18 = x_160;
goto block_32;
}
case 3:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; 
lean_free_object(x_138);
lean_dec(x_89);
x_161 = lean_ctor_get(x_144, 0);
lean_inc(x_161);
lean_dec(x_144);
x_162 = l_Lean_Expr_sort___override(x_161);
x_163 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_163, 0, x_143);
lean_ctor_set(x_163, 1, x_162);
x_164 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_164, 0, x_163);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_165 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_164, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_164);
x_18 = x_165;
goto block_32;
}
case 4:
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_free_object(x_138);
lean_dec(x_89);
x_166 = lean_ctor_get(x_144, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_144, 1);
lean_inc(x_167);
lean_dec(x_144);
x_168 = l_Lean_Expr_const___override(x_166, x_167);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_143);
lean_ctor_set(x_169, 1, x_168);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_171 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_170, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_170);
x_18 = x_171;
goto block_32;
}
case 5:
{
lean_object* x_172; 
x_172 = lean_ctor_get(x_144, 1);
lean_inc(x_172);
switch (lean_obj_tag(x_172)) {
case 0:
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; 
lean_free_object(x_138);
lean_dec(x_89);
x_173 = lean_ctor_get(x_144, 0);
lean_inc(x_173);
lean_dec(x_144);
x_174 = lean_ctor_get(x_172, 0);
lean_inc(x_174);
lean_dec(x_172);
x_175 = l_Lean_Expr_bvar___override(x_174);
x_176 = l_Lean_Expr_app___override(x_173, x_175);
x_177 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_177, 0, x_143);
lean_ctor_set(x_177, 1, x_176);
x_178 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_178, 0, x_177);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_179 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_178, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_178);
x_18 = x_179;
goto block_32;
}
case 1:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_free_object(x_138);
lean_dec(x_89);
x_180 = lean_ctor_get(x_144, 0);
lean_inc(x_180);
lean_dec(x_144);
x_181 = lean_ctor_get(x_172, 0);
lean_inc(x_181);
lean_dec(x_172);
x_182 = l_Lean_Expr_fvar___override(x_181);
x_183 = l_Lean_Expr_app___override(x_180, x_182);
x_184 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_184, 0, x_143);
lean_ctor_set(x_184, 1, x_183);
x_185 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_185, 0, x_184);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_186 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_185, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_185);
x_18 = x_186;
goto block_32;
}
case 2:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_138);
lean_dec(x_89);
x_187 = lean_ctor_get(x_144, 0);
lean_inc(x_187);
lean_dec(x_144);
x_188 = lean_ctor_get(x_172, 0);
lean_inc(x_188);
lean_dec(x_172);
x_189 = l_Lean_Expr_mvar___override(x_188);
x_190 = l_Lean_Expr_app___override(x_187, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_143);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_192, 0, x_191);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_193 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_192, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_192);
x_18 = x_193;
goto block_32;
}
case 3:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
lean_free_object(x_138);
lean_dec(x_89);
x_194 = lean_ctor_get(x_144, 0);
lean_inc(x_194);
lean_dec(x_144);
x_195 = lean_ctor_get(x_172, 0);
lean_inc(x_195);
lean_dec(x_172);
x_196 = l_Lean_Expr_sort___override(x_195);
x_197 = l_Lean_Expr_app___override(x_194, x_196);
x_198 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_198, 0, x_143);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_199, 0, x_198);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_200 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_199, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_199);
x_18 = x_200;
goto block_32;
}
case 4:
{
lean_object* x_201; 
x_201 = lean_ctor_get(x_172, 1);
lean_inc(x_201);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_dec(x_144);
lean_dec(x_143);
x_202 = lean_ctor_get(x_172, 0);
lean_inc(x_202);
lean_dec(x_172);
x_203 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_203, 0, x_202);
x_204 = lean_unsigned_to_nat(0u);
x_205 = l_Array_findIdx_x3f_loop___redArg(x_203, x_3, x_204);
if (lean_obj_tag(x_205) == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_free_object(x_138);
lean_dec(x_89);
x_206 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_207 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifyEnumWithDefault", 83, 83);
x_208 = lean_unsigned_to_nat(163u);
x_209 = lean_unsigned_to_nat(74u);
x_210 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_211 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_206, x_207, x_208, x_209, x_210);
lean_dec(x_210);
lean_dec(x_207);
lean_dec(x_206);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_212 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_211, x_7, x_8, x_9, x_10, x_141);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; 
x_213 = lean_ctor_get(x_212, 1);
lean_inc(x_213);
lean_dec(x_212);
x_12 = x_92;
x_13 = x_213;
goto block_17;
}
else
{
uint8_t x_214; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_214 = !lean_is_exclusive(x_212);
if (x_214 == 0)
{
return x_212;
}
else
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_212, 0);
x_216 = lean_ctor_get(x_212, 1);
lean_inc(x_216);
lean_inc(x_215);
lean_dec(x_212);
x_217 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
return x_217;
}
}
}
else
{
uint8_t x_218; 
x_218 = !lean_is_exclusive(x_205);
if (x_218 == 0)
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_219 = lean_ctor_get(x_205, 0);
x_220 = lean_nat_add(x_219, x_39);
lean_dec(x_219);
x_221 = lean_array_get(x_36, x_2, x_220);
lean_dec(x_220);
x_222 = lean_expr_eqv(x_89, x_221);
lean_dec(x_221);
lean_dec(x_89);
if (x_222 == 0)
{
if (x_96 == 0)
{
lean_free_object(x_205);
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
else
{
lean_object* x_223; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_ctor_set(x_205, 0, x_37);
x_223 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_223, 0, x_205);
lean_ctor_set(x_223, 1, x_38);
lean_ctor_set(x_138, 0, x_223);
return x_138;
}
}
else
{
lean_free_object(x_205);
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
}
else
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; 
x_224 = lean_ctor_get(x_205, 0);
lean_inc(x_224);
lean_dec(x_205);
x_225 = lean_nat_add(x_224, x_39);
lean_dec(x_224);
x_226 = lean_array_get(x_36, x_2, x_225);
lean_dec(x_225);
x_227 = lean_expr_eqv(x_89, x_226);
lean_dec(x_226);
lean_dec(x_89);
if (x_227 == 0)
{
if (x_96 == 0)
{
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
else
{
lean_object* x_228; lean_object* x_229; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_37);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_38);
lean_ctor_set(x_138, 0, x_229);
return x_138;
}
}
else
{
lean_free_object(x_138);
x_12 = x_92;
x_13 = x_141;
goto block_17;
}
}
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
lean_free_object(x_138);
lean_dec(x_89);
x_230 = lean_ctor_get(x_144, 0);
lean_inc(x_230);
lean_dec(x_144);
x_231 = lean_ctor_get(x_172, 0);
lean_inc(x_231);
lean_dec(x_172);
lean_inc(x_201);
x_232 = l_Lean_Expr_const___override(x_231, x_201);
x_233 = !lean_is_exclusive(x_201);
if (x_233 == 0)
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_234 = lean_ctor_get(x_201, 1);
lean_dec(x_234);
x_235 = lean_ctor_get(x_201, 0);
lean_dec(x_235);
x_236 = l_Lean_Expr_app___override(x_230, x_232);
lean_ctor_set_tag(x_201, 0);
lean_ctor_set(x_201, 1, x_236);
lean_ctor_set(x_201, 0, x_143);
x_237 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_237, 0, x_201);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_238 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_237, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_237);
x_18 = x_238;
goto block_32;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_dec(x_201);
x_239 = l_Lean_Expr_app___override(x_230, x_232);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_143);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_242 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_241, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_241);
x_18 = x_242;
goto block_32;
}
}
}
case 5:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_free_object(x_138);
lean_dec(x_89);
x_243 = lean_ctor_get(x_144, 0);
lean_inc(x_243);
lean_dec(x_144);
x_244 = lean_ctor_get(x_172, 0);
lean_inc(x_244);
x_245 = lean_ctor_get(x_172, 1);
lean_inc(x_245);
lean_dec(x_172);
x_246 = l_Lean_Expr_app___override(x_244, x_245);
x_247 = l_Lean_Expr_app___override(x_243, x_246);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_143);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_249, 0, x_248);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_250 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_249, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_249);
x_18 = x_250;
goto block_32;
}
case 6:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; uint8_t x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_free_object(x_138);
lean_dec(x_89);
x_251 = lean_ctor_get(x_144, 0);
lean_inc(x_251);
lean_dec(x_144);
x_252 = lean_ctor_get(x_172, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_172, 1);
lean_inc(x_253);
x_254 = lean_ctor_get(x_172, 2);
lean_inc(x_254);
x_255 = lean_ctor_get_uint8(x_172, sizeof(void*)*3 + 8);
lean_dec(x_172);
x_256 = l_Lean_Expr_lam___override(x_252, x_253, x_254, x_255);
x_257 = l_Lean_Expr_app___override(x_251, x_256);
x_258 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_258, 0, x_143);
lean_ctor_set(x_258, 1, x_257);
x_259 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_259, 0, x_258);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_260 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_259, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_259);
x_18 = x_260;
goto block_32;
}
case 7:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_free_object(x_138);
lean_dec(x_89);
x_261 = lean_ctor_get(x_144, 0);
lean_inc(x_261);
lean_dec(x_144);
x_262 = lean_ctor_get(x_172, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_172, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_172, 2);
lean_inc(x_264);
x_265 = lean_ctor_get_uint8(x_172, sizeof(void*)*3 + 8);
lean_dec(x_172);
x_266 = l_Lean_Expr_forallE___override(x_262, x_263, x_264, x_265);
x_267 = l_Lean_Expr_app___override(x_261, x_266);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_143);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_269, 0, x_268);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_270 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_269, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_269);
x_18 = x_270;
goto block_32;
}
case 8:
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; 
lean_free_object(x_138);
lean_dec(x_89);
x_271 = lean_ctor_get(x_144, 0);
lean_inc(x_271);
lean_dec(x_144);
x_272 = lean_ctor_get(x_172, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_172, 1);
lean_inc(x_273);
x_274 = lean_ctor_get(x_172, 2);
lean_inc(x_274);
x_275 = lean_ctor_get(x_172, 3);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_172, sizeof(void*)*4 + 8);
lean_dec(x_172);
x_277 = l_Lean_Expr_letE___override(x_272, x_273, x_274, x_275, x_276);
x_278 = l_Lean_Expr_app___override(x_271, x_277);
x_279 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_279, 0, x_143);
lean_ctor_set(x_279, 1, x_278);
x_280 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_280, 0, x_279);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_281 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_280, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_280);
x_18 = x_281;
goto block_32;
}
case 9:
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
lean_free_object(x_138);
lean_dec(x_89);
x_282 = lean_ctor_get(x_144, 0);
lean_inc(x_282);
lean_dec(x_144);
x_283 = lean_ctor_get(x_172, 0);
lean_inc(x_283);
lean_dec(x_172);
x_284 = l_Lean_Expr_lit___override(x_283);
x_285 = l_Lean_Expr_app___override(x_282, x_284);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_143);
lean_ctor_set(x_286, 1, x_285);
x_287 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_287, 0, x_286);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_288 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_287, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_287);
x_18 = x_288;
goto block_32;
}
case 10:
{
lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_free_object(x_138);
lean_dec(x_89);
x_289 = lean_ctor_get(x_144, 0);
lean_inc(x_289);
lean_dec(x_144);
x_290 = lean_ctor_get(x_172, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_172, 1);
lean_inc(x_291);
lean_dec(x_172);
x_292 = l_Lean_Expr_mdata___override(x_290, x_291);
x_293 = l_Lean_Expr_app___override(x_289, x_292);
x_294 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_294, 0, x_143);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_295, 0, x_294);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_296 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_295, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_295);
x_18 = x_296;
goto block_32;
}
default: 
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; 
lean_free_object(x_138);
lean_dec(x_89);
x_297 = lean_ctor_get(x_144, 0);
lean_inc(x_297);
lean_dec(x_144);
x_298 = lean_ctor_get(x_172, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_172, 1);
lean_inc(x_299);
x_300 = lean_ctor_get(x_172, 2);
lean_inc(x_300);
lean_dec(x_172);
x_301 = l_Lean_Expr_proj___override(x_298, x_299, x_300);
x_302 = l_Lean_Expr_app___override(x_297, x_301);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_143);
lean_ctor_set(x_303, 1, x_302);
x_304 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_304, 0, x_303);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_305 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_304, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_304);
x_18 = x_305;
goto block_32;
}
}
}
case 6:
{
lean_object* x_306; lean_object* x_307; lean_object* x_308; uint8_t x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; 
lean_free_object(x_138);
lean_dec(x_89);
x_306 = lean_ctor_get(x_144, 0);
lean_inc(x_306);
x_307 = lean_ctor_get(x_144, 1);
lean_inc(x_307);
x_308 = lean_ctor_get(x_144, 2);
lean_inc(x_308);
x_309 = lean_ctor_get_uint8(x_144, sizeof(void*)*3 + 8);
lean_dec(x_144);
x_310 = l_Lean_Expr_lam___override(x_306, x_307, x_308, x_309);
x_311 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_311, 0, x_143);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_312, 0, x_311);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_313 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_312, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_312);
x_18 = x_313;
goto block_32;
}
case 7:
{
lean_object* x_314; lean_object* x_315; lean_object* x_316; uint8_t x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; 
lean_free_object(x_138);
lean_dec(x_89);
x_314 = lean_ctor_get(x_144, 0);
lean_inc(x_314);
x_315 = lean_ctor_get(x_144, 1);
lean_inc(x_315);
x_316 = lean_ctor_get(x_144, 2);
lean_inc(x_316);
x_317 = lean_ctor_get_uint8(x_144, sizeof(void*)*3 + 8);
lean_dec(x_144);
x_318 = l_Lean_Expr_forallE___override(x_314, x_315, x_316, x_317);
x_319 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_319, 0, x_143);
lean_ctor_set(x_319, 1, x_318);
x_320 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_320, 0, x_319);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_321 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_320, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_320);
x_18 = x_321;
goto block_32;
}
case 8:
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; uint8_t x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_free_object(x_138);
lean_dec(x_89);
x_322 = lean_ctor_get(x_144, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_144, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_144, 2);
lean_inc(x_324);
x_325 = lean_ctor_get(x_144, 3);
lean_inc(x_325);
x_326 = lean_ctor_get_uint8(x_144, sizeof(void*)*4 + 8);
lean_dec(x_144);
x_327 = l_Lean_Expr_letE___override(x_322, x_323, x_324, x_325, x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_143);
lean_ctor_set(x_328, 1, x_327);
x_329 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_329, 0, x_328);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_330 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_329, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_329);
x_18 = x_330;
goto block_32;
}
case 9:
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_free_object(x_138);
lean_dec(x_89);
x_331 = lean_ctor_get(x_144, 0);
lean_inc(x_331);
lean_dec(x_144);
x_332 = l_Lean_Expr_lit___override(x_331);
x_333 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_333, 0, x_143);
lean_ctor_set(x_333, 1, x_332);
x_334 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_334, 0, x_333);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_335 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_334, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_334);
x_18 = x_335;
goto block_32;
}
case 10:
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_free_object(x_138);
lean_dec(x_89);
x_336 = lean_ctor_get(x_144, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_144, 1);
lean_inc(x_337);
lean_dec(x_144);
x_338 = l_Lean_Expr_mdata___override(x_336, x_337);
x_339 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_339, 0, x_143);
lean_ctor_set(x_339, 1, x_338);
x_340 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_340, 0, x_339);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_341 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_340, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_340);
x_18 = x_341;
goto block_32;
}
default: 
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_free_object(x_138);
lean_dec(x_89);
x_342 = lean_ctor_get(x_144, 0);
lean_inc(x_342);
x_343 = lean_ctor_get(x_144, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_144, 2);
lean_inc(x_344);
lean_dec(x_144);
x_345 = l_Lean_Expr_proj___override(x_342, x_343, x_344);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_143);
lean_ctor_set(x_346, 1, x_345);
x_347 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_347, 0, x_346);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_348 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_347, x_7, x_8, x_9, x_10, x_141);
lean_dec(x_347);
x_18 = x_348;
goto block_32;
}
}
}
else
{
lean_object* x_349; lean_object* x_350; 
lean_dec(x_144);
lean_dec(x_143);
lean_free_object(x_138);
lean_dec(x_89);
x_349 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_350 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_349, x_7, x_8, x_9, x_10, x_141);
x_18 = x_350;
goto block_32;
}
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_351 = lean_ctor_get(x_138, 1);
lean_inc(x_351);
lean_dec(x_138);
x_352 = lean_ctor_get(x_139, 1);
lean_inc(x_352);
x_353 = lean_ctor_get(x_139, 2);
lean_inc(x_353);
lean_dec(x_139);
x_354 = l_Lean_Expr_hasLooseBVars(x_353);
if (x_354 == 0)
{
switch (lean_obj_tag(x_353)) {
case 0:
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_89);
x_355 = lean_ctor_get(x_353, 0);
lean_inc(x_355);
lean_dec(x_353);
x_356 = l_Lean_Expr_bvar___override(x_355);
x_357 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_357, 0, x_352);
lean_ctor_set(x_357, 1, x_356);
x_358 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_358, 0, x_357);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_359 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_358, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_358);
x_18 = x_359;
goto block_32;
}
case 1:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; 
lean_dec(x_89);
x_360 = lean_ctor_get(x_353, 0);
lean_inc(x_360);
lean_dec(x_353);
x_361 = l_Lean_Expr_fvar___override(x_360);
x_362 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_362, 0, x_352);
lean_ctor_set(x_362, 1, x_361);
x_363 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_363, 0, x_362);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_364 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_363, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_363);
x_18 = x_364;
goto block_32;
}
case 2:
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_89);
x_365 = lean_ctor_get(x_353, 0);
lean_inc(x_365);
lean_dec(x_353);
x_366 = l_Lean_Expr_mvar___override(x_365);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_352);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_368, 0, x_367);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_369 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_368, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_368);
x_18 = x_369;
goto block_32;
}
case 3:
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; 
lean_dec(x_89);
x_370 = lean_ctor_get(x_353, 0);
lean_inc(x_370);
lean_dec(x_353);
x_371 = l_Lean_Expr_sort___override(x_370);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_352);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_373, 0, x_372);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_374 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_373, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_373);
x_18 = x_374;
goto block_32;
}
case 4:
{
lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
lean_dec(x_89);
x_375 = lean_ctor_get(x_353, 0);
lean_inc(x_375);
x_376 = lean_ctor_get(x_353, 1);
lean_inc(x_376);
lean_dec(x_353);
x_377 = l_Lean_Expr_const___override(x_375, x_376);
x_378 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_378, 0, x_352);
lean_ctor_set(x_378, 1, x_377);
x_379 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_379, 0, x_378);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_380 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_379, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_379);
x_18 = x_380;
goto block_32;
}
case 5:
{
lean_object* x_381; 
x_381 = lean_ctor_get(x_353, 1);
lean_inc(x_381);
switch (lean_obj_tag(x_381)) {
case 0:
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; 
lean_dec(x_89);
x_382 = lean_ctor_get(x_353, 0);
lean_inc(x_382);
lean_dec(x_353);
x_383 = lean_ctor_get(x_381, 0);
lean_inc(x_383);
lean_dec(x_381);
x_384 = l_Lean_Expr_bvar___override(x_383);
x_385 = l_Lean_Expr_app___override(x_382, x_384);
x_386 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_386, 0, x_352);
lean_ctor_set(x_386, 1, x_385);
x_387 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_387, 0, x_386);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_388 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_387, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_387);
x_18 = x_388;
goto block_32;
}
case 1:
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_89);
x_389 = lean_ctor_get(x_353, 0);
lean_inc(x_389);
lean_dec(x_353);
x_390 = lean_ctor_get(x_381, 0);
lean_inc(x_390);
lean_dec(x_381);
x_391 = l_Lean_Expr_fvar___override(x_390);
x_392 = l_Lean_Expr_app___override(x_389, x_391);
x_393 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_393, 0, x_352);
lean_ctor_set(x_393, 1, x_392);
x_394 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_394, 0, x_393);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_395 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_394, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_394);
x_18 = x_395;
goto block_32;
}
case 2:
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_89);
x_396 = lean_ctor_get(x_353, 0);
lean_inc(x_396);
lean_dec(x_353);
x_397 = lean_ctor_get(x_381, 0);
lean_inc(x_397);
lean_dec(x_381);
x_398 = l_Lean_Expr_mvar___override(x_397);
x_399 = l_Lean_Expr_app___override(x_396, x_398);
x_400 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_400, 0, x_352);
lean_ctor_set(x_400, 1, x_399);
x_401 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_401, 0, x_400);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_402 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_401, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_401);
x_18 = x_402;
goto block_32;
}
case 3:
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; 
lean_dec(x_89);
x_403 = lean_ctor_get(x_353, 0);
lean_inc(x_403);
lean_dec(x_353);
x_404 = lean_ctor_get(x_381, 0);
lean_inc(x_404);
lean_dec(x_381);
x_405 = l_Lean_Expr_sort___override(x_404);
x_406 = l_Lean_Expr_app___override(x_403, x_405);
x_407 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_407, 0, x_352);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_408, 0, x_407);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_409 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_408, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_408);
x_18 = x_409;
goto block_32;
}
case 4:
{
lean_object* x_410; 
x_410 = lean_ctor_get(x_381, 1);
lean_inc(x_410);
if (lean_obj_tag(x_410) == 0)
{
lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; 
lean_dec(x_353);
lean_dec(x_352);
x_411 = lean_ctor_get(x_381, 0);
lean_inc(x_411);
lean_dec(x_381);
x_412 = lean_alloc_closure((void*)(l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_412, 0, x_411);
x_413 = lean_unsigned_to_nat(0u);
x_414 = l_Array_findIdx_x3f_loop___redArg(x_412, x_3, x_413);
if (lean_obj_tag(x_414) == 0)
{
lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
lean_dec(x_89);
x_415 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_416 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch.verifyEnumWithDefault", 83, 83);
x_417 = lean_unsigned_to_nat(163u);
x_418 = lean_unsigned_to_nat(74u);
x_419 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_420 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_415, x_416, x_417, x_418, x_419);
lean_dec(x_419);
lean_dec(x_416);
lean_dec(x_415);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_421 = l_panic___at___Lean_Meta_congrArg_x3f_spec__0(x_420, x_7, x_8, x_9, x_10, x_351);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; 
x_422 = lean_ctor_get(x_421, 1);
lean_inc(x_422);
lean_dec(x_421);
x_12 = x_92;
x_13 = x_422;
goto block_17;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_423 = lean_ctor_get(x_421, 0);
lean_inc(x_423);
x_424 = lean_ctor_get(x_421, 1);
lean_inc(x_424);
if (lean_is_exclusive(x_421)) {
 lean_ctor_release(x_421, 0);
 lean_ctor_release(x_421, 1);
 x_425 = x_421;
} else {
 lean_dec_ref(x_421);
 x_425 = lean_box(0);
}
if (lean_is_scalar(x_425)) {
 x_426 = lean_alloc_ctor(1, 2, 0);
} else {
 x_426 = x_425;
}
lean_ctor_set(x_426, 0, x_423);
lean_ctor_set(x_426, 1, x_424);
return x_426;
}
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; uint8_t x_431; 
x_427 = lean_ctor_get(x_414, 0);
lean_inc(x_427);
if (lean_is_exclusive(x_414)) {
 lean_ctor_release(x_414, 0);
 x_428 = x_414;
} else {
 lean_dec_ref(x_414);
 x_428 = lean_box(0);
}
x_429 = lean_nat_add(x_427, x_39);
lean_dec(x_427);
x_430 = lean_array_get(x_36, x_2, x_429);
lean_dec(x_429);
x_431 = lean_expr_eqv(x_89, x_430);
lean_dec(x_430);
lean_dec(x_89);
if (x_431 == 0)
{
if (x_96 == 0)
{
lean_dec(x_428);
x_12 = x_92;
x_13 = x_351;
goto block_17;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; 
lean_dec(x_92);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
if (lean_is_scalar(x_428)) {
 x_432 = lean_alloc_ctor(1, 1, 0);
} else {
 x_432 = x_428;
}
lean_ctor_set(x_432, 0, x_37);
x_433 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_433, 0, x_432);
lean_ctor_set(x_433, 1, x_38);
x_434 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_434, 0, x_433);
lean_ctor_set(x_434, 1, x_351);
return x_434;
}
}
else
{
lean_dec(x_428);
x_12 = x_92;
x_13 = x_351;
goto block_17;
}
}
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_89);
x_435 = lean_ctor_get(x_353, 0);
lean_inc(x_435);
lean_dec(x_353);
x_436 = lean_ctor_get(x_381, 0);
lean_inc(x_436);
lean_dec(x_381);
lean_inc(x_410);
x_437 = l_Lean_Expr_const___override(x_436, x_410);
if (lean_is_exclusive(x_410)) {
 lean_ctor_release(x_410, 0);
 lean_ctor_release(x_410, 1);
 x_438 = x_410;
} else {
 lean_dec_ref(x_410);
 x_438 = lean_box(0);
}
x_439 = l_Lean_Expr_app___override(x_435, x_437);
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_438;
 lean_ctor_set_tag(x_440, 0);
}
lean_ctor_set(x_440, 0, x_352);
lean_ctor_set(x_440, 1, x_439);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_440);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_442 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_441, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_441);
x_18 = x_442;
goto block_32;
}
}
case 5:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_89);
x_443 = lean_ctor_get(x_353, 0);
lean_inc(x_443);
lean_dec(x_353);
x_444 = lean_ctor_get(x_381, 0);
lean_inc(x_444);
x_445 = lean_ctor_get(x_381, 1);
lean_inc(x_445);
lean_dec(x_381);
x_446 = l_Lean_Expr_app___override(x_444, x_445);
x_447 = l_Lean_Expr_app___override(x_443, x_446);
x_448 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_448, 0, x_352);
lean_ctor_set(x_448, 1, x_447);
x_449 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_449, 0, x_448);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_450 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_449, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_449);
x_18 = x_450;
goto block_32;
}
case 6:
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; uint8_t x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; 
lean_dec(x_89);
x_451 = lean_ctor_get(x_353, 0);
lean_inc(x_451);
lean_dec(x_353);
x_452 = lean_ctor_get(x_381, 0);
lean_inc(x_452);
x_453 = lean_ctor_get(x_381, 1);
lean_inc(x_453);
x_454 = lean_ctor_get(x_381, 2);
lean_inc(x_454);
x_455 = lean_ctor_get_uint8(x_381, sizeof(void*)*3 + 8);
lean_dec(x_381);
x_456 = l_Lean_Expr_lam___override(x_452, x_453, x_454, x_455);
x_457 = l_Lean_Expr_app___override(x_451, x_456);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_352);
lean_ctor_set(x_458, 1, x_457);
x_459 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_459, 0, x_458);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_460 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_459, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_459);
x_18 = x_460;
goto block_32;
}
case 7:
{
lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; uint8_t x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; 
lean_dec(x_89);
x_461 = lean_ctor_get(x_353, 0);
lean_inc(x_461);
lean_dec(x_353);
x_462 = lean_ctor_get(x_381, 0);
lean_inc(x_462);
x_463 = lean_ctor_get(x_381, 1);
lean_inc(x_463);
x_464 = lean_ctor_get(x_381, 2);
lean_inc(x_464);
x_465 = lean_ctor_get_uint8(x_381, sizeof(void*)*3 + 8);
lean_dec(x_381);
x_466 = l_Lean_Expr_forallE___override(x_462, x_463, x_464, x_465);
x_467 = l_Lean_Expr_app___override(x_461, x_466);
x_468 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_468, 0, x_352);
lean_ctor_set(x_468, 1, x_467);
x_469 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_469, 0, x_468);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_470 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_469, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_469);
x_18 = x_470;
goto block_32;
}
case 8:
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; uint8_t x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_dec(x_89);
x_471 = lean_ctor_get(x_353, 0);
lean_inc(x_471);
lean_dec(x_353);
x_472 = lean_ctor_get(x_381, 0);
lean_inc(x_472);
x_473 = lean_ctor_get(x_381, 1);
lean_inc(x_473);
x_474 = lean_ctor_get(x_381, 2);
lean_inc(x_474);
x_475 = lean_ctor_get(x_381, 3);
lean_inc(x_475);
x_476 = lean_ctor_get_uint8(x_381, sizeof(void*)*4 + 8);
lean_dec(x_381);
x_477 = l_Lean_Expr_letE___override(x_472, x_473, x_474, x_475, x_476);
x_478 = l_Lean_Expr_app___override(x_471, x_477);
x_479 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_479, 0, x_352);
lean_ctor_set(x_479, 1, x_478);
x_480 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_480, 0, x_479);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_481 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_480, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_480);
x_18 = x_481;
goto block_32;
}
case 9:
{
lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
lean_dec(x_89);
x_482 = lean_ctor_get(x_353, 0);
lean_inc(x_482);
lean_dec(x_353);
x_483 = lean_ctor_get(x_381, 0);
lean_inc(x_483);
lean_dec(x_381);
x_484 = l_Lean_Expr_lit___override(x_483);
x_485 = l_Lean_Expr_app___override(x_482, x_484);
x_486 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_486, 0, x_352);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_487, 0, x_486);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_488 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_487, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_487);
x_18 = x_488;
goto block_32;
}
case 10:
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_89);
x_489 = lean_ctor_get(x_353, 0);
lean_inc(x_489);
lean_dec(x_353);
x_490 = lean_ctor_get(x_381, 0);
lean_inc(x_490);
x_491 = lean_ctor_get(x_381, 1);
lean_inc(x_491);
lean_dec(x_381);
x_492 = l_Lean_Expr_mdata___override(x_490, x_491);
x_493 = l_Lean_Expr_app___override(x_489, x_492);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_352);
lean_ctor_set(x_494, 1, x_493);
x_495 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_495, 0, x_494);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_496 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_495, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_495);
x_18 = x_496;
goto block_32;
}
default: 
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; 
lean_dec(x_89);
x_497 = lean_ctor_get(x_353, 0);
lean_inc(x_497);
lean_dec(x_353);
x_498 = lean_ctor_get(x_381, 0);
lean_inc(x_498);
x_499 = lean_ctor_get(x_381, 1);
lean_inc(x_499);
x_500 = lean_ctor_get(x_381, 2);
lean_inc(x_500);
lean_dec(x_381);
x_501 = l_Lean_Expr_proj___override(x_498, x_499, x_500);
x_502 = l_Lean_Expr_app___override(x_497, x_501);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_352);
lean_ctor_set(x_503, 1, x_502);
x_504 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_504, 0, x_503);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_505 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_504, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_504);
x_18 = x_505;
goto block_32;
}
}
}
case 6:
{
lean_object* x_506; lean_object* x_507; lean_object* x_508; uint8_t x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_89);
x_506 = lean_ctor_get(x_353, 0);
lean_inc(x_506);
x_507 = lean_ctor_get(x_353, 1);
lean_inc(x_507);
x_508 = lean_ctor_get(x_353, 2);
lean_inc(x_508);
x_509 = lean_ctor_get_uint8(x_353, sizeof(void*)*3 + 8);
lean_dec(x_353);
x_510 = l_Lean_Expr_lam___override(x_506, x_507, x_508, x_509);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_352);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_512, 0, x_511);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_513 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_512, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_512);
x_18 = x_513;
goto block_32;
}
case 7:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; uint8_t x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_89);
x_514 = lean_ctor_get(x_353, 0);
lean_inc(x_514);
x_515 = lean_ctor_get(x_353, 1);
lean_inc(x_515);
x_516 = lean_ctor_get(x_353, 2);
lean_inc(x_516);
x_517 = lean_ctor_get_uint8(x_353, sizeof(void*)*3 + 8);
lean_dec(x_353);
x_518 = l_Lean_Expr_forallE___override(x_514, x_515, x_516, x_517);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_352);
lean_ctor_set(x_519, 1, x_518);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_519);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_521 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_520, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_520);
x_18 = x_521;
goto block_32;
}
case 8:
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; uint8_t x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_89);
x_522 = lean_ctor_get(x_353, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_353, 1);
lean_inc(x_523);
x_524 = lean_ctor_get(x_353, 2);
lean_inc(x_524);
x_525 = lean_ctor_get(x_353, 3);
lean_inc(x_525);
x_526 = lean_ctor_get_uint8(x_353, sizeof(void*)*4 + 8);
lean_dec(x_353);
x_527 = l_Lean_Expr_letE___override(x_522, x_523, x_524, x_525, x_526);
x_528 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_528, 0, x_352);
lean_ctor_set(x_528, 1, x_527);
x_529 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_529, 0, x_528);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_530 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_529, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_529);
x_18 = x_530;
goto block_32;
}
case 9:
{
lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; 
lean_dec(x_89);
x_531 = lean_ctor_get(x_353, 0);
lean_inc(x_531);
lean_dec(x_353);
x_532 = l_Lean_Expr_lit___override(x_531);
x_533 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_533, 0, x_352);
lean_ctor_set(x_533, 1, x_532);
x_534 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_534, 0, x_533);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_535 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_534, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_534);
x_18 = x_535;
goto block_32;
}
case 10:
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; 
lean_dec(x_89);
x_536 = lean_ctor_get(x_353, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_353, 1);
lean_inc(x_537);
lean_dec(x_353);
x_538 = l_Lean_Expr_mdata___override(x_536, x_537);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_352);
lean_ctor_set(x_539, 1, x_538);
x_540 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_540, 0, x_539);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_541 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_540, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_540);
x_18 = x_541;
goto block_32;
}
default: 
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_dec(x_89);
x_542 = lean_ctor_get(x_353, 0);
lean_inc(x_542);
x_543 = lean_ctor_get(x_353, 1);
lean_inc(x_543);
x_544 = lean_ctor_get(x_353, 2);
lean_inc(x_544);
lean_dec(x_353);
x_545 = l_Lean_Expr_proj___override(x_542, x_543, x_544);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_352);
lean_ctor_set(x_546, 1, x_545);
x_547 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_547, 0, x_546);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_548 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_547, x_7, x_8, x_9, x_10, x_351);
lean_dec(x_547);
x_18 = x_548;
goto block_32;
}
}
}
else
{
lean_object* x_549; lean_object* x_550; 
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_89);
x_549 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_550 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_549, x_7, x_8, x_9, x_10, x_351);
x_18 = x_550;
goto block_32;
}
}
}
else
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; 
lean_dec(x_139);
lean_dec(x_89);
x_551 = lean_ctor_get(x_138, 1);
lean_inc(x_551);
lean_dec(x_138);
x_552 = lean_box(0);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_553 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_92, x_552, x_7, x_8, x_9, x_10, x_551);
x_18 = x_553;
goto block_32;
}
}
else
{
uint8_t x_554; 
lean_dec(x_92);
lean_dec(x_89);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_554 = !lean_is_exclusive(x_138);
if (x_554 == 0)
{
return x_138;
}
else
{
lean_object* x_555; lean_object* x_556; lean_object* x_557; 
x_555 = lean_ctor_get(x_138, 0);
x_556 = lean_ctor_get(x_138, 1);
lean_inc(x_556);
lean_inc(x_555);
lean_dec(x_138);
x_557 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_557, 0, x_555);
lean_ctor_set(x_557, 1, x_556);
return x_557;
}
}
}
}
else
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; lean_object* x_563; 
x_558 = lean_ctor_get(x_41, 0);
lean_inc(x_558);
lean_dec(x_41);
x_559 = lean_ctor_get(x_63, 0);
lean_inc(x_559);
lean_dec(x_63);
x_560 = l_Lean_Expr_const___override(x_559, x_88);
x_561 = l_Lean_Expr_app___override(x_558, x_560);
x_562 = lean_unbox(x_37);
x_563 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_562, x_38, x_561, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_561);
x_18 = x_563;
goto block_32;
}
}
case 5:
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; lean_object* x_570; 
x_564 = lean_ctor_get(x_41, 0);
lean_inc(x_564);
lean_dec(x_41);
x_565 = lean_ctor_get(x_63, 0);
lean_inc(x_565);
x_566 = lean_ctor_get(x_63, 1);
lean_inc(x_566);
lean_dec(x_63);
x_567 = l_Lean_Expr_app___override(x_565, x_566);
x_568 = l_Lean_Expr_app___override(x_564, x_567);
x_569 = lean_unbox(x_37);
x_570 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_569, x_38, x_568, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_568);
x_18 = x_570;
goto block_32;
}
case 6:
{
lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; uint8_t x_575; lean_object* x_576; lean_object* x_577; uint8_t x_578; lean_object* x_579; 
x_571 = lean_ctor_get(x_41, 0);
lean_inc(x_571);
lean_dec(x_41);
x_572 = lean_ctor_get(x_63, 0);
lean_inc(x_572);
x_573 = lean_ctor_get(x_63, 1);
lean_inc(x_573);
x_574 = lean_ctor_get(x_63, 2);
lean_inc(x_574);
x_575 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_dec(x_63);
x_576 = l_Lean_Expr_lam___override(x_572, x_573, x_574, x_575);
x_577 = l_Lean_Expr_app___override(x_571, x_576);
x_578 = lean_unbox(x_37);
x_579 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_578, x_38, x_577, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_577);
x_18 = x_579;
goto block_32;
}
case 7:
{
lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; lean_object* x_586; uint8_t x_587; lean_object* x_588; 
x_580 = lean_ctor_get(x_41, 0);
lean_inc(x_580);
lean_dec(x_41);
x_581 = lean_ctor_get(x_63, 0);
lean_inc(x_581);
x_582 = lean_ctor_get(x_63, 1);
lean_inc(x_582);
x_583 = lean_ctor_get(x_63, 2);
lean_inc(x_583);
x_584 = lean_ctor_get_uint8(x_63, sizeof(void*)*3 + 8);
lean_dec(x_63);
x_585 = l_Lean_Expr_forallE___override(x_581, x_582, x_583, x_584);
x_586 = l_Lean_Expr_app___override(x_580, x_585);
x_587 = lean_unbox(x_37);
x_588 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_587, x_38, x_586, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_586);
x_18 = x_588;
goto block_32;
}
case 8:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; uint8_t x_594; lean_object* x_595; lean_object* x_596; uint8_t x_597; lean_object* x_598; 
x_589 = lean_ctor_get(x_41, 0);
lean_inc(x_589);
lean_dec(x_41);
x_590 = lean_ctor_get(x_63, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_63, 1);
lean_inc(x_591);
x_592 = lean_ctor_get(x_63, 2);
lean_inc(x_592);
x_593 = lean_ctor_get(x_63, 3);
lean_inc(x_593);
x_594 = lean_ctor_get_uint8(x_63, sizeof(void*)*4 + 8);
lean_dec(x_63);
x_595 = l_Lean_Expr_letE___override(x_590, x_591, x_592, x_593, x_594);
x_596 = l_Lean_Expr_app___override(x_589, x_595);
x_597 = lean_unbox(x_37);
x_598 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_597, x_38, x_596, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_596);
x_18 = x_598;
goto block_32;
}
case 9:
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; uint8_t x_603; lean_object* x_604; 
x_599 = lean_ctor_get(x_41, 0);
lean_inc(x_599);
lean_dec(x_41);
x_600 = lean_ctor_get(x_63, 0);
lean_inc(x_600);
lean_dec(x_63);
x_601 = l_Lean_Expr_lit___override(x_600);
x_602 = l_Lean_Expr_app___override(x_599, x_601);
x_603 = lean_unbox(x_37);
x_604 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_603, x_38, x_602, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_602);
x_18 = x_604;
goto block_32;
}
case 10:
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; uint8_t x_610; lean_object* x_611; 
x_605 = lean_ctor_get(x_41, 0);
lean_inc(x_605);
lean_dec(x_41);
x_606 = lean_ctor_get(x_63, 0);
lean_inc(x_606);
x_607 = lean_ctor_get(x_63, 1);
lean_inc(x_607);
lean_dec(x_63);
x_608 = l_Lean_Expr_mdata___override(x_606, x_607);
x_609 = l_Lean_Expr_app___override(x_605, x_608);
x_610 = lean_unbox(x_37);
x_611 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_610, x_38, x_609, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_609);
x_18 = x_611;
goto block_32;
}
default: 
{
lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; lean_object* x_619; 
x_612 = lean_ctor_get(x_41, 0);
lean_inc(x_612);
lean_dec(x_41);
x_613 = lean_ctor_get(x_63, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_63, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_63, 2);
lean_inc(x_615);
lean_dec(x_63);
x_616 = l_Lean_Expr_proj___override(x_613, x_614, x_615);
x_617 = l_Lean_Expr_app___override(x_612, x_616);
x_618 = lean_unbox(x_37);
x_619 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_618, x_38, x_617, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_617);
x_18 = x_619;
goto block_32;
}
}
}
case 6:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; uint8_t x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; 
x_620 = lean_ctor_get(x_41, 0);
lean_inc(x_620);
x_621 = lean_ctor_get(x_41, 1);
lean_inc(x_621);
x_622 = lean_ctor_get(x_41, 2);
lean_inc(x_622);
x_623 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_624 = l_Lean_Expr_lam___override(x_620, x_621, x_622, x_623);
x_625 = lean_unbox(x_37);
x_626 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_625, x_38, x_624, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_624);
x_18 = x_626;
goto block_32;
}
case 7:
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; uint8_t x_630; lean_object* x_631; uint8_t x_632; lean_object* x_633; 
x_627 = lean_ctor_get(x_41, 0);
lean_inc(x_627);
x_628 = lean_ctor_get(x_41, 1);
lean_inc(x_628);
x_629 = lean_ctor_get(x_41, 2);
lean_inc(x_629);
x_630 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_631 = l_Lean_Expr_forallE___override(x_627, x_628, x_629, x_630);
x_632 = lean_unbox(x_37);
x_633 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_632, x_38, x_631, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_631);
x_18 = x_633;
goto block_32;
}
case 8:
{
lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; uint8_t x_638; lean_object* x_639; uint8_t x_640; lean_object* x_641; 
x_634 = lean_ctor_get(x_41, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_41, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_41, 2);
lean_inc(x_636);
x_637 = lean_ctor_get(x_41, 3);
lean_inc(x_637);
x_638 = lean_ctor_get_uint8(x_41, sizeof(void*)*4 + 8);
lean_dec(x_41);
x_639 = l_Lean_Expr_letE___override(x_634, x_635, x_636, x_637, x_638);
x_640 = lean_unbox(x_37);
x_641 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_640, x_38, x_639, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_639);
x_18 = x_641;
goto block_32;
}
case 9:
{
lean_object* x_642; lean_object* x_643; uint8_t x_644; lean_object* x_645; 
x_642 = lean_ctor_get(x_41, 0);
lean_inc(x_642);
lean_dec(x_41);
x_643 = l_Lean_Expr_lit___override(x_642);
x_644 = lean_unbox(x_37);
x_645 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_644, x_38, x_643, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_643);
x_18 = x_645;
goto block_32;
}
case 10:
{
lean_object* x_646; lean_object* x_647; lean_object* x_648; uint8_t x_649; lean_object* x_650; 
x_646 = lean_ctor_get(x_41, 0);
lean_inc(x_646);
x_647 = lean_ctor_get(x_41, 1);
lean_inc(x_647);
lean_dec(x_41);
x_648 = l_Lean_Expr_mdata___override(x_646, x_647);
x_649 = lean_unbox(x_37);
x_650 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_649, x_38, x_648, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_648);
x_18 = x_650;
goto block_32;
}
default: 
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; uint8_t x_655; lean_object* x_656; 
x_651 = lean_ctor_get(x_41, 0);
lean_inc(x_651);
x_652 = lean_ctor_get(x_41, 1);
lean_inc(x_652);
x_653 = lean_ctor_get(x_41, 2);
lean_inc(x_653);
lean_dec(x_41);
x_654 = l_Lean_Expr_proj___override(x_651, x_652, x_653);
x_655 = lean_unbox(x_37);
x_656 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleEnum_spec__0___redArg___lam__0(x_655, x_38, x_654, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_654);
x_18 = x_656;
goto block_32;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_4, 2);
x_15 = lean_nat_add(x_6, x_14);
x_16 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_12, x_15, x_7, x_8, x_9, x_10, x_13);
return x_16;
}
block_32:
{
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_20 = !lean_is_exclusive(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_19, 0);
lean_inc(x_22);
lean_dec(x_19);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_18, 1);
lean_inc(x_23);
lean_dec(x_18);
x_24 = lean_ctor_get(x_19, 0);
lean_inc(x_24);
lean_dec(x_19);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_18, 1);
lean_inc(x_26);
lean_dec(x_18);
x_27 = lean_ctor_get(x_19, 0);
lean_inc(x_27);
lean_dec(x_19);
x_12 = x_27;
x_13 = x_26;
goto block_17;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_28 = !lean_is_exclusive(x_18);
if (x_28 == 0)
{
return x_18;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_18, 0);
x_30 = lean_ctor_get(x_18, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_18);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_array_set(x_5, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
lean_dec(x_6);
x_4 = x_12;
x_5 = x_14;
x_6 = x_16;
goto _start;
}
else
{
lean_object* x_18; 
lean_dec(x_6);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp(x_1, x_4, x_5, x_2, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_box(0);
x_29 = lean_box(0);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_28);
x_30 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(x_5, x_2, x_3, x_27, x_18, x_24, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(x_5, x_2, x_3, x_51, x_54, x_48, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_19);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_19);
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_67 = x_55;
} else {
 lean_dec_ref(x_55);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
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
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
if (lean_obj_tag(x_4) == 5)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_array_set(x_5, x_6, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_sub(x_6, x_15);
x_17 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2_spec__2(x_1, x_2, x_3, x_12, x_14, x_16, x_7, x_8, x_9, x_10, x_11);
return x_17;
}
else
{
lean_object* x_18; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_2);
lean_inc(x_1);
x_18 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifySimpleCasesOnApp(x_1, x_4, x_5, x_2, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_unbox(x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_unsigned_to_nat(0u);
x_25 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_25);
lean_ctor_set(x_27, 2, x_26);
x_28 = lean_box(0);
x_29 = lean_box(0);
lean_ctor_set(x_18, 1, x_29);
lean_ctor_set(x_18, 0, x_28);
x_30 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(x_5, x_2, x_3, x_27, x_18, x_24, x_7, x_8, x_9, x_10, x_22);
lean_dec(x_27);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_19);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_19);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
lean_dec(x_19);
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = lean_ctor_get(x_32, 0);
lean_inc(x_39);
lean_dec(x_32);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = lean_ctor_get(x_32, 0);
lean_inc(x_41);
lean_dec(x_32);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_19);
x_43 = !lean_is_exclusive(x_30);
if (x_43 == 0)
{
return x_30;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_30, 0);
x_45 = lean_ctor_get(x_30, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_30);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_47 = lean_ctor_get(x_18, 1);
lean_inc(x_47);
lean_dec(x_18);
x_48 = lean_unsigned_to_nat(0u);
x_49 = l_Lean_InductiveVal_numCtors(x_1);
lean_dec(x_1);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_51, 0, x_48);
lean_ctor_set(x_51, 1, x_49);
lean_ctor_set(x_51, 2, x_50);
x_52 = lean_box(0);
x_53 = lean_box(0);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(x_5, x_2, x_3, x_51, x_54, x_48, x_7, x_8, x_9, x_10, x_47);
lean_dec(x_51);
lean_dec(x_2);
lean_dec(x_5);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
lean_dec(x_56);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_55, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_59 = x_55;
} else {
 lean_dec_ref(x_55);
 x_59 = lean_box(0);
}
if (lean_is_scalar(x_59)) {
 x_60 = lean_alloc_ctor(0, 2, 0);
} else {
 x_60 = x_59;
}
lean_ctor_set(x_60, 0, x_19);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_19);
x_61 = lean_ctor_get(x_55, 1);
lean_inc(x_61);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_62 = x_55;
} else {
 lean_dec_ref(x_55);
 x_62 = lean_box(0);
}
x_63 = lean_ctor_get(x_57, 0);
lean_inc(x_63);
lean_dec(x_57);
if (lean_is_scalar(x_62)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_62;
}
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_61);
return x_64;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_19);
x_65 = lean_ctor_get(x_55, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_55, 1);
lean_inc(x_66);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_67 = x_55;
} else {
 lean_dec_ref(x_55);
 x_67 = lean_box(0);
}
if (lean_is_scalar(x_67)) {
 x_68 = lean_alloc_ctor(1, 2, 0);
} else {
 x_68 = x_67;
}
lean_ctor_set(x_68, 0, x_65);
lean_ctor_set(x_68, 1, x_66);
return x_68;
}
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
lean_dec(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_16 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2(x_1, x_3, x_2, x_4, x_13, x_15, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault___lam__0___boxed), 9, 2);
lean_closure_set(x_9, 0, x_2);
lean_closure_set(x_9, 1, x_3);
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_Meta_lambdaTelescope___at___Lean_PrettyPrinter_Delaborator_returnsPi_spec__0___redArg(x_10, x_9, x_12, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_3);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(1);
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
x_12 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_10, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
if (lean_obj_tag(x_14) == 6)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_14, 0);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_ctor_get(x_20, 4);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_nat_dec_eq(x_22, x_21);
lean_dec(x_22);
x_24 = lean_box(x_23);
lean_inc(x_15);
lean_ctor_set(x_12, 0, x_24);
x_16 = x_12;
x_17 = x_23;
goto block_19;
}
else
{
lean_object* x_25; 
lean_dec(x_14);
x_25 = lean_box(x_1);
lean_inc(x_15);
lean_ctor_set(x_12, 0, x_25);
x_16 = x_12;
x_17 = x_1;
goto block_19;
}
block_19:
{
if (x_17 == 0)
{
lean_dec(x_15);
lean_dec(x_11);
return x_16;
}
else
{
lean_dec(x_16);
x_2 = x_11;
x_7 = x_15;
goto _start;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_12, 0);
x_27 = lean_ctor_get(x_12, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_12);
if (lean_obj_tag(x_26) == 6)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = lean_unsigned_to_nat(0u);
x_34 = lean_ctor_get(x_32, 4);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_nat_dec_eq(x_34, x_33);
lean_dec(x_34);
x_36 = lean_box(x_35);
lean_inc(x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_27);
x_28 = x_37;
x_29 = x_35;
goto block_31;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_26);
x_38 = lean_box(x_1);
lean_inc(x_27);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_27);
x_28 = x_39;
x_29 = x_1;
goto block_31;
}
block_31:
{
if (x_29 == 0)
{
lean_dec(x_27);
lean_dec(x_11);
return x_28;
}
else
{
lean_dec(x_28);
x_2 = x_11;
x_7 = x_27;
goto _start;
}
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
x_40 = !lean_is_exclusive(x_12);
if (x_40 == 0)
{
return x_12;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
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
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Expr_isProp(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = l_Lean_InductiveVal_numTypeFormers(x_12);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_12);
x_19 = lean_box(x_18);
lean_ctor_set(x_7, 0, x_19);
return x_7;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_12, 2);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_12);
x_23 = lean_box(x_22);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_ctor_get(x_12, 1);
lean_inc(x_24);
x_25 = lean_nat_dec_eq(x_24, x_21);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; 
lean_dec(x_12);
x_26 = lean_box(x_25);
lean_ctor_set(x_7, 0, x_26);
return x_7;
}
else
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_12, 4);
lean_inc(x_27);
x_28 = l_List_isEmpty___redArg(x_27);
if (x_28 == 0)
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_12, sizeof(void*)*6);
if (x_29 == 0)
{
uint8_t x_30; 
x_30 = lean_ctor_get_uint8(x_12, sizeof(void*)*6 + 1);
lean_dec(x_12);
if (x_30 == 0)
{
lean_object* x_31; 
lean_free_object(x_7);
x_31 = l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0_spec__0(x_30, x_27, x_2, x_3, x_4, x_5, x_10);
return x_31;
}
else
{
lean_object* x_32; 
lean_dec(x_27);
x_32 = lean_box(x_29);
lean_ctor_set(x_7, 0, x_32);
return x_7;
}
}
else
{
lean_object* x_33; 
lean_dec(x_27);
lean_dec(x_12);
x_33 = lean_box(x_28);
lean_ctor_set(x_7, 0, x_33);
return x_7;
}
}
else
{
lean_object* x_34; 
lean_dec(x_27);
lean_dec(x_12);
x_34 = lean_box(x_15);
lean_ctor_set(x_7, 0, x_34);
return x_7;
}
}
}
}
}
else
{
lean_object* x_35; 
lean_dec(x_12);
x_35 = lean_box(0);
lean_ctor_set(x_7, 0, x_35);
return x_7;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_dec(x_7);
x_37 = lean_ctor_get(x_8, 0);
lean_inc(x_37);
lean_dec(x_8);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 2);
lean_inc(x_39);
lean_dec(x_38);
x_40 = l_Lean_Expr_isProp(x_39);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = l_Lean_InductiveVal_numTypeFormers(x_37);
x_42 = lean_unsigned_to_nat(1u);
x_43 = lean_nat_dec_eq(x_41, x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_37);
x_44 = lean_box(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_36);
return x_45;
}
else
{
lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_46 = lean_ctor_get(x_37, 2);
lean_inc(x_46);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_nat_dec_eq(x_46, x_47);
lean_dec(x_46);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_37);
x_49 = lean_box(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_36);
return x_50;
}
else
{
lean_object* x_51; uint8_t x_52; 
x_51 = lean_ctor_get(x_37, 1);
lean_inc(x_51);
x_52 = lean_nat_dec_eq(x_51, x_47);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_37);
x_53 = lean_box(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_36);
return x_54;
}
else
{
lean_object* x_55; uint8_t x_56; 
x_55 = lean_ctor_get(x_37, 4);
lean_inc(x_55);
x_56 = l_List_isEmpty___redArg(x_55);
if (x_56 == 0)
{
uint8_t x_57; 
x_57 = lean_ctor_get_uint8(x_37, sizeof(void*)*6);
if (x_57 == 0)
{
uint8_t x_58; 
x_58 = lean_ctor_get_uint8(x_37, sizeof(void*)*6 + 1);
lean_dec(x_37);
if (x_58 == 0)
{
lean_object* x_59; 
x_59 = l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0_spec__0(x_58, x_55, x_2, x_3, x_4, x_5, x_36);
return x_59;
}
else
{
lean_object* x_60; lean_object* x_61; 
lean_dec(x_55);
x_60 = lean_box(x_57);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_36);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_55);
lean_dec(x_37);
x_62 = lean_box(x_56);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_36);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_55);
lean_dec(x_37);
x_64 = lean_box(x_40);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_36);
return x_65;
}
}
}
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_37);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_36);
return x_67;
}
}
}
else
{
uint8_t x_68; 
lean_dec(x_8);
x_68 = !lean_is_exclusive(x_7);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_7, 0);
lean_dec(x_69);
x_70 = lean_box(0);
lean_ctor_set(x_7, 0, x_70);
return x_7;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_7, 1);
lean_inc(x_71);
lean_dec(x_7);
x_72 = lean_box(0);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_71);
return x_73;
}
}
}
else
{
uint8_t x_74; 
x_74 = !lean_is_exclusive(x_7);
if (x_74 == 0)
{
return x_7;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_7, 0);
x_76 = lean_ctor_get(x_7, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_7);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_3, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
lean_dec(x_3);
x_9 = lean_array_set(x_4, x_5, x_8);
x_10 = lean_nat_sub(x_5, x_6);
lean_dec(x_5);
x_3 = x_7;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_18; 
lean_dec(x_5);
x_12 = l_Lean_instInhabitedExpr;
x_13 = lean_unsigned_to_nat(0u);
x_18 = lean_expr_eqv(x_3, x_2);
lean_dec(x_3);
if (x_18 == 0)
{
x_14 = x_18;
goto block_17;
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_array_get_size(x_4);
x_20 = lean_nat_dec_eq(x_19, x_6);
lean_dec(x_19);
x_14 = x_20;
goto block_17;
}
block_17:
{
if (x_14 == 0)
{
lean_dec(x_4);
return x_14;
}
else
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_array_get(x_12, x_4, x_13);
lean_dec(x_4);
x_16 = lean_expr_eqv(x_15, x_1);
lean_dec(x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_3, 1);
x_27 = lean_nat_dec_lt(x_5, x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_4);
lean_ctor_set(x_28, 1, x_10);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_29 = lean_unsigned_to_nat(2u);
x_30 = l_Lean_instInhabitedExpr;
x_31 = lean_nat_add(x_5, x_29);
x_32 = lean_array_get(x_30, x_1, x_31);
lean_dec(x_31);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_33 = lean_infer_type(x_32, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_33) == 0)
{
uint8_t x_34; 
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_33, 0);
x_36 = lean_ctor_get(x_33, 1);
x_37 = lean_ctor_get(x_4, 1);
lean_inc(x_37);
lean_dec(x_4);
if (lean_obj_tag(x_35) == 7)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_35, 1);
lean_inc(x_41);
x_42 = lean_ctor_get(x_35, 2);
lean_inc(x_42);
lean_dec(x_35);
x_43 = l_Lean_Expr_hasLooseBVars(x_42);
if (x_43 == 0)
{
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_free_object(x_33);
lean_dec(x_5);
x_44 = lean_ctor_get(x_41, 0);
lean_inc(x_44);
lean_dec(x_41);
x_45 = l_Lean_Expr_bvar___override(x_44);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_42);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_46);
x_48 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_47, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_47);
x_17 = x_48;
goto block_25;
}
case 1:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_free_object(x_33);
lean_dec(x_5);
x_49 = lean_ctor_get(x_41, 0);
lean_inc(x_49);
lean_dec(x_41);
x_50 = l_Lean_Expr_fvar___override(x_49);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_42);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_51);
x_53 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_52, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_52);
x_17 = x_53;
goto block_25;
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_free_object(x_33);
lean_dec(x_5);
x_54 = lean_ctor_get(x_41, 0);
lean_inc(x_54);
lean_dec(x_41);
x_55 = l_Lean_Expr_mvar___override(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_42);
x_57 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_57, 0, x_56);
x_58 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_57, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_57);
x_17 = x_58;
goto block_25;
}
case 3:
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
lean_free_object(x_33);
lean_dec(x_5);
x_59 = lean_ctor_get(x_41, 0);
lean_inc(x_59);
lean_dec(x_41);
x_60 = l_Lean_Expr_sort___override(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_42);
x_62 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_62, 0, x_61);
x_63 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_62, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_62);
x_17 = x_63;
goto block_25;
}
case 4:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_64 = lean_ctor_get(x_41, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_41, 1);
lean_inc(x_65);
lean_dec(x_41);
x_66 = lean_box(0);
lean_inc(x_65);
x_67 = l_Lean_Expr_const___override(x_66, x_65);
switch (lean_obj_tag(x_64)) {
case 0:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_65);
lean_free_object(x_33);
lean_dec(x_5);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_42);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
x_70 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_69, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_69);
x_17 = x_70;
goto block_25;
}
case 1:
{
lean_object* x_71; 
lean_dec(x_67);
x_71 = lean_ctor_get(x_64, 0);
lean_inc(x_71);
switch (lean_obj_tag(x_71)) {
case 0:
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_64, 1);
lean_inc(x_72);
lean_dec(x_64);
x_73 = lean_mk_string_unchecked("Unit", 4, 4);
x_74 = lean_string_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
lean_dec(x_73);
lean_free_object(x_33);
lean_dec(x_5);
x_75 = l_Lean_Name_str___override(x_66, x_72);
x_76 = l_Lean_Expr_const___override(x_75, x_65);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_42);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_79 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_78, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_78);
x_17 = x_79;
goto block_25;
}
else
{
lean_dec(x_72);
if (lean_obj_tag(x_65) == 0)
{
switch (lean_obj_tag(x_42)) {
case 0:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_free_object(x_33);
lean_dec(x_5);
x_80 = lean_ctor_get(x_42, 0);
lean_inc(x_80);
lean_dec(x_42);
x_81 = l_Lean_Name_str___override(x_66, x_73);
x_82 = l_Lean_Expr_const___override(x_81, x_65);
x_83 = l_Lean_Expr_bvar___override(x_80);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_85, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_85);
x_17 = x_86;
goto block_25;
}
case 1:
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_free_object(x_33);
lean_dec(x_5);
x_87 = lean_ctor_get(x_42, 0);
lean_inc(x_87);
lean_dec(x_42);
x_88 = l_Lean_Name_str___override(x_66, x_73);
x_89 = l_Lean_Expr_const___override(x_88, x_65);
x_90 = l_Lean_Expr_fvar___override(x_87);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_92, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_92);
x_17 = x_93;
goto block_25;
}
case 2:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_free_object(x_33);
lean_dec(x_5);
x_94 = lean_ctor_get(x_42, 0);
lean_inc(x_94);
lean_dec(x_42);
x_95 = l_Lean_Name_str___override(x_66, x_73);
x_96 = l_Lean_Expr_const___override(x_95, x_65);
x_97 = l_Lean_Expr_mvar___override(x_94);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_99, 0, x_98);
x_100 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_99, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_99);
x_17 = x_100;
goto block_25;
}
case 3:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_free_object(x_33);
lean_dec(x_5);
x_101 = lean_ctor_get(x_42, 0);
lean_inc(x_101);
lean_dec(x_42);
x_102 = l_Lean_Name_str___override(x_66, x_73);
x_103 = l_Lean_Expr_const___override(x_102, x_65);
x_104 = l_Lean_Expr_sort___override(x_101);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_103);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_105);
x_107 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_106, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_106);
x_17 = x_107;
goto block_25;
}
case 4:
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_free_object(x_33);
lean_dec(x_5);
x_108 = lean_ctor_get(x_42, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_42, 1);
lean_inc(x_109);
lean_dec(x_42);
x_110 = l_Lean_Name_str___override(x_66, x_73);
x_111 = l_Lean_Expr_const___override(x_110, x_65);
x_112 = l_Lean_Expr_const___override(x_108, x_109);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_114, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_114);
x_17 = x_115;
goto block_25;
}
case 5:
{
lean_object* x_116; 
x_116 = lean_ctor_get(x_42, 1);
lean_inc(x_116);
switch (lean_obj_tag(x_116)) {
case 0:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_free_object(x_33);
lean_dec(x_5);
x_117 = lean_ctor_get(x_42, 0);
lean_inc(x_117);
lean_dec(x_42);
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = l_Lean_Name_str___override(x_66, x_73);
x_120 = l_Lean_Expr_const___override(x_119, x_65);
x_121 = l_Lean_Expr_bvar___override(x_118);
x_122 = l_Lean_Expr_app___override(x_117, x_121);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_124, 0, x_123);
x_125 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_124, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_124);
x_17 = x_125;
goto block_25;
}
case 1:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_33);
lean_dec(x_5);
x_126 = lean_ctor_get(x_42, 0);
lean_inc(x_126);
lean_dec(x_42);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
lean_dec(x_116);
x_128 = l_Lean_Name_str___override(x_66, x_73);
x_129 = l_Lean_Expr_const___override(x_128, x_65);
x_130 = l_Lean_Expr_fvar___override(x_127);
x_131 = l_Lean_Expr_app___override(x_126, x_130);
x_132 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_132, 0, x_129);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_133, 0, x_132);
x_134 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_133, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_133);
x_17 = x_134;
goto block_25;
}
case 2:
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
lean_free_object(x_33);
lean_dec(x_5);
x_135 = lean_ctor_get(x_42, 0);
lean_inc(x_135);
lean_dec(x_42);
x_136 = lean_ctor_get(x_116, 0);
lean_inc(x_136);
lean_dec(x_116);
x_137 = l_Lean_Name_str___override(x_66, x_73);
x_138 = l_Lean_Expr_const___override(x_137, x_65);
x_139 = l_Lean_Expr_mvar___override(x_136);
x_140 = l_Lean_Expr_app___override(x_135, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_138);
lean_ctor_set(x_141, 1, x_140);
x_142 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_142, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_142);
x_17 = x_143;
goto block_25;
}
case 3:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_free_object(x_33);
lean_dec(x_5);
x_144 = lean_ctor_get(x_42, 0);
lean_inc(x_144);
lean_dec(x_42);
x_145 = lean_ctor_get(x_116, 0);
lean_inc(x_145);
lean_dec(x_116);
x_146 = l_Lean_Name_str___override(x_66, x_73);
x_147 = l_Lean_Expr_const___override(x_146, x_65);
x_148 = l_Lean_Expr_sort___override(x_145);
x_149 = l_Lean_Expr_app___override(x_144, x_148);
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_151, 0, x_150);
x_152 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_151, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_151);
x_17 = x_152;
goto block_25;
}
case 4:
{
lean_object* x_153; 
x_153 = lean_ctor_get(x_116, 1);
lean_inc(x_153);
if (lean_obj_tag(x_153) == 0)
{
lean_object* x_154; lean_object* x_155; uint8_t x_156; 
lean_dec(x_73);
x_154 = lean_ctor_get(x_42, 0);
lean_inc(x_154);
lean_dec(x_42);
x_155 = lean_ctor_get(x_116, 0);
lean_inc(x_155);
lean_dec(x_116);
x_156 = lean_expr_eqv(x_154, x_2);
lean_dec(x_154);
if (x_156 == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_155);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_157 = lean_box(0);
x_158 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_158, 0, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_158);
lean_ctor_set(x_159, 1, x_37);
lean_ctor_set(x_33, 0, x_159);
return x_33;
}
else
{
lean_object* x_160; 
lean_free_object(x_33);
x_160 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_155, x_6, x_7, x_8, x_9, x_36);
if (lean_obj_tag(x_160) == 0)
{
lean_object* x_161; 
x_161 = lean_ctor_get(x_160, 0);
lean_inc(x_161);
if (lean_obj_tag(x_161) == 6)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_ctor_get(x_160, 1);
lean_inc(x_162);
lean_dec(x_160);
x_163 = lean_ctor_get(x_161, 0);
lean_inc(x_163);
lean_dec(x_161);
x_164 = lean_box(0);
x_165 = lean_array_push(x_37, x_163);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
x_11 = x_166;
x_12 = x_162;
goto block_16;
}
else
{
uint8_t x_167; 
lean_dec(x_161);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_167 = !lean_is_exclusive(x_160);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_168 = lean_ctor_get(x_160, 0);
lean_dec(x_168);
x_169 = lean_box(0);
x_170 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_170, 0, x_169);
x_171 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_171, 0, x_170);
lean_ctor_set(x_171, 1, x_37);
lean_ctor_set(x_160, 0, x_171);
return x_160;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_160, 1);
lean_inc(x_172);
lean_dec(x_160);
x_173 = lean_box(0);
x_174 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_174, 0, x_173);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_174);
lean_ctor_set(x_175, 1, x_37);
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_175);
lean_ctor_set(x_176, 1, x_172);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_37);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_177 = !lean_is_exclusive(x_160);
if (x_177 == 0)
{
return x_160;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_160, 0);
x_179 = lean_ctor_get(x_160, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_160);
x_180 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_180, 0, x_178);
lean_ctor_set(x_180, 1, x_179);
return x_180;
}
}
}
}
else
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
lean_free_object(x_33);
lean_dec(x_5);
x_181 = lean_ctor_get(x_42, 0);
lean_inc(x_181);
lean_dec(x_42);
x_182 = lean_ctor_get(x_116, 0);
lean_inc(x_182);
lean_dec(x_116);
x_183 = l_Lean_Name_str___override(x_66, x_73);
x_184 = l_Lean_Expr_const___override(x_183, x_65);
lean_inc(x_153);
x_185 = l_Lean_Expr_const___override(x_182, x_153);
x_186 = !lean_is_exclusive(x_153);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_187 = lean_ctor_get(x_153, 1);
lean_dec(x_187);
x_188 = lean_ctor_get(x_153, 0);
lean_dec(x_188);
x_189 = l_Lean_Expr_app___override(x_181, x_185);
lean_ctor_set_tag(x_153, 0);
lean_ctor_set(x_153, 1, x_189);
lean_ctor_set(x_153, 0, x_184);
x_190 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_190, 0, x_153);
x_191 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_190, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_190);
x_17 = x_191;
goto block_25;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; 
lean_dec(x_153);
x_192 = l_Lean_Expr_app___override(x_181, x_185);
x_193 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_193, 0, x_184);
lean_ctor_set(x_193, 1, x_192);
x_194 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_194, 0, x_193);
x_195 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_194, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_194);
x_17 = x_195;
goto block_25;
}
}
}
case 5:
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; 
lean_free_object(x_33);
lean_dec(x_5);
x_196 = lean_ctor_get(x_42, 0);
lean_inc(x_196);
lean_dec(x_42);
x_197 = lean_ctor_get(x_116, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_116, 1);
lean_inc(x_198);
lean_dec(x_116);
x_199 = l_Lean_Name_str___override(x_66, x_73);
x_200 = l_Lean_Expr_const___override(x_199, x_65);
x_201 = l_Lean_Expr_app___override(x_197, x_198);
x_202 = l_Lean_Expr_app___override(x_196, x_201);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_200);
lean_ctor_set(x_203, 1, x_202);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
x_205 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_204, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_204);
x_17 = x_205;
goto block_25;
}
case 6:
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; uint8_t x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; 
lean_free_object(x_33);
lean_dec(x_5);
x_206 = lean_ctor_get(x_42, 0);
lean_inc(x_206);
lean_dec(x_42);
x_207 = lean_ctor_get(x_116, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_116, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_116, 2);
lean_inc(x_209);
x_210 = lean_ctor_get_uint8(x_116, sizeof(void*)*3 + 8);
lean_dec(x_116);
x_211 = l_Lean_Name_str___override(x_66, x_73);
x_212 = l_Lean_Expr_const___override(x_211, x_65);
x_213 = l_Lean_Expr_lam___override(x_207, x_208, x_209, x_210);
x_214 = l_Lean_Expr_app___override(x_206, x_213);
x_215 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_215, 0, x_212);
lean_ctor_set(x_215, 1, x_214);
x_216 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_216, 0, x_215);
x_217 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_216, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_216);
x_17 = x_217;
goto block_25;
}
case 7:
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; uint8_t x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_free_object(x_33);
lean_dec(x_5);
x_218 = lean_ctor_get(x_42, 0);
lean_inc(x_218);
lean_dec(x_42);
x_219 = lean_ctor_get(x_116, 0);
lean_inc(x_219);
x_220 = lean_ctor_get(x_116, 1);
lean_inc(x_220);
x_221 = lean_ctor_get(x_116, 2);
lean_inc(x_221);
x_222 = lean_ctor_get_uint8(x_116, sizeof(void*)*3 + 8);
lean_dec(x_116);
x_223 = l_Lean_Name_str___override(x_66, x_73);
x_224 = l_Lean_Expr_const___override(x_223, x_65);
x_225 = l_Lean_Expr_forallE___override(x_219, x_220, x_221, x_222);
x_226 = l_Lean_Expr_app___override(x_218, x_225);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_224);
lean_ctor_set(x_227, 1, x_226);
x_228 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_228, 0, x_227);
x_229 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_228, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_228);
x_17 = x_229;
goto block_25;
}
case 8:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; 
lean_free_object(x_33);
lean_dec(x_5);
x_230 = lean_ctor_get(x_42, 0);
lean_inc(x_230);
lean_dec(x_42);
x_231 = lean_ctor_get(x_116, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_116, 1);
lean_inc(x_232);
x_233 = lean_ctor_get(x_116, 2);
lean_inc(x_233);
x_234 = lean_ctor_get(x_116, 3);
lean_inc(x_234);
x_235 = lean_ctor_get_uint8(x_116, sizeof(void*)*4 + 8);
lean_dec(x_116);
x_236 = l_Lean_Name_str___override(x_66, x_73);
x_237 = l_Lean_Expr_const___override(x_236, x_65);
x_238 = l_Lean_Expr_letE___override(x_231, x_232, x_233, x_234, x_235);
x_239 = l_Lean_Expr_app___override(x_230, x_238);
x_240 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_240, 0, x_237);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_241, 0, x_240);
x_242 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_241, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_241);
x_17 = x_242;
goto block_25;
}
case 9:
{
lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
lean_free_object(x_33);
lean_dec(x_5);
x_243 = lean_ctor_get(x_42, 0);
lean_inc(x_243);
lean_dec(x_42);
x_244 = lean_ctor_get(x_116, 0);
lean_inc(x_244);
lean_dec(x_116);
x_245 = l_Lean_Name_str___override(x_66, x_73);
x_246 = l_Lean_Expr_const___override(x_245, x_65);
x_247 = l_Lean_Expr_lit___override(x_244);
x_248 = l_Lean_Expr_app___override(x_243, x_247);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_248);
x_250 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_250, 0, x_249);
x_251 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_250, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_250);
x_17 = x_251;
goto block_25;
}
case 10:
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
lean_free_object(x_33);
lean_dec(x_5);
x_252 = lean_ctor_get(x_42, 0);
lean_inc(x_252);
lean_dec(x_42);
x_253 = lean_ctor_get(x_116, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_116, 1);
lean_inc(x_254);
lean_dec(x_116);
x_255 = l_Lean_Name_str___override(x_66, x_73);
x_256 = l_Lean_Expr_const___override(x_255, x_65);
x_257 = l_Lean_Expr_mdata___override(x_253, x_254);
x_258 = l_Lean_Expr_app___override(x_252, x_257);
x_259 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_259, 0, x_256);
lean_ctor_set(x_259, 1, x_258);
x_260 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_260, 0, x_259);
x_261 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_260, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_260);
x_17 = x_261;
goto block_25;
}
default: 
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_free_object(x_33);
lean_dec(x_5);
x_262 = lean_ctor_get(x_42, 0);
lean_inc(x_262);
lean_dec(x_42);
x_263 = lean_ctor_get(x_116, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_116, 1);
lean_inc(x_264);
x_265 = lean_ctor_get(x_116, 2);
lean_inc(x_265);
lean_dec(x_116);
x_266 = l_Lean_Name_str___override(x_66, x_73);
x_267 = l_Lean_Expr_const___override(x_266, x_65);
x_268 = l_Lean_Expr_proj___override(x_263, x_264, x_265);
x_269 = l_Lean_Expr_app___override(x_262, x_268);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_267);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_271, 0, x_270);
x_272 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_271, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_271);
x_17 = x_272;
goto block_25;
}
}
}
case 6:
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_free_object(x_33);
lean_dec(x_5);
x_273 = lean_ctor_get(x_42, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_42, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_42, 2);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_277 = l_Lean_Name_str___override(x_66, x_73);
x_278 = l_Lean_Expr_const___override(x_277, x_65);
x_279 = l_Lean_Expr_lam___override(x_273, x_274, x_275, x_276);
x_280 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_280, 0, x_278);
lean_ctor_set(x_280, 1, x_279);
x_281 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_281, 0, x_280);
x_282 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_281, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_281);
x_17 = x_282;
goto block_25;
}
case 7:
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; uint8_t x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_free_object(x_33);
lean_dec(x_5);
x_283 = lean_ctor_get(x_42, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_42, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_42, 2);
lean_inc(x_285);
x_286 = lean_ctor_get_uint8(x_42, sizeof(void*)*3 + 8);
lean_dec(x_42);
x_287 = l_Lean_Name_str___override(x_66, x_73);
x_288 = l_Lean_Expr_const___override(x_287, x_65);
x_289 = l_Lean_Expr_forallE___override(x_283, x_284, x_285, x_286);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
x_291 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_291, 0, x_290);
x_292 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_291, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_291);
x_17 = x_292;
goto block_25;
}
case 8:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; uint8_t x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_free_object(x_33);
lean_dec(x_5);
x_293 = lean_ctor_get(x_42, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_42, 1);
lean_inc(x_294);
x_295 = lean_ctor_get(x_42, 2);
lean_inc(x_295);
x_296 = lean_ctor_get(x_42, 3);
lean_inc(x_296);
x_297 = lean_ctor_get_uint8(x_42, sizeof(void*)*4 + 8);
lean_dec(x_42);
x_298 = l_Lean_Name_str___override(x_66, x_73);
x_299 = l_Lean_Expr_const___override(x_298, x_65);
x_300 = l_Lean_Expr_letE___override(x_293, x_294, x_295, x_296, x_297);
x_301 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_301, 0, x_299);
lean_ctor_set(x_301, 1, x_300);
x_302 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_302, 0, x_301);
x_303 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_302, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_302);
x_17 = x_303;
goto block_25;
}
case 9:
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_free_object(x_33);
lean_dec(x_5);
x_304 = lean_ctor_get(x_42, 0);
lean_inc(x_304);
lean_dec(x_42);
x_305 = l_Lean_Name_str___override(x_66, x_73);
x_306 = l_Lean_Expr_const___override(x_305, x_65);
x_307 = l_Lean_Expr_lit___override(x_304);
x_308 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_309, 0, x_308);
x_310 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_309, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_309);
x_17 = x_310;
goto block_25;
}
case 10:
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; 
lean_free_object(x_33);
lean_dec(x_5);
x_311 = lean_ctor_get(x_42, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_42, 1);
lean_inc(x_312);
lean_dec(x_42);
x_313 = l_Lean_Name_str___override(x_66, x_73);
x_314 = l_Lean_Expr_const___override(x_313, x_65);
x_315 = l_Lean_Expr_mdata___override(x_311, x_312);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_314);
lean_ctor_set(x_316, 1, x_315);
x_317 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_317, 0, x_316);
x_318 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_317, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_317);
x_17 = x_318;
goto block_25;
}
default: 
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_free_object(x_33);
lean_dec(x_5);
x_319 = lean_ctor_get(x_42, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_42, 1);
lean_inc(x_320);
x_321 = lean_ctor_get(x_42, 2);
lean_inc(x_321);
lean_dec(x_42);
x_322 = l_Lean_Name_str___override(x_66, x_73);
x_323 = l_Lean_Expr_const___override(x_322, x_65);
x_324 = l_Lean_Expr_proj___override(x_319, x_320, x_321);
x_325 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_325, 0, x_323);
lean_ctor_set(x_325, 1, x_324);
x_326 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_326, 0, x_325);
x_327 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_326, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_326);
x_17 = x_327;
goto block_25;
}
}
}
else
{
lean_object* x_328; lean_object* x_329; uint8_t x_330; 
lean_free_object(x_33);
lean_dec(x_5);
x_328 = l_Lean_Name_str___override(x_66, x_73);
lean_inc(x_65);
x_329 = l_Lean_Expr_const___override(x_328, x_65);
x_330 = !lean_is_exclusive(x_65);
if (x_330 == 0)
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_331 = lean_ctor_get(x_65, 1);
lean_dec(x_331);
x_332 = lean_ctor_get(x_65, 0);
lean_dec(x_332);
lean_ctor_set_tag(x_65, 0);
lean_ctor_set(x_65, 1, x_42);
lean_ctor_set(x_65, 0, x_329);
x_333 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_333, 0, x_65);
x_334 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_333, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_333);
x_17 = x_334;
goto block_25;
}
else
{
lean_object* x_335; lean_object* x_336; lean_object* x_337; 
lean_dec(x_65);
x_335 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_335, 0, x_329);
lean_ctor_set(x_335, 1, x_42);
x_336 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_336, 0, x_335);
x_337 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_336, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_336);
x_17 = x_337;
goto block_25;
}
}
}
}
case 1:
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; 
lean_free_object(x_33);
lean_dec(x_5);
x_338 = lean_ctor_get(x_64, 1);
lean_inc(x_338);
lean_dec(x_64);
x_339 = lean_ctor_get(x_71, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_71, 1);
lean_inc(x_340);
lean_dec(x_71);
x_341 = l_Lean_Name_str___override(x_339, x_340);
x_342 = l_Lean_Name_str___override(x_341, x_338);
x_343 = l_Lean_Expr_const___override(x_342, x_65);
x_344 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_344, 0, x_343);
lean_ctor_set(x_344, 1, x_42);
x_345 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_345, 0, x_344);
x_346 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_345, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_345);
x_17 = x_346;
goto block_25;
}
default: 
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_free_object(x_33);
lean_dec(x_5);
x_347 = lean_ctor_get(x_64, 1);
lean_inc(x_347);
lean_dec(x_64);
x_348 = lean_ctor_get(x_71, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_71, 1);
lean_inc(x_349);
lean_dec(x_71);
x_350 = l_Lean_Name_num___override(x_348, x_349);
x_351 = l_Lean_Name_str___override(x_350, x_347);
x_352 = l_Lean_Expr_const___override(x_351, x_65);
x_353 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_353, 0, x_352);
lean_ctor_set(x_353, 1, x_42);
x_354 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_354, 0, x_353);
x_355 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_354, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_354);
x_17 = x_355;
goto block_25;
}
}
}
default: 
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_67);
lean_free_object(x_33);
lean_dec(x_5);
x_356 = lean_ctor_get(x_64, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_64, 1);
lean_inc(x_357);
lean_dec(x_64);
x_358 = l_Lean_Name_num___override(x_356, x_357);
x_359 = l_Lean_Expr_const___override(x_358, x_65);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_42);
x_361 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_361, 0, x_360);
x_362 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_361, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_361);
x_17 = x_362;
goto block_25;
}
}
}
case 5:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; 
lean_free_object(x_33);
lean_dec(x_5);
x_363 = lean_ctor_get(x_41, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_41, 1);
lean_inc(x_364);
lean_dec(x_41);
x_365 = l_Lean_Expr_app___override(x_363, x_364);
x_366 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_366, 0, x_365);
lean_ctor_set(x_366, 1, x_42);
x_367 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_367, 0, x_366);
x_368 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_367, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_367);
x_17 = x_368;
goto block_25;
}
case 6:
{
lean_object* x_369; lean_object* x_370; lean_object* x_371; uint8_t x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; 
lean_free_object(x_33);
lean_dec(x_5);
x_369 = lean_ctor_get(x_41, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_41, 1);
lean_inc(x_370);
x_371 = lean_ctor_get(x_41, 2);
lean_inc(x_371);
x_372 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_373 = l_Lean_Expr_lam___override(x_369, x_370, x_371, x_372);
x_374 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_374, 0, x_373);
lean_ctor_set(x_374, 1, x_42);
x_375 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_375, 0, x_374);
x_376 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_375, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_375);
x_17 = x_376;
goto block_25;
}
case 7:
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; uint8_t x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_free_object(x_33);
lean_dec(x_5);
x_377 = lean_ctor_get(x_41, 0);
lean_inc(x_377);
x_378 = lean_ctor_get(x_41, 1);
lean_inc(x_378);
x_379 = lean_ctor_get(x_41, 2);
lean_inc(x_379);
x_380 = lean_ctor_get_uint8(x_41, sizeof(void*)*3 + 8);
lean_dec(x_41);
x_381 = l_Lean_Expr_forallE___override(x_377, x_378, x_379, x_380);
x_382 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_382, 0, x_381);
lean_ctor_set(x_382, 1, x_42);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
x_384 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_383, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_383);
x_17 = x_384;
goto block_25;
}
case 8:
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; 
lean_free_object(x_33);
lean_dec(x_5);
x_385 = lean_ctor_get(x_41, 0);
lean_inc(x_385);
x_386 = lean_ctor_get(x_41, 1);
lean_inc(x_386);
x_387 = lean_ctor_get(x_41, 2);
lean_inc(x_387);
x_388 = lean_ctor_get(x_41, 3);
lean_inc(x_388);
x_389 = lean_ctor_get_uint8(x_41, sizeof(void*)*4 + 8);
lean_dec(x_41);
x_390 = l_Lean_Expr_letE___override(x_385, x_386, x_387, x_388, x_389);
x_391 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_391, 0, x_390);
lean_ctor_set(x_391, 1, x_42);
x_392 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_392, 0, x_391);
x_393 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_392, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_392);
x_17 = x_393;
goto block_25;
}
case 9:
{
lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
lean_free_object(x_33);
lean_dec(x_5);
x_394 = lean_ctor_get(x_41, 0);
lean_inc(x_394);
lean_dec(x_41);
x_395 = l_Lean_Expr_lit___override(x_394);
x_396 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_396, 0, x_395);
lean_ctor_set(x_396, 1, x_42);
x_397 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_397, 0, x_396);
x_398 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_397, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_397);
x_17 = x_398;
goto block_25;
}
case 10:
{
lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
lean_free_object(x_33);
lean_dec(x_5);
x_399 = lean_ctor_get(x_41, 0);
lean_inc(x_399);
x_400 = lean_ctor_get(x_41, 1);
lean_inc(x_400);
lean_dec(x_41);
x_401 = l_Lean_Expr_mdata___override(x_399, x_400);
x_402 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_42);
x_403 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_403, 0, x_402);
x_404 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_403, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_403);
x_17 = x_404;
goto block_25;
}
default: 
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; 
lean_free_object(x_33);
lean_dec(x_5);
x_405 = lean_ctor_get(x_41, 0);
lean_inc(x_405);
x_406 = lean_ctor_get(x_41, 1);
lean_inc(x_406);
x_407 = lean_ctor_get(x_41, 2);
lean_inc(x_407);
lean_dec(x_41);
x_408 = l_Lean_Expr_proj___override(x_405, x_406, x_407);
x_409 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_409, 0, x_408);
lean_ctor_set(x_409, 1, x_42);
x_410 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_410, 0, x_409);
x_411 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_410, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_410);
x_17 = x_411;
goto block_25;
}
}
}
else
{
lean_object* x_412; 
lean_dec(x_42);
lean_dec(x_41);
lean_free_object(x_33);
lean_dec(x_5);
x_412 = lean_box(0);
x_38 = x_412;
goto block_40;
}
}
else
{
lean_object* x_413; 
lean_free_object(x_33);
lean_dec(x_35);
lean_dec(x_5);
x_413 = lean_box(0);
x_38 = x_413;
goto block_40;
}
block_40:
{
lean_object* x_39; 
x_39 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_37, x_38, x_6, x_7, x_8, x_9, x_36);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_38);
x_17 = x_39;
goto block_25;
}
}
else
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; 
x_414 = lean_ctor_get(x_33, 0);
x_415 = lean_ctor_get(x_33, 1);
lean_inc(x_415);
lean_inc(x_414);
lean_dec(x_33);
x_416 = lean_ctor_get(x_4, 1);
lean_inc(x_416);
lean_dec(x_4);
if (lean_obj_tag(x_414) == 7)
{
lean_object* x_420; lean_object* x_421; uint8_t x_422; 
x_420 = lean_ctor_get(x_414, 1);
lean_inc(x_420);
x_421 = lean_ctor_get(x_414, 2);
lean_inc(x_421);
lean_dec(x_414);
x_422 = l_Lean_Expr_hasLooseBVars(x_421);
if (x_422 == 0)
{
switch (lean_obj_tag(x_420)) {
case 0:
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_5);
x_423 = lean_ctor_get(x_420, 0);
lean_inc(x_423);
lean_dec(x_420);
x_424 = l_Lean_Expr_bvar___override(x_423);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_424);
lean_ctor_set(x_425, 1, x_421);
x_426 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_426, 0, x_425);
x_427 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_426, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_426);
x_17 = x_427;
goto block_25;
}
case 1:
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_5);
x_428 = lean_ctor_get(x_420, 0);
lean_inc(x_428);
lean_dec(x_420);
x_429 = l_Lean_Expr_fvar___override(x_428);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_421);
x_431 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_431, 0, x_430);
x_432 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_431, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_431);
x_17 = x_432;
goto block_25;
}
case 2:
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; 
lean_dec(x_5);
x_433 = lean_ctor_get(x_420, 0);
lean_inc(x_433);
lean_dec(x_420);
x_434 = l_Lean_Expr_mvar___override(x_433);
x_435 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_435, 0, x_434);
lean_ctor_set(x_435, 1, x_421);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
x_437 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_436, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_436);
x_17 = x_437;
goto block_25;
}
case 3:
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_5);
x_438 = lean_ctor_get(x_420, 0);
lean_inc(x_438);
lean_dec(x_420);
x_439 = l_Lean_Expr_sort___override(x_438);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_421);
x_441 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_441, 0, x_440);
x_442 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_441, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_441);
x_17 = x_442;
goto block_25;
}
case 4:
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; 
x_443 = lean_ctor_get(x_420, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_420, 1);
lean_inc(x_444);
lean_dec(x_420);
x_445 = lean_box(0);
lean_inc(x_444);
x_446 = l_Lean_Expr_const___override(x_445, x_444);
switch (lean_obj_tag(x_443)) {
case 0:
{
lean_object* x_447; lean_object* x_448; lean_object* x_449; 
lean_dec(x_444);
lean_dec(x_5);
x_447 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_447, 0, x_446);
lean_ctor_set(x_447, 1, x_421);
x_448 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_448, 0, x_447);
x_449 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_448, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_448);
x_17 = x_449;
goto block_25;
}
case 1:
{
lean_object* x_450; 
lean_dec(x_446);
x_450 = lean_ctor_get(x_443, 0);
lean_inc(x_450);
switch (lean_obj_tag(x_450)) {
case 0:
{
lean_object* x_451; lean_object* x_452; uint8_t x_453; 
x_451 = lean_ctor_get(x_443, 1);
lean_inc(x_451);
lean_dec(x_443);
x_452 = lean_mk_string_unchecked("Unit", 4, 4);
x_453 = lean_string_dec_eq(x_451, x_452);
if (x_453 == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
lean_dec(x_452);
lean_dec(x_5);
x_454 = l_Lean_Name_str___override(x_445, x_451);
x_455 = l_Lean_Expr_const___override(x_454, x_444);
x_456 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_456, 0, x_455);
lean_ctor_set(x_456, 1, x_421);
x_457 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_457, 0, x_456);
x_458 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_457, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_457);
x_17 = x_458;
goto block_25;
}
else
{
lean_dec(x_451);
if (lean_obj_tag(x_444) == 0)
{
switch (lean_obj_tag(x_421)) {
case 0:
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
lean_dec(x_5);
x_459 = lean_ctor_get(x_421, 0);
lean_inc(x_459);
lean_dec(x_421);
x_460 = l_Lean_Name_str___override(x_445, x_452);
x_461 = l_Lean_Expr_const___override(x_460, x_444);
x_462 = l_Lean_Expr_bvar___override(x_459);
x_463 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_463, 0, x_461);
lean_ctor_set(x_463, 1, x_462);
x_464 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_464, 0, x_463);
x_465 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_464, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_464);
x_17 = x_465;
goto block_25;
}
case 1:
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_5);
x_466 = lean_ctor_get(x_421, 0);
lean_inc(x_466);
lean_dec(x_421);
x_467 = l_Lean_Name_str___override(x_445, x_452);
x_468 = l_Lean_Expr_const___override(x_467, x_444);
x_469 = l_Lean_Expr_fvar___override(x_466);
x_470 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_470, 0, x_468);
lean_ctor_set(x_470, 1, x_469);
x_471 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_471, 0, x_470);
x_472 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_471, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_471);
x_17 = x_472;
goto block_25;
}
case 2:
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_5);
x_473 = lean_ctor_get(x_421, 0);
lean_inc(x_473);
lean_dec(x_421);
x_474 = l_Lean_Name_str___override(x_445, x_452);
x_475 = l_Lean_Expr_const___override(x_474, x_444);
x_476 = l_Lean_Expr_mvar___override(x_473);
x_477 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
x_478 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_478, 0, x_477);
x_479 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_478, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_478);
x_17 = x_479;
goto block_25;
}
case 3:
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_5);
x_480 = lean_ctor_get(x_421, 0);
lean_inc(x_480);
lean_dec(x_421);
x_481 = l_Lean_Name_str___override(x_445, x_452);
x_482 = l_Lean_Expr_const___override(x_481, x_444);
x_483 = l_Lean_Expr_sort___override(x_480);
x_484 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_484, 0, x_482);
lean_ctor_set(x_484, 1, x_483);
x_485 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_485, 0, x_484);
x_486 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_485, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_485);
x_17 = x_486;
goto block_25;
}
case 4:
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; 
lean_dec(x_5);
x_487 = lean_ctor_get(x_421, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_421, 1);
lean_inc(x_488);
lean_dec(x_421);
x_489 = l_Lean_Name_str___override(x_445, x_452);
x_490 = l_Lean_Expr_const___override(x_489, x_444);
x_491 = l_Lean_Expr_const___override(x_487, x_488);
x_492 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_492, 0, x_490);
lean_ctor_set(x_492, 1, x_491);
x_493 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_493, 0, x_492);
x_494 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_493, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_493);
x_17 = x_494;
goto block_25;
}
case 5:
{
lean_object* x_495; 
x_495 = lean_ctor_get(x_421, 1);
lean_inc(x_495);
switch (lean_obj_tag(x_495)) {
case 0:
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_5);
x_496 = lean_ctor_get(x_421, 0);
lean_inc(x_496);
lean_dec(x_421);
x_497 = lean_ctor_get(x_495, 0);
lean_inc(x_497);
lean_dec(x_495);
x_498 = l_Lean_Name_str___override(x_445, x_452);
x_499 = l_Lean_Expr_const___override(x_498, x_444);
x_500 = l_Lean_Expr_bvar___override(x_497);
x_501 = l_Lean_Expr_app___override(x_496, x_500);
x_502 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_502, 0, x_499);
lean_ctor_set(x_502, 1, x_501);
x_503 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_503, 0, x_502);
x_504 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_503, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_503);
x_17 = x_504;
goto block_25;
}
case 1:
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; 
lean_dec(x_5);
x_505 = lean_ctor_get(x_421, 0);
lean_inc(x_505);
lean_dec(x_421);
x_506 = lean_ctor_get(x_495, 0);
lean_inc(x_506);
lean_dec(x_495);
x_507 = l_Lean_Name_str___override(x_445, x_452);
x_508 = l_Lean_Expr_const___override(x_507, x_444);
x_509 = l_Lean_Expr_fvar___override(x_506);
x_510 = l_Lean_Expr_app___override(x_505, x_509);
x_511 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_511, 0, x_508);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_512, 0, x_511);
x_513 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_512, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_512);
x_17 = x_513;
goto block_25;
}
case 2:
{
lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_5);
x_514 = lean_ctor_get(x_421, 0);
lean_inc(x_514);
lean_dec(x_421);
x_515 = lean_ctor_get(x_495, 0);
lean_inc(x_515);
lean_dec(x_495);
x_516 = l_Lean_Name_str___override(x_445, x_452);
x_517 = l_Lean_Expr_const___override(x_516, x_444);
x_518 = l_Lean_Expr_mvar___override(x_515);
x_519 = l_Lean_Expr_app___override(x_514, x_518);
x_520 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_520, 0, x_517);
lean_ctor_set(x_520, 1, x_519);
x_521 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_521, 0, x_520);
x_522 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_521, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_521);
x_17 = x_522;
goto block_25;
}
case 3:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
lean_dec(x_5);
x_523 = lean_ctor_get(x_421, 0);
lean_inc(x_523);
lean_dec(x_421);
x_524 = lean_ctor_get(x_495, 0);
lean_inc(x_524);
lean_dec(x_495);
x_525 = l_Lean_Name_str___override(x_445, x_452);
x_526 = l_Lean_Expr_const___override(x_525, x_444);
x_527 = l_Lean_Expr_sort___override(x_524);
x_528 = l_Lean_Expr_app___override(x_523, x_527);
x_529 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_529, 0, x_526);
lean_ctor_set(x_529, 1, x_528);
x_530 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_530, 0, x_529);
x_531 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_530, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_530);
x_17 = x_531;
goto block_25;
}
case 4:
{
lean_object* x_532; 
x_532 = lean_ctor_get(x_495, 1);
lean_inc(x_532);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; uint8_t x_535; 
lean_dec(x_452);
x_533 = lean_ctor_get(x_421, 0);
lean_inc(x_533);
lean_dec(x_421);
x_534 = lean_ctor_get(x_495, 0);
lean_inc(x_534);
lean_dec(x_495);
x_535 = lean_expr_eqv(x_533, x_2);
lean_dec(x_533);
if (x_535 == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; 
lean_dec(x_534);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_536 = lean_box(0);
x_537 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_537, 0, x_536);
x_538 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_538, 0, x_537);
lean_ctor_set(x_538, 1, x_416);
x_539 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_539, 0, x_538);
lean_ctor_set(x_539, 1, x_415);
return x_539;
}
else
{
lean_object* x_540; 
x_540 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_534, x_6, x_7, x_8, x_9, x_415);
if (lean_obj_tag(x_540) == 0)
{
lean_object* x_541; 
x_541 = lean_ctor_get(x_540, 0);
lean_inc(x_541);
if (lean_obj_tag(x_541) == 6)
{
lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; 
x_542 = lean_ctor_get(x_540, 1);
lean_inc(x_542);
lean_dec(x_540);
x_543 = lean_ctor_get(x_541, 0);
lean_inc(x_543);
lean_dec(x_541);
x_544 = lean_box(0);
x_545 = lean_array_push(x_416, x_543);
x_546 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_546, 0, x_544);
lean_ctor_set(x_546, 1, x_545);
x_11 = x_546;
x_12 = x_542;
goto block_16;
}
else
{
lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
lean_dec(x_541);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_547 = lean_ctor_get(x_540, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_548 = x_540;
} else {
 lean_dec_ref(x_540);
 x_548 = lean_box(0);
}
x_549 = lean_box(0);
x_550 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_550, 0, x_549);
x_551 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_551, 0, x_550);
lean_ctor_set(x_551, 1, x_416);
if (lean_is_scalar(x_548)) {
 x_552 = lean_alloc_ctor(0, 2, 0);
} else {
 x_552 = x_548;
}
lean_ctor_set(x_552, 0, x_551);
lean_ctor_set(x_552, 1, x_547);
return x_552;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_416);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_553 = lean_ctor_get(x_540, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_540, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_540)) {
 lean_ctor_release(x_540, 0);
 lean_ctor_release(x_540, 1);
 x_555 = x_540;
} else {
 lean_dec_ref(x_540);
 x_555 = lean_box(0);
}
if (lean_is_scalar(x_555)) {
 x_556 = lean_alloc_ctor(1, 2, 0);
} else {
 x_556 = x_555;
}
lean_ctor_set(x_556, 0, x_553);
lean_ctor_set(x_556, 1, x_554);
return x_556;
}
}
}
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; 
lean_dec(x_5);
x_557 = lean_ctor_get(x_421, 0);
lean_inc(x_557);
lean_dec(x_421);
x_558 = lean_ctor_get(x_495, 0);
lean_inc(x_558);
lean_dec(x_495);
x_559 = l_Lean_Name_str___override(x_445, x_452);
x_560 = l_Lean_Expr_const___override(x_559, x_444);
lean_inc(x_532);
x_561 = l_Lean_Expr_const___override(x_558, x_532);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_562 = x_532;
} else {
 lean_dec_ref(x_532);
 x_562 = lean_box(0);
}
x_563 = l_Lean_Expr_app___override(x_557, x_561);
if (lean_is_scalar(x_562)) {
 x_564 = lean_alloc_ctor(0, 2, 0);
} else {
 x_564 = x_562;
 lean_ctor_set_tag(x_564, 0);
}
lean_ctor_set(x_564, 0, x_560);
lean_ctor_set(x_564, 1, x_563);
x_565 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_565, 0, x_564);
x_566 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_565, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_565);
x_17 = x_566;
goto block_25;
}
}
case 5:
{
lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; 
lean_dec(x_5);
x_567 = lean_ctor_get(x_421, 0);
lean_inc(x_567);
lean_dec(x_421);
x_568 = lean_ctor_get(x_495, 0);
lean_inc(x_568);
x_569 = lean_ctor_get(x_495, 1);
lean_inc(x_569);
lean_dec(x_495);
x_570 = l_Lean_Name_str___override(x_445, x_452);
x_571 = l_Lean_Expr_const___override(x_570, x_444);
x_572 = l_Lean_Expr_app___override(x_568, x_569);
x_573 = l_Lean_Expr_app___override(x_567, x_572);
x_574 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_574, 0, x_571);
lean_ctor_set(x_574, 1, x_573);
x_575 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_575, 0, x_574);
x_576 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_575, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_575);
x_17 = x_576;
goto block_25;
}
case 6:
{
lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; uint8_t x_581; lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_5);
x_577 = lean_ctor_get(x_421, 0);
lean_inc(x_577);
lean_dec(x_421);
x_578 = lean_ctor_get(x_495, 0);
lean_inc(x_578);
x_579 = lean_ctor_get(x_495, 1);
lean_inc(x_579);
x_580 = lean_ctor_get(x_495, 2);
lean_inc(x_580);
x_581 = lean_ctor_get_uint8(x_495, sizeof(void*)*3 + 8);
lean_dec(x_495);
x_582 = l_Lean_Name_str___override(x_445, x_452);
x_583 = l_Lean_Expr_const___override(x_582, x_444);
x_584 = l_Lean_Expr_lam___override(x_578, x_579, x_580, x_581);
x_585 = l_Lean_Expr_app___override(x_577, x_584);
x_586 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_586, 0, x_583);
lean_ctor_set(x_586, 1, x_585);
x_587 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_587, 0, x_586);
x_588 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_587, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_587);
x_17 = x_588;
goto block_25;
}
case 7:
{
lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; uint8_t x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_599; lean_object* x_600; 
lean_dec(x_5);
x_589 = lean_ctor_get(x_421, 0);
lean_inc(x_589);
lean_dec(x_421);
x_590 = lean_ctor_get(x_495, 0);
lean_inc(x_590);
x_591 = lean_ctor_get(x_495, 1);
lean_inc(x_591);
x_592 = lean_ctor_get(x_495, 2);
lean_inc(x_592);
x_593 = lean_ctor_get_uint8(x_495, sizeof(void*)*3 + 8);
lean_dec(x_495);
x_594 = l_Lean_Name_str___override(x_445, x_452);
x_595 = l_Lean_Expr_const___override(x_594, x_444);
x_596 = l_Lean_Expr_forallE___override(x_590, x_591, x_592, x_593);
x_597 = l_Lean_Expr_app___override(x_589, x_596);
x_598 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_598, 0, x_595);
lean_ctor_set(x_598, 1, x_597);
x_599 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_599, 0, x_598);
x_600 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_599, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_599);
x_17 = x_600;
goto block_25;
}
case 8:
{
lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; uint8_t x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; 
lean_dec(x_5);
x_601 = lean_ctor_get(x_421, 0);
lean_inc(x_601);
lean_dec(x_421);
x_602 = lean_ctor_get(x_495, 0);
lean_inc(x_602);
x_603 = lean_ctor_get(x_495, 1);
lean_inc(x_603);
x_604 = lean_ctor_get(x_495, 2);
lean_inc(x_604);
x_605 = lean_ctor_get(x_495, 3);
lean_inc(x_605);
x_606 = lean_ctor_get_uint8(x_495, sizeof(void*)*4 + 8);
lean_dec(x_495);
x_607 = l_Lean_Name_str___override(x_445, x_452);
x_608 = l_Lean_Expr_const___override(x_607, x_444);
x_609 = l_Lean_Expr_letE___override(x_602, x_603, x_604, x_605, x_606);
x_610 = l_Lean_Expr_app___override(x_601, x_609);
x_611 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_611, 0, x_608);
lean_ctor_set(x_611, 1, x_610);
x_612 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_612, 0, x_611);
x_613 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_612, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_612);
x_17 = x_613;
goto block_25;
}
case 9:
{
lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; 
lean_dec(x_5);
x_614 = lean_ctor_get(x_421, 0);
lean_inc(x_614);
lean_dec(x_421);
x_615 = lean_ctor_get(x_495, 0);
lean_inc(x_615);
lean_dec(x_495);
x_616 = l_Lean_Name_str___override(x_445, x_452);
x_617 = l_Lean_Expr_const___override(x_616, x_444);
x_618 = l_Lean_Expr_lit___override(x_615);
x_619 = l_Lean_Expr_app___override(x_614, x_618);
x_620 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_620, 0, x_617);
lean_ctor_set(x_620, 1, x_619);
x_621 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_621, 0, x_620);
x_622 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_621, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_621);
x_17 = x_622;
goto block_25;
}
case 10:
{
lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; 
lean_dec(x_5);
x_623 = lean_ctor_get(x_421, 0);
lean_inc(x_623);
lean_dec(x_421);
x_624 = lean_ctor_get(x_495, 0);
lean_inc(x_624);
x_625 = lean_ctor_get(x_495, 1);
lean_inc(x_625);
lean_dec(x_495);
x_626 = l_Lean_Name_str___override(x_445, x_452);
x_627 = l_Lean_Expr_const___override(x_626, x_444);
x_628 = l_Lean_Expr_mdata___override(x_624, x_625);
x_629 = l_Lean_Expr_app___override(x_623, x_628);
x_630 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_630, 0, x_627);
lean_ctor_set(x_630, 1, x_629);
x_631 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_631, 0, x_630);
x_632 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_631, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_631);
x_17 = x_632;
goto block_25;
}
default: 
{
lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; 
lean_dec(x_5);
x_633 = lean_ctor_get(x_421, 0);
lean_inc(x_633);
lean_dec(x_421);
x_634 = lean_ctor_get(x_495, 0);
lean_inc(x_634);
x_635 = lean_ctor_get(x_495, 1);
lean_inc(x_635);
x_636 = lean_ctor_get(x_495, 2);
lean_inc(x_636);
lean_dec(x_495);
x_637 = l_Lean_Name_str___override(x_445, x_452);
x_638 = l_Lean_Expr_const___override(x_637, x_444);
x_639 = l_Lean_Expr_proj___override(x_634, x_635, x_636);
x_640 = l_Lean_Expr_app___override(x_633, x_639);
x_641 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_641, 0, x_638);
lean_ctor_set(x_641, 1, x_640);
x_642 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_642, 0, x_641);
x_643 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_642, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_642);
x_17 = x_643;
goto block_25;
}
}
}
case 6:
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; uint8_t x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; 
lean_dec(x_5);
x_644 = lean_ctor_get(x_421, 0);
lean_inc(x_644);
x_645 = lean_ctor_get(x_421, 1);
lean_inc(x_645);
x_646 = lean_ctor_get(x_421, 2);
lean_inc(x_646);
x_647 = lean_ctor_get_uint8(x_421, sizeof(void*)*3 + 8);
lean_dec(x_421);
x_648 = l_Lean_Name_str___override(x_445, x_452);
x_649 = l_Lean_Expr_const___override(x_648, x_444);
x_650 = l_Lean_Expr_lam___override(x_644, x_645, x_646, x_647);
x_651 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_651, 0, x_649);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_652, 0, x_651);
x_653 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_652, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_652);
x_17 = x_653;
goto block_25;
}
case 7:
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; uint8_t x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; 
lean_dec(x_5);
x_654 = lean_ctor_get(x_421, 0);
lean_inc(x_654);
x_655 = lean_ctor_get(x_421, 1);
lean_inc(x_655);
x_656 = lean_ctor_get(x_421, 2);
lean_inc(x_656);
x_657 = lean_ctor_get_uint8(x_421, sizeof(void*)*3 + 8);
lean_dec(x_421);
x_658 = l_Lean_Name_str___override(x_445, x_452);
x_659 = l_Lean_Expr_const___override(x_658, x_444);
x_660 = l_Lean_Expr_forallE___override(x_654, x_655, x_656, x_657);
x_661 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_661, 0, x_659);
lean_ctor_set(x_661, 1, x_660);
x_662 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_662, 0, x_661);
x_663 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_662, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_662);
x_17 = x_663;
goto block_25;
}
case 8:
{
lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; uint8_t x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; 
lean_dec(x_5);
x_664 = lean_ctor_get(x_421, 0);
lean_inc(x_664);
x_665 = lean_ctor_get(x_421, 1);
lean_inc(x_665);
x_666 = lean_ctor_get(x_421, 2);
lean_inc(x_666);
x_667 = lean_ctor_get(x_421, 3);
lean_inc(x_667);
x_668 = lean_ctor_get_uint8(x_421, sizeof(void*)*4 + 8);
lean_dec(x_421);
x_669 = l_Lean_Name_str___override(x_445, x_452);
x_670 = l_Lean_Expr_const___override(x_669, x_444);
x_671 = l_Lean_Expr_letE___override(x_664, x_665, x_666, x_667, x_668);
x_672 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
x_673 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_673, 0, x_672);
x_674 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_673, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_673);
x_17 = x_674;
goto block_25;
}
case 9:
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
lean_dec(x_5);
x_675 = lean_ctor_get(x_421, 0);
lean_inc(x_675);
lean_dec(x_421);
x_676 = l_Lean_Name_str___override(x_445, x_452);
x_677 = l_Lean_Expr_const___override(x_676, x_444);
x_678 = l_Lean_Expr_lit___override(x_675);
x_679 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_679, 0, x_677);
lean_ctor_set(x_679, 1, x_678);
x_680 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_680, 0, x_679);
x_681 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_680, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_680);
x_17 = x_681;
goto block_25;
}
case 10:
{
lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; lean_object* x_687; lean_object* x_688; lean_object* x_689; 
lean_dec(x_5);
x_682 = lean_ctor_get(x_421, 0);
lean_inc(x_682);
x_683 = lean_ctor_get(x_421, 1);
lean_inc(x_683);
lean_dec(x_421);
x_684 = l_Lean_Name_str___override(x_445, x_452);
x_685 = l_Lean_Expr_const___override(x_684, x_444);
x_686 = l_Lean_Expr_mdata___override(x_682, x_683);
x_687 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_687, 0, x_685);
lean_ctor_set(x_687, 1, x_686);
x_688 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_688, 0, x_687);
x_689 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_688, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_688);
x_17 = x_689;
goto block_25;
}
default: 
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; 
lean_dec(x_5);
x_690 = lean_ctor_get(x_421, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_421, 1);
lean_inc(x_691);
x_692 = lean_ctor_get(x_421, 2);
lean_inc(x_692);
lean_dec(x_421);
x_693 = l_Lean_Name_str___override(x_445, x_452);
x_694 = l_Lean_Expr_const___override(x_693, x_444);
x_695 = l_Lean_Expr_proj___override(x_690, x_691, x_692);
x_696 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_696, 0, x_694);
lean_ctor_set(x_696, 1, x_695);
x_697 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_697, 0, x_696);
x_698 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_697, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_697);
x_17 = x_698;
goto block_25;
}
}
}
else
{
lean_object* x_699; lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_5);
x_699 = l_Lean_Name_str___override(x_445, x_452);
lean_inc(x_444);
x_700 = l_Lean_Expr_const___override(x_699, x_444);
if (lean_is_exclusive(x_444)) {
 lean_ctor_release(x_444, 0);
 lean_ctor_release(x_444, 1);
 x_701 = x_444;
} else {
 lean_dec_ref(x_444);
 x_701 = lean_box(0);
}
if (lean_is_scalar(x_701)) {
 x_702 = lean_alloc_ctor(0, 2, 0);
} else {
 x_702 = x_701;
 lean_ctor_set_tag(x_702, 0);
}
lean_ctor_set(x_702, 0, x_700);
lean_ctor_set(x_702, 1, x_421);
x_703 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_703, 0, x_702);
x_704 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_703, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_703);
x_17 = x_704;
goto block_25;
}
}
}
case 1:
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; 
lean_dec(x_5);
x_705 = lean_ctor_get(x_443, 1);
lean_inc(x_705);
lean_dec(x_443);
x_706 = lean_ctor_get(x_450, 0);
lean_inc(x_706);
x_707 = lean_ctor_get(x_450, 1);
lean_inc(x_707);
lean_dec(x_450);
x_708 = l_Lean_Name_str___override(x_706, x_707);
x_709 = l_Lean_Name_str___override(x_708, x_705);
x_710 = l_Lean_Expr_const___override(x_709, x_444);
x_711 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_711, 0, x_710);
lean_ctor_set(x_711, 1, x_421);
x_712 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_712, 0, x_711);
x_713 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_712, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_712);
x_17 = x_713;
goto block_25;
}
default: 
{
lean_object* x_714; lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; lean_object* x_721; lean_object* x_722; 
lean_dec(x_5);
x_714 = lean_ctor_get(x_443, 1);
lean_inc(x_714);
lean_dec(x_443);
x_715 = lean_ctor_get(x_450, 0);
lean_inc(x_715);
x_716 = lean_ctor_get(x_450, 1);
lean_inc(x_716);
lean_dec(x_450);
x_717 = l_Lean_Name_num___override(x_715, x_716);
x_718 = l_Lean_Name_str___override(x_717, x_714);
x_719 = l_Lean_Expr_const___override(x_718, x_444);
x_720 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_720, 0, x_719);
lean_ctor_set(x_720, 1, x_421);
x_721 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_721, 0, x_720);
x_722 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_721, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_721);
x_17 = x_722;
goto block_25;
}
}
}
default: 
{
lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; 
lean_dec(x_446);
lean_dec(x_5);
x_723 = lean_ctor_get(x_443, 0);
lean_inc(x_723);
x_724 = lean_ctor_get(x_443, 1);
lean_inc(x_724);
lean_dec(x_443);
x_725 = l_Lean_Name_num___override(x_723, x_724);
x_726 = l_Lean_Expr_const___override(x_725, x_444);
x_727 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_727, 0, x_726);
lean_ctor_set(x_727, 1, x_421);
x_728 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_728, 0, x_727);
x_729 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_728, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_728);
x_17 = x_729;
goto block_25;
}
}
}
case 5:
{
lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; 
lean_dec(x_5);
x_730 = lean_ctor_get(x_420, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_420, 1);
lean_inc(x_731);
lean_dec(x_420);
x_732 = l_Lean_Expr_app___override(x_730, x_731);
x_733 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_733, 0, x_732);
lean_ctor_set(x_733, 1, x_421);
x_734 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_734, 0, x_733);
x_735 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_734, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_734);
x_17 = x_735;
goto block_25;
}
case 6:
{
lean_object* x_736; lean_object* x_737; lean_object* x_738; uint8_t x_739; lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_5);
x_736 = lean_ctor_get(x_420, 0);
lean_inc(x_736);
x_737 = lean_ctor_get(x_420, 1);
lean_inc(x_737);
x_738 = lean_ctor_get(x_420, 2);
lean_inc(x_738);
x_739 = lean_ctor_get_uint8(x_420, sizeof(void*)*3 + 8);
lean_dec(x_420);
x_740 = l_Lean_Expr_lam___override(x_736, x_737, x_738, x_739);
x_741 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_741, 0, x_740);
lean_ctor_set(x_741, 1, x_421);
x_742 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_742, 0, x_741);
x_743 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_742, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_742);
x_17 = x_743;
goto block_25;
}
case 7:
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; uint8_t x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_751; 
lean_dec(x_5);
x_744 = lean_ctor_get(x_420, 0);
lean_inc(x_744);
x_745 = lean_ctor_get(x_420, 1);
lean_inc(x_745);
x_746 = lean_ctor_get(x_420, 2);
lean_inc(x_746);
x_747 = lean_ctor_get_uint8(x_420, sizeof(void*)*3 + 8);
lean_dec(x_420);
x_748 = l_Lean_Expr_forallE___override(x_744, x_745, x_746, x_747);
x_749 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_749, 0, x_748);
lean_ctor_set(x_749, 1, x_421);
x_750 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_750, 0, x_749);
x_751 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_750, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_750);
x_17 = x_751;
goto block_25;
}
case 8:
{
lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; uint8_t x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; 
lean_dec(x_5);
x_752 = lean_ctor_get(x_420, 0);
lean_inc(x_752);
x_753 = lean_ctor_get(x_420, 1);
lean_inc(x_753);
x_754 = lean_ctor_get(x_420, 2);
lean_inc(x_754);
x_755 = lean_ctor_get(x_420, 3);
lean_inc(x_755);
x_756 = lean_ctor_get_uint8(x_420, sizeof(void*)*4 + 8);
lean_dec(x_420);
x_757 = l_Lean_Expr_letE___override(x_752, x_753, x_754, x_755, x_756);
x_758 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_758, 0, x_757);
lean_ctor_set(x_758, 1, x_421);
x_759 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_759, 0, x_758);
x_760 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_759, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_759);
x_17 = x_760;
goto block_25;
}
case 9:
{
lean_object* x_761; lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; 
lean_dec(x_5);
x_761 = lean_ctor_get(x_420, 0);
lean_inc(x_761);
lean_dec(x_420);
x_762 = l_Lean_Expr_lit___override(x_761);
x_763 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_763, 0, x_762);
lean_ctor_set(x_763, 1, x_421);
x_764 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_764, 0, x_763);
x_765 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_764, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_764);
x_17 = x_765;
goto block_25;
}
case 10:
{
lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; 
lean_dec(x_5);
x_766 = lean_ctor_get(x_420, 0);
lean_inc(x_766);
x_767 = lean_ctor_get(x_420, 1);
lean_inc(x_767);
lean_dec(x_420);
x_768 = l_Lean_Expr_mdata___override(x_766, x_767);
x_769 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_769, 0, x_768);
lean_ctor_set(x_769, 1, x_421);
x_770 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_770, 0, x_769);
x_771 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_770, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_770);
x_17 = x_771;
goto block_25;
}
default: 
{
lean_object* x_772; lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; 
lean_dec(x_5);
x_772 = lean_ctor_get(x_420, 0);
lean_inc(x_772);
x_773 = lean_ctor_get(x_420, 1);
lean_inc(x_773);
x_774 = lean_ctor_get(x_420, 2);
lean_inc(x_774);
lean_dec(x_420);
x_775 = l_Lean_Expr_proj___override(x_772, x_773, x_774);
x_776 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_776, 0, x_775);
lean_ctor_set(x_776, 1, x_421);
x_777 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_777, 0, x_776);
x_778 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_777, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_777);
x_17 = x_778;
goto block_25;
}
}
}
else
{
lean_object* x_779; 
lean_dec(x_421);
lean_dec(x_420);
lean_dec(x_5);
x_779 = lean_box(0);
x_417 = x_779;
goto block_419;
}
}
else
{
lean_object* x_780; 
lean_dec(x_414);
lean_dec(x_5);
x_780 = lean_box(0);
x_417 = x_780;
goto block_419;
}
block_419:
{
lean_object* x_418; 
x_418 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum_spec__0___redArg___lam__0(x_416, x_417, x_6, x_7, x_8, x_9, x_415);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_417);
x_17 = x_418;
goto block_25;
}
}
}
else
{
uint8_t x_781; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_781 = !lean_is_exclusive(x_33);
if (x_781 == 0)
{
return x_33;
}
else
{
lean_object* x_782; lean_object* x_783; lean_object* x_784; 
x_782 = lean_ctor_get(x_33, 0);
x_783 = lean_ctor_get(x_33, 1);
lean_inc(x_783);
lean_inc(x_782);
lean_dec(x_33);
x_784 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_784, 0, x_782);
lean_ctor_set(x_784, 1, x_783);
return x_784;
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
block_25:
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
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
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_unsigned_to_nat(1u);
if (lean_obj_tag(x_3) == 5)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_dec(x_3);
x_10 = lean_array_set(x_4, x_5, x_9);
x_11 = lean_nat_sub(x_5, x_7);
lean_dec(x_5);
x_3 = x_8;
x_4 = x_10;
x_5 = x_11;
goto _start;
}
else
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; uint8_t x_23; 
lean_dec(x_5);
x_13 = l_Lean_instInhabitedExpr;
x_14 = lean_unsigned_to_nat(0u);
x_23 = lean_expr_eqv(x_3, x_2);
lean_dec(x_3);
if (x_23 == 0)
{
x_15 = x_23;
goto block_22;
}
else
{
lean_object* x_24; uint8_t x_25; 
x_24 = lean_array_get_size(x_4);
x_25 = lean_nat_dec_eq(x_24, x_7);
lean_dec(x_24);
x_15 = x_25;
goto block_22;
}
block_22:
{
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
x_16 = lean_box(x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_6);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_array_get(x_13, x_4, x_14);
lean_dec(x_4);
x_19 = lean_expr_eqv(x_18, x_1);
lean_dec(x_18);
x_20 = lean_box(x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_6);
return x_21;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_array_get_size(x_7);
x_15 = lean_nat_dec_eq(x_14, x_1);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
x_16 = lean_box(x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_get(x_3, x_7, x_4);
lean_inc(x_18);
x_19 = lean_infer_type(x_18, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = l_Lean_Expr_isConstOf(x_21, x_5);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_18);
lean_dec(x_8);
x_23 = lean_box(x_2);
lean_ctor_set(x_19, 0, x_23);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; 
x_24 = lean_box(0);
x_25 = l_Lean_Expr_sort___override(x_24);
x_26 = l_Lean_Expr_getAppNumArgs(x_8);
lean_inc(x_26);
x_27 = lean_mk_array(x_26, x_25);
x_28 = lean_nat_sub(x_26, x_1);
lean_dec(x_26);
x_29 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__2(x_18, x_6, x_8, x_27, x_28);
lean_dec(x_18);
x_30 = lean_box(x_29);
lean_ctor_set(x_19, 0, x_30);
return x_19;
}
}
else
{
lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_31 = lean_ctor_get(x_19, 0);
x_32 = lean_ctor_get(x_19, 1);
lean_inc(x_32);
lean_inc(x_31);
lean_dec(x_19);
x_33 = l_Lean_Expr_isConstOf(x_31, x_5);
lean_dec(x_31);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_18);
lean_dec(x_8);
x_34 = lean_box(x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; 
x_36 = lean_box(0);
x_37 = l_Lean_Expr_sort___override(x_36);
x_38 = l_Lean_Expr_getAppNumArgs(x_8);
lean_inc(x_38);
x_39 = lean_mk_array(x_38, x_37);
x_40 = lean_nat_sub(x_38, x_1);
lean_dec(x_38);
x_41 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__2(x_18, x_6, x_8, x_39, x_40);
lean_dec(x_18);
x_42 = lean_box(x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_32);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_18);
lean_dec(x_8);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_array_get_size(x_6);
x_14 = lean_unsigned_to_nat(2u);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
lean_inc(x_1);
x_16 = lean_array_get(x_1, x_6, x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_16);
x_17 = lean_infer_type(x_16, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = l_Lean_Expr_constName_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_17);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
lean_inc(x_23);
x_25 = l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0(x_23, x_8, x_9, x_10, x_11, x_20);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
uint8_t x_28; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_25);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_25, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_25, 0, x_30);
return x_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_25, 1);
lean_inc(x_31);
lean_dec(x_25);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
else
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_25, 1);
lean_inc(x_34);
lean_dec(x_25);
lean_inc(x_23);
x_35 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_23, x_8, x_9, x_10, x_11, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
if (lean_obj_tag(x_36) == 5)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_1);
x_39 = lean_array_get(x_1, x_6, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_39);
x_40 = lean_infer_type(x_39, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
if (lean_obj_tag(x_41) == 7)
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_40);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_ctor_get(x_40, 1);
x_44 = lean_ctor_get(x_40, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_41, 2);
lean_inc(x_46);
lean_dec(x_41);
x_47 = l_Lean_Expr_hasLooseBVars(x_46);
if (x_47 == 0)
{
switch (lean_obj_tag(x_45)) {
case 0:
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_ctor_get(x_45, 0);
lean_inc(x_48);
lean_dec(x_45);
x_49 = l_Lean_Expr_bvar___override(x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_51 = lean_alloc_ctor(1, 1, 0);
} else {
 x_51 = x_24;
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_apply_6(x_4, x_51, x_8, x_9, x_10, x_11, x_43);
return x_52;
}
case 1:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
x_54 = l_Lean_Expr_fvar___override(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_24;
}
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_apply_6(x_4, x_56, x_8, x_9, x_10, x_11, x_43);
return x_57;
}
case 2:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_58 = lean_ctor_get(x_45, 0);
lean_inc(x_58);
lean_dec(x_45);
x_59 = l_Lean_Expr_mvar___override(x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_61 = lean_alloc_ctor(1, 1, 0);
} else {
 x_61 = x_24;
}
lean_ctor_set(x_61, 0, x_60);
x_62 = lean_apply_6(x_4, x_61, x_8, x_9, x_10, x_11, x_43);
return x_62;
}
case 3:
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_63 = lean_ctor_get(x_45, 0);
lean_inc(x_63);
lean_dec(x_45);
x_64 = l_Lean_Expr_sort___override(x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_24;
}
lean_ctor_set(x_66, 0, x_65);
x_67 = lean_apply_6(x_4, x_66, x_8, x_9, x_10, x_11, x_43);
return x_67;
}
case 4:
{
lean_object* x_68; 
x_68 = lean_ctor_get(x_45, 1);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
switch (lean_obj_tag(x_46)) {
case 0:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_69 = lean_ctor_get(x_45, 0);
lean_inc(x_69);
lean_dec(x_45);
x_70 = lean_ctor_get(x_46, 0);
lean_inc(x_70);
lean_dec(x_46);
x_71 = l_Lean_Expr_const___override(x_69, x_68);
x_72 = l_Lean_Expr_bvar___override(x_70);
x_73 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
if (lean_is_scalar(x_24)) {
 x_74 = lean_alloc_ctor(1, 1, 0);
} else {
 x_74 = x_24;
}
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_apply_6(x_4, x_74, x_8, x_9, x_10, x_11, x_43);
return x_75;
}
case 1:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_76 = lean_ctor_get(x_45, 0);
lean_inc(x_76);
lean_dec(x_45);
x_77 = lean_ctor_get(x_46, 0);
lean_inc(x_77);
lean_dec(x_46);
x_78 = l_Lean_Expr_const___override(x_76, x_68);
x_79 = l_Lean_Expr_fvar___override(x_77);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
if (lean_is_scalar(x_24)) {
 x_81 = lean_alloc_ctor(1, 1, 0);
} else {
 x_81 = x_24;
}
lean_ctor_set(x_81, 0, x_80);
x_82 = lean_apply_6(x_4, x_81, x_8, x_9, x_10, x_11, x_43);
return x_82;
}
case 2:
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_83 = lean_ctor_get(x_45, 0);
lean_inc(x_83);
lean_dec(x_45);
x_84 = lean_ctor_get(x_46, 0);
lean_inc(x_84);
lean_dec(x_46);
x_85 = l_Lean_Expr_const___override(x_83, x_68);
x_86 = l_Lean_Expr_mvar___override(x_84);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_85);
lean_ctor_set(x_87, 1, x_86);
if (lean_is_scalar(x_24)) {
 x_88 = lean_alloc_ctor(1, 1, 0);
} else {
 x_88 = x_24;
}
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_apply_6(x_4, x_88, x_8, x_9, x_10, x_11, x_43);
return x_89;
}
case 3:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_45, 0);
lean_inc(x_90);
lean_dec(x_45);
x_91 = lean_ctor_get(x_46, 0);
lean_inc(x_91);
lean_dec(x_46);
lean_inc(x_90);
x_92 = l_Lean_Expr_const___override(x_90, x_68);
x_93 = lean_box(0);
x_94 = l_Lean_Expr_sort___override(x_93);
switch (lean_obj_tag(x_91)) {
case 0:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
lean_dec(x_90);
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_92);
lean_ctor_set(x_95, 1, x_94);
if (lean_is_scalar(x_24)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_24;
}
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_apply_6(x_4, x_96, x_8, x_9, x_10, x_11, x_43);
return x_97;
}
case 1:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
lean_dec(x_94);
lean_dec(x_90);
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_98 = lean_ctor_get(x_91, 0);
lean_inc(x_98);
lean_dec(x_91);
x_99 = l_Lean_Level_succ___override(x_98);
x_100 = l_Lean_Expr_sort___override(x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_92);
lean_ctor_set(x_101, 1, x_100);
if (lean_is_scalar(x_24)) {
 x_102 = lean_alloc_ctor(1, 1, 0);
} else {
 x_102 = x_24;
}
lean_ctor_set(x_102, 0, x_101);
x_103 = lean_apply_6(x_4, x_102, x_8, x_9, x_10, x_11, x_43);
return x_103;
}
case 2:
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_94);
lean_dec(x_90);
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_104 = lean_ctor_get(x_91, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_91, 1);
lean_inc(x_105);
lean_dec(x_91);
x_106 = l_Lean_Level_max___override(x_104, x_105);
x_107 = l_Lean_Expr_sort___override(x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_92);
lean_ctor_set(x_108, 1, x_107);
if (lean_is_scalar(x_24)) {
 x_109 = lean_alloc_ctor(1, 1, 0);
} else {
 x_109 = x_24;
}
lean_ctor_set(x_109, 0, x_108);
x_110 = lean_apply_6(x_4, x_109, x_8, x_9, x_10, x_11, x_43);
return x_110;
}
case 3:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_94);
lean_dec(x_90);
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_111 = lean_ctor_get(x_91, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_91, 1);
lean_inc(x_112);
lean_dec(x_91);
x_113 = l_Lean_Level_imax___override(x_111, x_112);
x_114 = l_Lean_Expr_sort___override(x_113);
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_92);
lean_ctor_set(x_115, 1, x_114);
if (lean_is_scalar(x_24)) {
 x_116 = lean_alloc_ctor(1, 1, 0);
} else {
 x_116 = x_24;
}
lean_ctor_set(x_116, 0, x_115);
x_117 = lean_apply_6(x_4, x_116, x_8, x_9, x_10, x_11, x_43);
return x_117;
}
case 4:
{
uint8_t x_118; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_4);
x_118 = lean_name_eq(x_90, x_23);
lean_dec(x_90);
if (x_118 == 0)
{
lean_object* x_119; 
lean_dec(x_94);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_box(0);
lean_ctor_set(x_40, 0, x_119);
return x_40;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
lean_free_object(x_40);
x_120 = l_Lean_Expr_getAppNumArgs(x_7);
lean_inc(x_120);
x_121 = lean_mk_array(x_120, x_94);
x_122 = lean_nat_sub(x_120, x_2);
lean_dec(x_120);
x_123 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg(x_16, x_39, x_7, x_121, x_122, x_43);
lean_dec(x_16);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_unbox(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
uint8_t x_126; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_126 = !lean_is_exclusive(x_123);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = lean_ctor_get(x_123, 0);
lean_dec(x_127);
x_128 = lean_box(0);
lean_ctor_set(x_123, 0, x_128);
return x_123;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_123, 1);
lean_inc(x_129);
lean_dec(x_123);
x_130 = lean_box(0);
x_131 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_131, 0, x_130);
lean_ctor_set(x_131, 1, x_129);
return x_131;
}
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_210; lean_object* x_211; uint8_t x_212; 
x_132 = lean_ctor_get(x_123, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_133 = x_123;
} else {
 lean_dec_ref(x_123);
 x_133 = lean_box(0);
}
x_134 = lean_box(x_15);
lean_inc(x_39);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_135 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1___boxed), 13, 6);
lean_closure_set(x_135, 0, x_2);
lean_closure_set(x_135, 1, x_134);
lean_closure_set(x_135, 2, x_1);
lean_closure_set(x_135, 3, x_3);
lean_closure_set(x_135, 4, x_23);
lean_closure_set(x_135, 5, x_39);
x_210 = l_Lean_InductiveVal_numCtors(x_38);
x_211 = lean_nat_add(x_210, x_14);
x_212 = lean_nat_dec_eq(x_13, x_211);
lean_dec(x_211);
if (x_212 == 0)
{
lean_dec(x_210);
x_136 = x_8;
x_137 = x_9;
x_138 = x_10;
x_139 = x_11;
x_140 = x_132;
goto block_209;
}
else
{
lean_object* x_213; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_38);
lean_inc(x_5);
x_213 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum(x_5, x_38, x_6, x_210, x_39, x_8, x_9, x_10, x_11, x_132);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; 
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_136 = x_8;
x_137 = x_9;
x_138 = x_10;
x_139 = x_11;
x_140 = x_215;
goto block_209;
}
else
{
lean_dec(x_214);
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_213;
}
}
else
{
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_213;
}
}
block_209:
{
uint8_t x_141; 
x_141 = lean_nat_dec_lt(x_14, x_13);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_142 = lean_box(0);
if (lean_is_scalar(x_133)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_133;
}
lean_ctor_set(x_143, 0, x_142);
lean_ctor_set(x_143, 1, x_140);
return x_143;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; 
lean_dec(x_133);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_sub(x_13, x_144);
x_146 = lean_mk_empty_array_with_capacity(x_145);
lean_inc(x_2);
lean_inc(x_3);
x_147 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_147, 0, x_3);
lean_ctor_set(x_147, 1, x_145);
lean_ctor_set(x_147, 2, x_2);
x_148 = lean_box(0);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_148);
lean_ctor_set(x_149, 1, x_146);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
x_150 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg(x_6, x_39, x_147, x_149, x_3, x_136, x_137, x_138, x_139, x_140);
lean_dec(x_147);
lean_dec(x_39);
if (lean_obj_tag(x_150) == 0)
{
lean_object* x_151; lean_object* x_152; 
x_151 = lean_ctor_get(x_150, 0);
lean_inc(x_151);
x_152 = lean_ctor_get(x_151, 0);
lean_inc(x_152);
if (lean_obj_tag(x_152) == 0)
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_ctor_get(x_150, 1);
lean_inc(x_153);
lean_dec(x_150);
x_154 = lean_nat_sub(x_13, x_2);
lean_dec(x_2);
lean_dec(x_13);
x_155 = lean_array_get(x_1, x_6, x_154);
lean_dec(x_154);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
x_156 = lean_infer_type(x_155, x_136, x_137, x_138, x_139, x_153);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
lean_inc(x_139);
lean_inc(x_138);
lean_inc(x_137);
lean_inc(x_136);
x_159 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_157, x_135, x_15, x_136, x_137, x_138, x_139, x_158);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_unbox(x_160);
lean_dec(x_160);
if (x_161 == 0)
{
uint8_t x_162; 
lean_dec(x_151);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_5);
x_162 = !lean_is_exclusive(x_159);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; 
x_163 = lean_ctor_get(x_159, 0);
lean_dec(x_163);
x_164 = lean_box(0);
lean_ctor_set(x_159, 0, x_164);
return x_159;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_165 = lean_ctor_get(x_159, 1);
lean_inc(x_165);
lean_dec(x_159);
x_166 = lean_box(0);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_165);
return x_167;
}
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_159, 1);
lean_inc(x_168);
lean_dec(x_159);
x_169 = lean_ctor_get(x_151, 1);
lean_inc(x_169);
lean_dec(x_151);
lean_inc(x_169);
lean_inc(x_38);
x_170 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault(x_5, x_38, x_169, x_136, x_137, x_138, x_139, x_168);
if (lean_obj_tag(x_170) == 0)
{
lean_object* x_171; uint8_t x_172; 
x_171 = lean_ctor_get(x_170, 0);
lean_inc(x_171);
x_172 = lean_unbox(x_171);
lean_dec(x_171);
if (x_172 == 0)
{
uint8_t x_173; 
lean_dec(x_169);
lean_dec(x_38);
lean_dec(x_24);
x_173 = !lean_is_exclusive(x_170);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = lean_ctor_get(x_170, 0);
lean_dec(x_174);
x_175 = lean_box(0);
lean_ctor_set(x_170, 0, x_175);
return x_170;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_170, 1);
lean_inc(x_176);
lean_dec(x_170);
x_177 = lean_box(0);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_177);
lean_ctor_set(x_178, 1, x_176);
return x_178;
}
}
else
{
uint8_t x_179; 
x_179 = !lean_is_exclusive(x_170);
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; 
x_180 = lean_ctor_get(x_170, 0);
lean_dec(x_180);
x_181 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_181, 0, x_38);
lean_ctor_set(x_181, 1, x_169);
if (lean_is_scalar(x_24)) {
 x_182 = lean_alloc_ctor(1, 1, 0);
} else {
 x_182 = x_24;
}
lean_ctor_set(x_182, 0, x_181);
lean_ctor_set(x_170, 0, x_182);
return x_170;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_183 = lean_ctor_get(x_170, 1);
lean_inc(x_183);
lean_dec(x_170);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_38);
lean_ctor_set(x_184, 1, x_169);
if (lean_is_scalar(x_24)) {
 x_185 = lean_alloc_ctor(1, 1, 0);
} else {
 x_185 = x_24;
}
lean_ctor_set(x_185, 0, x_184);
x_186 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_186, 0, x_185);
lean_ctor_set(x_186, 1, x_183);
return x_186;
}
}
}
else
{
uint8_t x_187; 
lean_dec(x_169);
lean_dec(x_38);
lean_dec(x_24);
x_187 = !lean_is_exclusive(x_170);
if (x_187 == 0)
{
return x_170;
}
else
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; 
x_188 = lean_ctor_get(x_170, 0);
x_189 = lean_ctor_get(x_170, 1);
lean_inc(x_189);
lean_inc(x_188);
lean_dec(x_170);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
return x_190;
}
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_151);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_5);
x_191 = !lean_is_exclusive(x_159);
if (x_191 == 0)
{
return x_159;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_159, 0);
x_193 = lean_ctor_get(x_159, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_159);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
else
{
uint8_t x_195; 
lean_dec(x_151);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_5);
x_195 = !lean_is_exclusive(x_156);
if (x_195 == 0)
{
return x_156;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_156, 0);
x_197 = lean_ctor_get(x_156, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_156);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
uint8_t x_199; 
lean_dec(x_151);
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_199 = !lean_is_exclusive(x_150);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; 
x_200 = lean_ctor_get(x_150, 0);
lean_dec(x_200);
x_201 = lean_ctor_get(x_152, 0);
lean_inc(x_201);
lean_dec(x_152);
lean_ctor_set(x_150, 0, x_201);
return x_150;
}
else
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_150, 1);
lean_inc(x_202);
lean_dec(x_150);
x_203 = lean_ctor_get(x_152, 0);
lean_inc(x_203);
lean_dec(x_152);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_204, 1, x_202);
return x_204;
}
}
}
else
{
uint8_t x_205; 
lean_dec(x_139);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_150);
if (x_205 == 0)
{
return x_150;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_150, 0);
x_207 = lean_ctor_get(x_150, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_150);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
}
}
}
default: 
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_94);
lean_dec(x_90);
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_216 = lean_ctor_get(x_91, 0);
lean_inc(x_216);
lean_dec(x_91);
x_217 = l_Lean_Level_mvar___override(x_216);
x_218 = l_Lean_Expr_sort___override(x_217);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_92);
lean_ctor_set(x_219, 1, x_218);
if (lean_is_scalar(x_24)) {
 x_220 = lean_alloc_ctor(1, 1, 0);
} else {
 x_220 = x_24;
}
lean_ctor_set(x_220, 0, x_219);
x_221 = lean_apply_6(x_4, x_220, x_8, x_9, x_10, x_11, x_43);
return x_221;
}
}
}
case 4:
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_222 = lean_ctor_get(x_45, 0);
lean_inc(x_222);
lean_dec(x_45);
x_223 = lean_ctor_get(x_46, 0);
lean_inc(x_223);
x_224 = lean_ctor_get(x_46, 1);
lean_inc(x_224);
lean_dec(x_46);
x_225 = l_Lean_Expr_const___override(x_222, x_68);
x_226 = l_Lean_Expr_const___override(x_223, x_224);
x_227 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_227, 0, x_225);
lean_ctor_set(x_227, 1, x_226);
if (lean_is_scalar(x_24)) {
 x_228 = lean_alloc_ctor(1, 1, 0);
} else {
 x_228 = x_24;
}
lean_ctor_set(x_228, 0, x_227);
x_229 = lean_apply_6(x_4, x_228, x_8, x_9, x_10, x_11, x_43);
return x_229;
}
case 5:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_230 = lean_ctor_get(x_45, 0);
lean_inc(x_230);
lean_dec(x_45);
x_231 = lean_ctor_get(x_46, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_46, 1);
lean_inc(x_232);
lean_dec(x_46);
x_233 = l_Lean_Expr_const___override(x_230, x_68);
x_234 = l_Lean_Expr_app___override(x_231, x_232);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_233);
lean_ctor_set(x_235, 1, x_234);
if (lean_is_scalar(x_24)) {
 x_236 = lean_alloc_ctor(1, 1, 0);
} else {
 x_236 = x_24;
}
lean_ctor_set(x_236, 0, x_235);
x_237 = lean_apply_6(x_4, x_236, x_8, x_9, x_10, x_11, x_43);
return x_237;
}
case 6:
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; uint8_t x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_238 = lean_ctor_get(x_45, 0);
lean_inc(x_238);
lean_dec(x_45);
x_239 = lean_ctor_get(x_46, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_46, 1);
lean_inc(x_240);
x_241 = lean_ctor_get(x_46, 2);
lean_inc(x_241);
x_242 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_243 = l_Lean_Expr_const___override(x_238, x_68);
x_244 = l_Lean_Expr_lam___override(x_239, x_240, x_241, x_242);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_243);
lean_ctor_set(x_245, 1, x_244);
if (lean_is_scalar(x_24)) {
 x_246 = lean_alloc_ctor(1, 1, 0);
} else {
 x_246 = x_24;
}
lean_ctor_set(x_246, 0, x_245);
x_247 = lean_apply_6(x_4, x_246, x_8, x_9, x_10, x_11, x_43);
return x_247;
}
case 7:
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; uint8_t x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_248 = lean_ctor_get(x_45, 0);
lean_inc(x_248);
lean_dec(x_45);
x_249 = lean_ctor_get(x_46, 0);
lean_inc(x_249);
x_250 = lean_ctor_get(x_46, 1);
lean_inc(x_250);
x_251 = lean_ctor_get(x_46, 2);
lean_inc(x_251);
x_252 = lean_ctor_get_uint8(x_46, sizeof(void*)*3 + 8);
lean_dec(x_46);
x_253 = l_Lean_Expr_const___override(x_248, x_68);
x_254 = l_Lean_Expr_forallE___override(x_249, x_250, x_251, x_252);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_253);
lean_ctor_set(x_255, 1, x_254);
if (lean_is_scalar(x_24)) {
 x_256 = lean_alloc_ctor(1, 1, 0);
} else {
 x_256 = x_24;
}
lean_ctor_set(x_256, 0, x_255);
x_257 = lean_apply_6(x_4, x_256, x_8, x_9, x_10, x_11, x_43);
return x_257;
}
case 8:
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; uint8_t x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_258 = lean_ctor_get(x_45, 0);
lean_inc(x_258);
lean_dec(x_45);
x_259 = lean_ctor_get(x_46, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_46, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_46, 2);
lean_inc(x_261);
x_262 = lean_ctor_get(x_46, 3);
lean_inc(x_262);
x_263 = lean_ctor_get_uint8(x_46, sizeof(void*)*4 + 8);
lean_dec(x_46);
x_264 = l_Lean_Expr_const___override(x_258, x_68);
x_265 = l_Lean_Expr_letE___override(x_259, x_260, x_261, x_262, x_263);
x_266 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_266, 0, x_264);
lean_ctor_set(x_266, 1, x_265);
if (lean_is_scalar(x_24)) {
 x_267 = lean_alloc_ctor(1, 1, 0);
} else {
 x_267 = x_24;
}
lean_ctor_set(x_267, 0, x_266);
x_268 = lean_apply_6(x_4, x_267, x_8, x_9, x_10, x_11, x_43);
return x_268;
}
case 9:
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_269 = lean_ctor_get(x_45, 0);
lean_inc(x_269);
lean_dec(x_45);
x_270 = lean_ctor_get(x_46, 0);
lean_inc(x_270);
lean_dec(x_46);
x_271 = l_Lean_Expr_const___override(x_269, x_68);
x_272 = l_Lean_Expr_lit___override(x_270);
x_273 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_273, 0, x_271);
lean_ctor_set(x_273, 1, x_272);
if (lean_is_scalar(x_24)) {
 x_274 = lean_alloc_ctor(1, 1, 0);
} else {
 x_274 = x_24;
}
lean_ctor_set(x_274, 0, x_273);
x_275 = lean_apply_6(x_4, x_274, x_8, x_9, x_10, x_11, x_43);
return x_275;
}
case 10:
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_276 = lean_ctor_get(x_45, 0);
lean_inc(x_276);
lean_dec(x_45);
x_277 = lean_ctor_get(x_46, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_46, 1);
lean_inc(x_278);
lean_dec(x_46);
x_279 = l_Lean_Expr_const___override(x_276, x_68);
x_280 = l_Lean_Expr_mdata___override(x_277, x_278);
x_281 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
if (lean_is_scalar(x_24)) {
 x_282 = lean_alloc_ctor(1, 1, 0);
} else {
 x_282 = x_24;
}
lean_ctor_set(x_282, 0, x_281);
x_283 = lean_apply_6(x_4, x_282, x_8, x_9, x_10, x_11, x_43);
return x_283;
}
default: 
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_284 = lean_ctor_get(x_45, 0);
lean_inc(x_284);
lean_dec(x_45);
x_285 = lean_ctor_get(x_46, 0);
lean_inc(x_285);
x_286 = lean_ctor_get(x_46, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_46, 2);
lean_inc(x_287);
lean_dec(x_46);
x_288 = l_Lean_Expr_const___override(x_284, x_68);
x_289 = l_Lean_Expr_proj___override(x_285, x_286, x_287);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_288);
lean_ctor_set(x_290, 1, x_289);
if (lean_is_scalar(x_24)) {
 x_291 = lean_alloc_ctor(1, 1, 0);
} else {
 x_291 = x_24;
}
lean_ctor_set(x_291, 0, x_290);
x_292 = lean_apply_6(x_4, x_291, x_8, x_9, x_10, x_11, x_43);
return x_292;
}
}
}
else
{
lean_object* x_293; lean_object* x_294; uint8_t x_295; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_293 = lean_ctor_get(x_45, 0);
lean_inc(x_293);
lean_dec(x_45);
lean_inc(x_68);
x_294 = l_Lean_Expr_const___override(x_293, x_68);
x_295 = !lean_is_exclusive(x_68);
if (x_295 == 0)
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_296 = lean_ctor_get(x_68, 1);
lean_dec(x_296);
x_297 = lean_ctor_get(x_68, 0);
lean_dec(x_297);
lean_ctor_set_tag(x_68, 0);
lean_ctor_set(x_68, 1, x_46);
lean_ctor_set(x_68, 0, x_294);
if (lean_is_scalar(x_24)) {
 x_298 = lean_alloc_ctor(1, 1, 0);
} else {
 x_298 = x_24;
}
lean_ctor_set(x_298, 0, x_68);
x_299 = lean_apply_6(x_4, x_298, x_8, x_9, x_10, x_11, x_43);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; 
lean_dec(x_68);
x_300 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_300, 0, x_294);
lean_ctor_set(x_300, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_301 = lean_alloc_ctor(1, 1, 0);
} else {
 x_301 = x_24;
}
lean_ctor_set(x_301, 0, x_300);
x_302 = lean_apply_6(x_4, x_301, x_8, x_9, x_10, x_11, x_43);
return x_302;
}
}
}
case 5:
{
lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_303 = lean_ctor_get(x_45, 0);
lean_inc(x_303);
x_304 = lean_ctor_get(x_45, 1);
lean_inc(x_304);
lean_dec(x_45);
x_305 = l_Lean_Expr_app___override(x_303, x_304);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_305);
lean_ctor_set(x_306, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_307 = lean_alloc_ctor(1, 1, 0);
} else {
 x_307 = x_24;
}
lean_ctor_set(x_307, 0, x_306);
x_308 = lean_apply_6(x_4, x_307, x_8, x_9, x_10, x_11, x_43);
return x_308;
}
case 6:
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; uint8_t x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_309 = lean_ctor_get(x_45, 0);
lean_inc(x_309);
x_310 = lean_ctor_get(x_45, 1);
lean_inc(x_310);
x_311 = lean_ctor_get(x_45, 2);
lean_inc(x_311);
x_312 = lean_ctor_get_uint8(x_45, sizeof(void*)*3 + 8);
lean_dec(x_45);
x_313 = l_Lean_Expr_lam___override(x_309, x_310, x_311, x_312);
x_314 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_314, 0, x_313);
lean_ctor_set(x_314, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_315 = lean_alloc_ctor(1, 1, 0);
} else {
 x_315 = x_24;
}
lean_ctor_set(x_315, 0, x_314);
x_316 = lean_apply_6(x_4, x_315, x_8, x_9, x_10, x_11, x_43);
return x_316;
}
case 7:
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_317 = lean_ctor_get(x_45, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_45, 1);
lean_inc(x_318);
x_319 = lean_ctor_get(x_45, 2);
lean_inc(x_319);
x_320 = lean_ctor_get_uint8(x_45, sizeof(void*)*3 + 8);
lean_dec(x_45);
x_321 = l_Lean_Expr_forallE___override(x_317, x_318, x_319, x_320);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_323 = lean_alloc_ctor(1, 1, 0);
} else {
 x_323 = x_24;
}
lean_ctor_set(x_323, 0, x_322);
x_324 = lean_apply_6(x_4, x_323, x_8, x_9, x_10, x_11, x_43);
return x_324;
}
case 8:
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; uint8_t x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_325 = lean_ctor_get(x_45, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_45, 1);
lean_inc(x_326);
x_327 = lean_ctor_get(x_45, 2);
lean_inc(x_327);
x_328 = lean_ctor_get(x_45, 3);
lean_inc(x_328);
x_329 = lean_ctor_get_uint8(x_45, sizeof(void*)*4 + 8);
lean_dec(x_45);
x_330 = l_Lean_Expr_letE___override(x_325, x_326, x_327, x_328, x_329);
x_331 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_331, 0, x_330);
lean_ctor_set(x_331, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_332 = lean_alloc_ctor(1, 1, 0);
} else {
 x_332 = x_24;
}
lean_ctor_set(x_332, 0, x_331);
x_333 = lean_apply_6(x_4, x_332, x_8, x_9, x_10, x_11, x_43);
return x_333;
}
case 9:
{
lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_334 = lean_ctor_get(x_45, 0);
lean_inc(x_334);
lean_dec(x_45);
x_335 = l_Lean_Expr_lit___override(x_334);
x_336 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_337 = lean_alloc_ctor(1, 1, 0);
} else {
 x_337 = x_24;
}
lean_ctor_set(x_337, 0, x_336);
x_338 = lean_apply_6(x_4, x_337, x_8, x_9, x_10, x_11, x_43);
return x_338;
}
case 10:
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_339 = lean_ctor_get(x_45, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_45, 1);
lean_inc(x_340);
lean_dec(x_45);
x_341 = l_Lean_Expr_mdata___override(x_339, x_340);
x_342 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_342, 0, x_341);
lean_ctor_set(x_342, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_343 = lean_alloc_ctor(1, 1, 0);
} else {
 x_343 = x_24;
}
lean_ctor_set(x_343, 0, x_342);
x_344 = lean_apply_6(x_4, x_343, x_8, x_9, x_10, x_11, x_43);
return x_344;
}
default: 
{
lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_345 = lean_ctor_get(x_45, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_45, 1);
lean_inc(x_346);
x_347 = lean_ctor_get(x_45, 2);
lean_inc(x_347);
lean_dec(x_45);
x_348 = l_Lean_Expr_proj___override(x_345, x_346, x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_46);
if (lean_is_scalar(x_24)) {
 x_350 = lean_alloc_ctor(1, 1, 0);
} else {
 x_350 = x_24;
}
lean_ctor_set(x_350, 0, x_349);
x_351 = lean_apply_6(x_4, x_350, x_8, x_9, x_10, x_11, x_43);
return x_351;
}
}
}
else
{
lean_object* x_352; lean_object* x_353; 
lean_dec(x_46);
lean_dec(x_45);
lean_free_object(x_40);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_352 = lean_box(0);
x_353 = lean_apply_6(x_4, x_352, x_8, x_9, x_10, x_11, x_43);
return x_353;
}
}
else
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; 
x_354 = lean_ctor_get(x_40, 1);
lean_inc(x_354);
lean_dec(x_40);
x_355 = lean_ctor_get(x_41, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_41, 2);
lean_inc(x_356);
lean_dec(x_41);
x_357 = l_Lean_Expr_hasLooseBVars(x_356);
if (x_357 == 0)
{
switch (lean_obj_tag(x_355)) {
case 0:
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_358 = lean_ctor_get(x_355, 0);
lean_inc(x_358);
lean_dec(x_355);
x_359 = l_Lean_Expr_bvar___override(x_358);
x_360 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_360, 0, x_359);
lean_ctor_set(x_360, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_24;
}
lean_ctor_set(x_361, 0, x_360);
x_362 = lean_apply_6(x_4, x_361, x_8, x_9, x_10, x_11, x_354);
return x_362;
}
case 1:
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; lean_object* x_367; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_363 = lean_ctor_get(x_355, 0);
lean_inc(x_363);
lean_dec(x_355);
x_364 = l_Lean_Expr_fvar___override(x_363);
x_365 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_365, 0, x_364);
lean_ctor_set(x_365, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_366 = lean_alloc_ctor(1, 1, 0);
} else {
 x_366 = x_24;
}
lean_ctor_set(x_366, 0, x_365);
x_367 = lean_apply_6(x_4, x_366, x_8, x_9, x_10, x_11, x_354);
return x_367;
}
case 2:
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_368 = lean_ctor_get(x_355, 0);
lean_inc(x_368);
lean_dec(x_355);
x_369 = l_Lean_Expr_mvar___override(x_368);
x_370 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_370, 0, x_369);
lean_ctor_set(x_370, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_371 = lean_alloc_ctor(1, 1, 0);
} else {
 x_371 = x_24;
}
lean_ctor_set(x_371, 0, x_370);
x_372 = lean_apply_6(x_4, x_371, x_8, x_9, x_10, x_11, x_354);
return x_372;
}
case 3:
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_373 = lean_ctor_get(x_355, 0);
lean_inc(x_373);
lean_dec(x_355);
x_374 = l_Lean_Expr_sort___override(x_373);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_376 = x_24;
}
lean_ctor_set(x_376, 0, x_375);
x_377 = lean_apply_6(x_4, x_376, x_8, x_9, x_10, x_11, x_354);
return x_377;
}
case 4:
{
lean_object* x_378; 
x_378 = lean_ctor_get(x_355, 1);
lean_inc(x_378);
if (lean_obj_tag(x_378) == 0)
{
switch (lean_obj_tag(x_356)) {
case 0:
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_379 = lean_ctor_get(x_355, 0);
lean_inc(x_379);
lean_dec(x_355);
x_380 = lean_ctor_get(x_356, 0);
lean_inc(x_380);
lean_dec(x_356);
x_381 = l_Lean_Expr_const___override(x_379, x_378);
x_382 = l_Lean_Expr_bvar___override(x_380);
x_383 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
if (lean_is_scalar(x_24)) {
 x_384 = lean_alloc_ctor(1, 1, 0);
} else {
 x_384 = x_24;
}
lean_ctor_set(x_384, 0, x_383);
x_385 = lean_apply_6(x_4, x_384, x_8, x_9, x_10, x_11, x_354);
return x_385;
}
case 1:
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_386 = lean_ctor_get(x_355, 0);
lean_inc(x_386);
lean_dec(x_355);
x_387 = lean_ctor_get(x_356, 0);
lean_inc(x_387);
lean_dec(x_356);
x_388 = l_Lean_Expr_const___override(x_386, x_378);
x_389 = l_Lean_Expr_fvar___override(x_387);
x_390 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_390, 0, x_388);
lean_ctor_set(x_390, 1, x_389);
if (lean_is_scalar(x_24)) {
 x_391 = lean_alloc_ctor(1, 1, 0);
} else {
 x_391 = x_24;
}
lean_ctor_set(x_391, 0, x_390);
x_392 = lean_apply_6(x_4, x_391, x_8, x_9, x_10, x_11, x_354);
return x_392;
}
case 2:
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_393 = lean_ctor_get(x_355, 0);
lean_inc(x_393);
lean_dec(x_355);
x_394 = lean_ctor_get(x_356, 0);
lean_inc(x_394);
lean_dec(x_356);
x_395 = l_Lean_Expr_const___override(x_393, x_378);
x_396 = l_Lean_Expr_mvar___override(x_394);
x_397 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
if (lean_is_scalar(x_24)) {
 x_398 = lean_alloc_ctor(1, 1, 0);
} else {
 x_398 = x_24;
}
lean_ctor_set(x_398, 0, x_397);
x_399 = lean_apply_6(x_4, x_398, x_8, x_9, x_10, x_11, x_354);
return x_399;
}
case 3:
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_400 = lean_ctor_get(x_355, 0);
lean_inc(x_400);
lean_dec(x_355);
x_401 = lean_ctor_get(x_356, 0);
lean_inc(x_401);
lean_dec(x_356);
lean_inc(x_400);
x_402 = l_Lean_Expr_const___override(x_400, x_378);
x_403 = lean_box(0);
x_404 = l_Lean_Expr_sort___override(x_403);
switch (lean_obj_tag(x_401)) {
case 0:
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; 
lean_dec(x_400);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_405 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_405, 0, x_402);
lean_ctor_set(x_405, 1, x_404);
if (lean_is_scalar(x_24)) {
 x_406 = lean_alloc_ctor(1, 1, 0);
} else {
 x_406 = x_24;
}
lean_ctor_set(x_406, 0, x_405);
x_407 = lean_apply_6(x_4, x_406, x_8, x_9, x_10, x_11, x_354);
return x_407;
}
case 1:
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_408 = lean_ctor_get(x_401, 0);
lean_inc(x_408);
lean_dec(x_401);
x_409 = l_Lean_Level_succ___override(x_408);
x_410 = l_Lean_Expr_sort___override(x_409);
x_411 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_411, 0, x_402);
lean_ctor_set(x_411, 1, x_410);
if (lean_is_scalar(x_24)) {
 x_412 = lean_alloc_ctor(1, 1, 0);
} else {
 x_412 = x_24;
}
lean_ctor_set(x_412, 0, x_411);
x_413 = lean_apply_6(x_4, x_412, x_8, x_9, x_10, x_11, x_354);
return x_413;
}
case 2:
{
lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_414 = lean_ctor_get(x_401, 0);
lean_inc(x_414);
x_415 = lean_ctor_get(x_401, 1);
lean_inc(x_415);
lean_dec(x_401);
x_416 = l_Lean_Level_max___override(x_414, x_415);
x_417 = l_Lean_Expr_sort___override(x_416);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_402);
lean_ctor_set(x_418, 1, x_417);
if (lean_is_scalar(x_24)) {
 x_419 = lean_alloc_ctor(1, 1, 0);
} else {
 x_419 = x_24;
}
lean_ctor_set(x_419, 0, x_418);
x_420 = lean_apply_6(x_4, x_419, x_8, x_9, x_10, x_11, x_354);
return x_420;
}
case 3:
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; 
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_421 = lean_ctor_get(x_401, 0);
lean_inc(x_421);
x_422 = lean_ctor_get(x_401, 1);
lean_inc(x_422);
lean_dec(x_401);
x_423 = l_Lean_Level_imax___override(x_421, x_422);
x_424 = l_Lean_Expr_sort___override(x_423);
x_425 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_425, 0, x_402);
lean_ctor_set(x_425, 1, x_424);
if (lean_is_scalar(x_24)) {
 x_426 = lean_alloc_ctor(1, 1, 0);
} else {
 x_426 = x_24;
}
lean_ctor_set(x_426, 0, x_425);
x_427 = lean_apply_6(x_4, x_426, x_8, x_9, x_10, x_11, x_354);
return x_427;
}
case 4:
{
uint8_t x_428; 
lean_dec(x_402);
lean_dec(x_401);
lean_dec(x_4);
x_428 = lean_name_eq(x_400, x_23);
lean_dec(x_400);
if (x_428 == 0)
{
lean_object* x_429; lean_object* x_430; 
lean_dec(x_404);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_429 = lean_box(0);
x_430 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_430, 0, x_429);
lean_ctor_set(x_430, 1, x_354);
return x_430;
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; uint8_t x_436; 
x_431 = l_Lean_Expr_getAppNumArgs(x_7);
lean_inc(x_431);
x_432 = lean_mk_array(x_431, x_404);
x_433 = lean_nat_sub(x_431, x_2);
lean_dec(x_431);
x_434 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg(x_16, x_39, x_7, x_432, x_433, x_354);
lean_dec(x_16);
x_435 = lean_ctor_get(x_434, 0);
lean_inc(x_435);
x_436 = lean_unbox(x_435);
lean_dec(x_435);
if (x_436 == 0)
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_437 = lean_ctor_get(x_434, 1);
lean_inc(x_437);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_438 = x_434;
} else {
 lean_dec_ref(x_434);
 x_438 = lean_box(0);
}
x_439 = lean_box(0);
if (lean_is_scalar(x_438)) {
 x_440 = lean_alloc_ctor(0, 2, 0);
} else {
 x_440 = x_438;
}
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_437);
return x_440;
}
else
{
lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_510; lean_object* x_511; uint8_t x_512; 
x_441 = lean_ctor_get(x_434, 1);
lean_inc(x_441);
if (lean_is_exclusive(x_434)) {
 lean_ctor_release(x_434, 0);
 lean_ctor_release(x_434, 1);
 x_442 = x_434;
} else {
 lean_dec_ref(x_434);
 x_442 = lean_box(0);
}
x_443 = lean_box(x_15);
lean_inc(x_39);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_444 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1___boxed), 13, 6);
lean_closure_set(x_444, 0, x_2);
lean_closure_set(x_444, 1, x_443);
lean_closure_set(x_444, 2, x_1);
lean_closure_set(x_444, 3, x_3);
lean_closure_set(x_444, 4, x_23);
lean_closure_set(x_444, 5, x_39);
x_510 = l_Lean_InductiveVal_numCtors(x_38);
x_511 = lean_nat_add(x_510, x_14);
x_512 = lean_nat_dec_eq(x_13, x_511);
lean_dec(x_511);
if (x_512 == 0)
{
lean_dec(x_510);
x_445 = x_8;
x_446 = x_9;
x_447 = x_10;
x_448 = x_11;
x_449 = x_441;
goto block_509;
}
else
{
lean_object* x_513; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_38);
lean_inc(x_5);
x_513 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum(x_5, x_38, x_6, x_510, x_39, x_8, x_9, x_10, x_11, x_441);
if (lean_obj_tag(x_513) == 0)
{
lean_object* x_514; 
x_514 = lean_ctor_get(x_513, 0);
lean_inc(x_514);
if (lean_obj_tag(x_514) == 0)
{
lean_object* x_515; 
x_515 = lean_ctor_get(x_513, 1);
lean_inc(x_515);
lean_dec(x_513);
x_445 = x_8;
x_446 = x_9;
x_447 = x_10;
x_448 = x_11;
x_449 = x_515;
goto block_509;
}
else
{
lean_dec(x_514);
lean_dec(x_444);
lean_dec(x_442);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_513;
}
}
else
{
lean_dec(x_444);
lean_dec(x_442);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_513;
}
}
block_509:
{
uint8_t x_450; 
x_450 = lean_nat_dec_lt(x_14, x_13);
if (x_450 == 0)
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_451 = lean_box(0);
if (lean_is_scalar(x_442)) {
 x_452 = lean_alloc_ctor(0, 2, 0);
} else {
 x_452 = x_442;
}
lean_ctor_set(x_452, 0, x_451);
lean_ctor_set(x_452, 1, x_449);
return x_452;
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; 
lean_dec(x_442);
x_453 = lean_unsigned_to_nat(3u);
x_454 = lean_nat_sub(x_13, x_453);
x_455 = lean_mk_empty_array_with_capacity(x_454);
lean_inc(x_2);
lean_inc(x_3);
x_456 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_456, 0, x_3);
lean_ctor_set(x_456, 1, x_454);
lean_ctor_set(x_456, 2, x_2);
x_457 = lean_box(0);
x_458 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_458, 0, x_457);
lean_ctor_set(x_458, 1, x_455);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
x_459 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg(x_6, x_39, x_456, x_458, x_3, x_445, x_446, x_447, x_448, x_449);
lean_dec(x_456);
lean_dec(x_39);
if (lean_obj_tag(x_459) == 0)
{
lean_object* x_460; lean_object* x_461; 
x_460 = lean_ctor_get(x_459, 0);
lean_inc(x_460);
x_461 = lean_ctor_get(x_460, 0);
lean_inc(x_461);
if (lean_obj_tag(x_461) == 0)
{
lean_object* x_462; lean_object* x_463; lean_object* x_464; lean_object* x_465; 
x_462 = lean_ctor_get(x_459, 1);
lean_inc(x_462);
lean_dec(x_459);
x_463 = lean_nat_sub(x_13, x_2);
lean_dec(x_2);
lean_dec(x_13);
x_464 = lean_array_get(x_1, x_6, x_463);
lean_dec(x_463);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
x_465 = lean_infer_type(x_464, x_445, x_446, x_447, x_448, x_462);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
lean_inc(x_448);
lean_inc(x_447);
lean_inc(x_446);
lean_inc(x_445);
x_468 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_466, x_444, x_15, x_445, x_446, x_447, x_448, x_467);
if (lean_obj_tag(x_468) == 0)
{
lean_object* x_469; uint8_t x_470; 
x_469 = lean_ctor_get(x_468, 0);
lean_inc(x_469);
x_470 = lean_unbox(x_469);
lean_dec(x_469);
if (x_470 == 0)
{
lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; 
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_5);
x_471 = lean_ctor_get(x_468, 1);
lean_inc(x_471);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_472 = x_468;
} else {
 lean_dec_ref(x_468);
 x_472 = lean_box(0);
}
x_473 = lean_box(0);
if (lean_is_scalar(x_472)) {
 x_474 = lean_alloc_ctor(0, 2, 0);
} else {
 x_474 = x_472;
}
lean_ctor_set(x_474, 0, x_473);
lean_ctor_set(x_474, 1, x_471);
return x_474;
}
else
{
lean_object* x_475; lean_object* x_476; lean_object* x_477; 
x_475 = lean_ctor_get(x_468, 1);
lean_inc(x_475);
lean_dec(x_468);
x_476 = lean_ctor_get(x_460, 1);
lean_inc(x_476);
lean_dec(x_460);
lean_inc(x_476);
lean_inc(x_38);
x_477 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault(x_5, x_38, x_476, x_445, x_446, x_447, x_448, x_475);
if (lean_obj_tag(x_477) == 0)
{
lean_object* x_478; uint8_t x_479; 
x_478 = lean_ctor_get(x_477, 0);
lean_inc(x_478);
x_479 = lean_unbox(x_478);
lean_dec(x_478);
if (x_479 == 0)
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; 
lean_dec(x_476);
lean_dec(x_38);
lean_dec(x_24);
x_480 = lean_ctor_get(x_477, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_481 = x_477;
} else {
 lean_dec_ref(x_477);
 x_481 = lean_box(0);
}
x_482 = lean_box(0);
if (lean_is_scalar(x_481)) {
 x_483 = lean_alloc_ctor(0, 2, 0);
} else {
 x_483 = x_481;
}
lean_ctor_set(x_483, 0, x_482);
lean_ctor_set(x_483, 1, x_480);
return x_483;
}
else
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; 
x_484 = lean_ctor_get(x_477, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_485 = x_477;
} else {
 lean_dec_ref(x_477);
 x_485 = lean_box(0);
}
x_486 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_486, 0, x_38);
lean_ctor_set(x_486, 1, x_476);
if (lean_is_scalar(x_24)) {
 x_487 = lean_alloc_ctor(1, 1, 0);
} else {
 x_487 = x_24;
}
lean_ctor_set(x_487, 0, x_486);
if (lean_is_scalar(x_485)) {
 x_488 = lean_alloc_ctor(0, 2, 0);
} else {
 x_488 = x_485;
}
lean_ctor_set(x_488, 0, x_487);
lean_ctor_set(x_488, 1, x_484);
return x_488;
}
}
else
{
lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_476);
lean_dec(x_38);
lean_dec(x_24);
x_489 = lean_ctor_get(x_477, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_477, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_477)) {
 lean_ctor_release(x_477, 0);
 lean_ctor_release(x_477, 1);
 x_491 = x_477;
} else {
 lean_dec_ref(x_477);
 x_491 = lean_box(0);
}
if (lean_is_scalar(x_491)) {
 x_492 = lean_alloc_ctor(1, 2, 0);
} else {
 x_492 = x_491;
}
lean_ctor_set(x_492, 0, x_489);
lean_ctor_set(x_492, 1, x_490);
return x_492;
}
}
}
else
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; 
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_5);
x_493 = lean_ctor_get(x_468, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_468, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_468)) {
 lean_ctor_release(x_468, 0);
 lean_ctor_release(x_468, 1);
 x_495 = x_468;
} else {
 lean_dec_ref(x_468);
 x_495 = lean_box(0);
}
if (lean_is_scalar(x_495)) {
 x_496 = lean_alloc_ctor(1, 2, 0);
} else {
 x_496 = x_495;
}
lean_ctor_set(x_496, 0, x_493);
lean_ctor_set(x_496, 1, x_494);
return x_496;
}
}
else
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_5);
x_497 = lean_ctor_get(x_465, 0);
lean_inc(x_497);
x_498 = lean_ctor_get(x_465, 1);
lean_inc(x_498);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_499 = x_465;
} else {
 lean_dec_ref(x_465);
 x_499 = lean_box(0);
}
if (lean_is_scalar(x_499)) {
 x_500 = lean_alloc_ctor(1, 2, 0);
} else {
 x_500 = x_499;
}
lean_ctor_set(x_500, 0, x_497);
lean_ctor_set(x_500, 1, x_498);
return x_500;
}
}
else
{
lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_460);
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_501 = lean_ctor_get(x_459, 1);
lean_inc(x_501);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_502 = x_459;
} else {
 lean_dec_ref(x_459);
 x_502 = lean_box(0);
}
x_503 = lean_ctor_get(x_461, 0);
lean_inc(x_503);
lean_dec(x_461);
if (lean_is_scalar(x_502)) {
 x_504 = lean_alloc_ctor(0, 2, 0);
} else {
 x_504 = x_502;
}
lean_ctor_set(x_504, 0, x_503);
lean_ctor_set(x_504, 1, x_501);
return x_504;
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_448);
lean_dec(x_447);
lean_dec(x_446);
lean_dec(x_445);
lean_dec(x_444);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_505 = lean_ctor_get(x_459, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_459, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_459)) {
 lean_ctor_release(x_459, 0);
 lean_ctor_release(x_459, 1);
 x_507 = x_459;
} else {
 lean_dec_ref(x_459);
 x_507 = lean_box(0);
}
if (lean_is_scalar(x_507)) {
 x_508 = lean_alloc_ctor(1, 2, 0);
} else {
 x_508 = x_507;
}
lean_ctor_set(x_508, 0, x_505);
lean_ctor_set(x_508, 1, x_506);
return x_508;
}
}
}
}
}
}
default: 
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_519; lean_object* x_520; lean_object* x_521; 
lean_dec(x_404);
lean_dec(x_400);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_516 = lean_ctor_get(x_401, 0);
lean_inc(x_516);
lean_dec(x_401);
x_517 = l_Lean_Level_mvar___override(x_516);
x_518 = l_Lean_Expr_sort___override(x_517);
x_519 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_519, 0, x_402);
lean_ctor_set(x_519, 1, x_518);
if (lean_is_scalar(x_24)) {
 x_520 = lean_alloc_ctor(1, 1, 0);
} else {
 x_520 = x_24;
}
lean_ctor_set(x_520, 0, x_519);
x_521 = lean_apply_6(x_4, x_520, x_8, x_9, x_10, x_11, x_354);
return x_521;
}
}
}
case 4:
{
lean_object* x_522; lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_522 = lean_ctor_get(x_355, 0);
lean_inc(x_522);
lean_dec(x_355);
x_523 = lean_ctor_get(x_356, 0);
lean_inc(x_523);
x_524 = lean_ctor_get(x_356, 1);
lean_inc(x_524);
lean_dec(x_356);
x_525 = l_Lean_Expr_const___override(x_522, x_378);
x_526 = l_Lean_Expr_const___override(x_523, x_524);
x_527 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_527, 0, x_525);
lean_ctor_set(x_527, 1, x_526);
if (lean_is_scalar(x_24)) {
 x_528 = lean_alloc_ctor(1, 1, 0);
} else {
 x_528 = x_24;
}
lean_ctor_set(x_528, 0, x_527);
x_529 = lean_apply_6(x_4, x_528, x_8, x_9, x_10, x_11, x_354);
return x_529;
}
case 5:
{
lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_530 = lean_ctor_get(x_355, 0);
lean_inc(x_530);
lean_dec(x_355);
x_531 = lean_ctor_get(x_356, 0);
lean_inc(x_531);
x_532 = lean_ctor_get(x_356, 1);
lean_inc(x_532);
lean_dec(x_356);
x_533 = l_Lean_Expr_const___override(x_530, x_378);
x_534 = l_Lean_Expr_app___override(x_531, x_532);
x_535 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_535, 0, x_533);
lean_ctor_set(x_535, 1, x_534);
if (lean_is_scalar(x_24)) {
 x_536 = lean_alloc_ctor(1, 1, 0);
} else {
 x_536 = x_24;
}
lean_ctor_set(x_536, 0, x_535);
x_537 = lean_apply_6(x_4, x_536, x_8, x_9, x_10, x_11, x_354);
return x_537;
}
case 6:
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; uint8_t x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_538 = lean_ctor_get(x_355, 0);
lean_inc(x_538);
lean_dec(x_355);
x_539 = lean_ctor_get(x_356, 0);
lean_inc(x_539);
x_540 = lean_ctor_get(x_356, 1);
lean_inc(x_540);
x_541 = lean_ctor_get(x_356, 2);
lean_inc(x_541);
x_542 = lean_ctor_get_uint8(x_356, sizeof(void*)*3 + 8);
lean_dec(x_356);
x_543 = l_Lean_Expr_const___override(x_538, x_378);
x_544 = l_Lean_Expr_lam___override(x_539, x_540, x_541, x_542);
x_545 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_545, 0, x_543);
lean_ctor_set(x_545, 1, x_544);
if (lean_is_scalar(x_24)) {
 x_546 = lean_alloc_ctor(1, 1, 0);
} else {
 x_546 = x_24;
}
lean_ctor_set(x_546, 0, x_545);
x_547 = lean_apply_6(x_4, x_546, x_8, x_9, x_10, x_11, x_354);
return x_547;
}
case 7:
{
lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; uint8_t x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_548 = lean_ctor_get(x_355, 0);
lean_inc(x_548);
lean_dec(x_355);
x_549 = lean_ctor_get(x_356, 0);
lean_inc(x_549);
x_550 = lean_ctor_get(x_356, 1);
lean_inc(x_550);
x_551 = lean_ctor_get(x_356, 2);
lean_inc(x_551);
x_552 = lean_ctor_get_uint8(x_356, sizeof(void*)*3 + 8);
lean_dec(x_356);
x_553 = l_Lean_Expr_const___override(x_548, x_378);
x_554 = l_Lean_Expr_forallE___override(x_549, x_550, x_551, x_552);
x_555 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
if (lean_is_scalar(x_24)) {
 x_556 = lean_alloc_ctor(1, 1, 0);
} else {
 x_556 = x_24;
}
lean_ctor_set(x_556, 0, x_555);
x_557 = lean_apply_6(x_4, x_556, x_8, x_9, x_10, x_11, x_354);
return x_557;
}
case 8:
{
lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; uint8_t x_563; lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_558 = lean_ctor_get(x_355, 0);
lean_inc(x_558);
lean_dec(x_355);
x_559 = lean_ctor_get(x_356, 0);
lean_inc(x_559);
x_560 = lean_ctor_get(x_356, 1);
lean_inc(x_560);
x_561 = lean_ctor_get(x_356, 2);
lean_inc(x_561);
x_562 = lean_ctor_get(x_356, 3);
lean_inc(x_562);
x_563 = lean_ctor_get_uint8(x_356, sizeof(void*)*4 + 8);
lean_dec(x_356);
x_564 = l_Lean_Expr_const___override(x_558, x_378);
x_565 = l_Lean_Expr_letE___override(x_559, x_560, x_561, x_562, x_563);
x_566 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_566, 0, x_564);
lean_ctor_set(x_566, 1, x_565);
if (lean_is_scalar(x_24)) {
 x_567 = lean_alloc_ctor(1, 1, 0);
} else {
 x_567 = x_24;
}
lean_ctor_set(x_567, 0, x_566);
x_568 = lean_apply_6(x_4, x_567, x_8, x_9, x_10, x_11, x_354);
return x_568;
}
case 9:
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_569 = lean_ctor_get(x_355, 0);
lean_inc(x_569);
lean_dec(x_355);
x_570 = lean_ctor_get(x_356, 0);
lean_inc(x_570);
lean_dec(x_356);
x_571 = l_Lean_Expr_const___override(x_569, x_378);
x_572 = l_Lean_Expr_lit___override(x_570);
x_573 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
if (lean_is_scalar(x_24)) {
 x_574 = lean_alloc_ctor(1, 1, 0);
} else {
 x_574 = x_24;
}
lean_ctor_set(x_574, 0, x_573);
x_575 = lean_apply_6(x_4, x_574, x_8, x_9, x_10, x_11, x_354);
return x_575;
}
case 10:
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_576 = lean_ctor_get(x_355, 0);
lean_inc(x_576);
lean_dec(x_355);
x_577 = lean_ctor_get(x_356, 0);
lean_inc(x_577);
x_578 = lean_ctor_get(x_356, 1);
lean_inc(x_578);
lean_dec(x_356);
x_579 = l_Lean_Expr_const___override(x_576, x_378);
x_580 = l_Lean_Expr_mdata___override(x_577, x_578);
x_581 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
if (lean_is_scalar(x_24)) {
 x_582 = lean_alloc_ctor(1, 1, 0);
} else {
 x_582 = x_24;
}
lean_ctor_set(x_582, 0, x_581);
x_583 = lean_apply_6(x_4, x_582, x_8, x_9, x_10, x_11, x_354);
return x_583;
}
default: 
{
lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_584 = lean_ctor_get(x_355, 0);
lean_inc(x_584);
lean_dec(x_355);
x_585 = lean_ctor_get(x_356, 0);
lean_inc(x_585);
x_586 = lean_ctor_get(x_356, 1);
lean_inc(x_586);
x_587 = lean_ctor_get(x_356, 2);
lean_inc(x_587);
lean_dec(x_356);
x_588 = l_Lean_Expr_const___override(x_584, x_378);
x_589 = l_Lean_Expr_proj___override(x_585, x_586, x_587);
x_590 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_590, 0, x_588);
lean_ctor_set(x_590, 1, x_589);
if (lean_is_scalar(x_24)) {
 x_591 = lean_alloc_ctor(1, 1, 0);
} else {
 x_591 = x_24;
}
lean_ctor_set(x_591, 0, x_590);
x_592 = lean_apply_6(x_4, x_591, x_8, x_9, x_10, x_11, x_354);
return x_592;
}
}
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_593 = lean_ctor_get(x_355, 0);
lean_inc(x_593);
lean_dec(x_355);
lean_inc(x_378);
x_594 = l_Lean_Expr_const___override(x_593, x_378);
if (lean_is_exclusive(x_378)) {
 lean_ctor_release(x_378, 0);
 lean_ctor_release(x_378, 1);
 x_595 = x_378;
} else {
 lean_dec_ref(x_378);
 x_595 = lean_box(0);
}
if (lean_is_scalar(x_595)) {
 x_596 = lean_alloc_ctor(0, 2, 0);
} else {
 x_596 = x_595;
 lean_ctor_set_tag(x_596, 0);
}
lean_ctor_set(x_596, 0, x_594);
lean_ctor_set(x_596, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_597 = lean_alloc_ctor(1, 1, 0);
} else {
 x_597 = x_24;
}
lean_ctor_set(x_597, 0, x_596);
x_598 = lean_apply_6(x_4, x_597, x_8, x_9, x_10, x_11, x_354);
return x_598;
}
}
case 5:
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_599 = lean_ctor_get(x_355, 0);
lean_inc(x_599);
x_600 = lean_ctor_get(x_355, 1);
lean_inc(x_600);
lean_dec(x_355);
x_601 = l_Lean_Expr_app___override(x_599, x_600);
x_602 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_602, 0, x_601);
lean_ctor_set(x_602, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_603 = lean_alloc_ctor(1, 1, 0);
} else {
 x_603 = x_24;
}
lean_ctor_set(x_603, 0, x_602);
x_604 = lean_apply_6(x_4, x_603, x_8, x_9, x_10, x_11, x_354);
return x_604;
}
case 6:
{
lean_object* x_605; lean_object* x_606; lean_object* x_607; uint8_t x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_605 = lean_ctor_get(x_355, 0);
lean_inc(x_605);
x_606 = lean_ctor_get(x_355, 1);
lean_inc(x_606);
x_607 = lean_ctor_get(x_355, 2);
lean_inc(x_607);
x_608 = lean_ctor_get_uint8(x_355, sizeof(void*)*3 + 8);
lean_dec(x_355);
x_609 = l_Lean_Expr_lam___override(x_605, x_606, x_607, x_608);
x_610 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_610, 0, x_609);
lean_ctor_set(x_610, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_611 = lean_alloc_ctor(1, 1, 0);
} else {
 x_611 = x_24;
}
lean_ctor_set(x_611, 0, x_610);
x_612 = lean_apply_6(x_4, x_611, x_8, x_9, x_10, x_11, x_354);
return x_612;
}
case 7:
{
lean_object* x_613; lean_object* x_614; lean_object* x_615; uint8_t x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_613 = lean_ctor_get(x_355, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_355, 1);
lean_inc(x_614);
x_615 = lean_ctor_get(x_355, 2);
lean_inc(x_615);
x_616 = lean_ctor_get_uint8(x_355, sizeof(void*)*3 + 8);
lean_dec(x_355);
x_617 = l_Lean_Expr_forallE___override(x_613, x_614, x_615, x_616);
x_618 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_618, 0, x_617);
lean_ctor_set(x_618, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_619 = lean_alloc_ctor(1, 1, 0);
} else {
 x_619 = x_24;
}
lean_ctor_set(x_619, 0, x_618);
x_620 = lean_apply_6(x_4, x_619, x_8, x_9, x_10, x_11, x_354);
return x_620;
}
case 8:
{
lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; uint8_t x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_621 = lean_ctor_get(x_355, 0);
lean_inc(x_621);
x_622 = lean_ctor_get(x_355, 1);
lean_inc(x_622);
x_623 = lean_ctor_get(x_355, 2);
lean_inc(x_623);
x_624 = lean_ctor_get(x_355, 3);
lean_inc(x_624);
x_625 = lean_ctor_get_uint8(x_355, sizeof(void*)*4 + 8);
lean_dec(x_355);
x_626 = l_Lean_Expr_letE___override(x_621, x_622, x_623, x_624, x_625);
x_627 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_627, 0, x_626);
lean_ctor_set(x_627, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_628 = lean_alloc_ctor(1, 1, 0);
} else {
 x_628 = x_24;
}
lean_ctor_set(x_628, 0, x_627);
x_629 = lean_apply_6(x_4, x_628, x_8, x_9, x_10, x_11, x_354);
return x_629;
}
case 9:
{
lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_630 = lean_ctor_get(x_355, 0);
lean_inc(x_630);
lean_dec(x_355);
x_631 = l_Lean_Expr_lit___override(x_630);
x_632 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_632, 0, x_631);
lean_ctor_set(x_632, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_633 = lean_alloc_ctor(1, 1, 0);
} else {
 x_633 = x_24;
}
lean_ctor_set(x_633, 0, x_632);
x_634 = lean_apply_6(x_4, x_633, x_8, x_9, x_10, x_11, x_354);
return x_634;
}
case 10:
{
lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_635 = lean_ctor_get(x_355, 0);
lean_inc(x_635);
x_636 = lean_ctor_get(x_355, 1);
lean_inc(x_636);
lean_dec(x_355);
x_637 = l_Lean_Expr_mdata___override(x_635, x_636);
x_638 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_638, 0, x_637);
lean_ctor_set(x_638, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_639 = lean_alloc_ctor(1, 1, 0);
} else {
 x_639 = x_24;
}
lean_ctor_set(x_639, 0, x_638);
x_640 = lean_apply_6(x_4, x_639, x_8, x_9, x_10, x_11, x_354);
return x_640;
}
default: 
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_641 = lean_ctor_get(x_355, 0);
lean_inc(x_641);
x_642 = lean_ctor_get(x_355, 1);
lean_inc(x_642);
x_643 = lean_ctor_get(x_355, 2);
lean_inc(x_643);
lean_dec(x_355);
x_644 = l_Lean_Expr_proj___override(x_641, x_642, x_643);
x_645 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_645, 0, x_644);
lean_ctor_set(x_645, 1, x_356);
if (lean_is_scalar(x_24)) {
 x_646 = lean_alloc_ctor(1, 1, 0);
} else {
 x_646 = x_24;
}
lean_ctor_set(x_646, 0, x_645);
x_647 = lean_apply_6(x_4, x_646, x_8, x_9, x_10, x_11, x_354);
return x_647;
}
}
}
else
{
lean_object* x_648; lean_object* x_649; 
lean_dec(x_356);
lean_dec(x_355);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_648 = lean_box(0);
x_649 = lean_apply_6(x_4, x_648, x_8, x_9, x_10, x_11, x_354);
return x_649;
}
}
}
else
{
lean_object* x_650; lean_object* x_651; lean_object* x_652; 
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_650 = lean_ctor_get(x_40, 1);
lean_inc(x_650);
lean_dec(x_40);
x_651 = lean_box(0);
x_652 = lean_apply_6(x_4, x_651, x_8, x_9, x_10, x_11, x_650);
return x_652;
}
}
else
{
uint8_t x_653; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_653 = !lean_is_exclusive(x_40);
if (x_653 == 0)
{
return x_40;
}
else
{
lean_object* x_654; lean_object* x_655; lean_object* x_656; 
x_654 = lean_ctor_get(x_40, 0);
x_655 = lean_ctor_get(x_40, 1);
lean_inc(x_655);
lean_inc(x_654);
lean_dec(x_40);
x_656 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
return x_656;
}
}
}
else
{
lean_object* x_657; lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; 
lean_dec(x_36);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_657 = lean_ctor_get(x_35, 1);
lean_inc(x_657);
lean_dec(x_35);
x_658 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_659 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch", 61, 61);
x_660 = lean_unsigned_to_nat(36u);
x_661 = lean_unsigned_to_nat(65u);
x_662 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_663 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_658, x_659, x_660, x_661, x_662);
lean_dec(x_662);
lean_dec(x_659);
lean_dec(x_658);
x_664 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__5(x_663, x_8, x_9, x_10, x_11, x_657);
return x_664;
}
}
else
{
uint8_t x_665; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_665 = !lean_is_exclusive(x_35);
if (x_665 == 0)
{
return x_35;
}
else
{
lean_object* x_666; lean_object* x_667; lean_object* x_668; 
x_666 = lean_ctor_get(x_35, 0);
x_667 = lean_ctor_get(x_35, 1);
lean_inc(x_667);
lean_inc(x_666);
lean_dec(x_35);
x_668 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_668, 0, x_666);
lean_ctor_set(x_668, 1, x_667);
return x_668;
}
}
}
}
else
{
uint8_t x_669; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_669 = !lean_is_exclusive(x_25);
if (x_669 == 0)
{
return x_25;
}
else
{
lean_object* x_670; lean_object* x_671; lean_object* x_672; 
x_670 = lean_ctor_get(x_25, 0);
x_671 = lean_ctor_get(x_25, 1);
lean_inc(x_671);
lean_inc(x_670);
lean_dec(x_25);
x_672 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_672, 0, x_670);
lean_ctor_set(x_672, 1, x_671);
return x_672;
}
}
}
}
else
{
lean_object* x_673; lean_object* x_674; lean_object* x_675; 
x_673 = lean_ctor_get(x_17, 0);
x_674 = lean_ctor_get(x_17, 1);
lean_inc(x_674);
lean_inc(x_673);
lean_dec(x_17);
x_675 = l_Lean_Expr_constName_x3f(x_673);
lean_dec(x_673);
if (lean_obj_tag(x_675) == 0)
{
lean_object* x_676; lean_object* x_677; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_676 = lean_box(0);
x_677 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_677, 0, x_676);
lean_ctor_set(x_677, 1, x_674);
return x_677;
}
else
{
lean_object* x_678; lean_object* x_679; lean_object* x_680; 
x_678 = lean_ctor_get(x_675, 0);
lean_inc(x_678);
if (lean_is_exclusive(x_675)) {
 lean_ctor_release(x_675, 0);
 x_679 = x_675;
} else {
 lean_dec_ref(x_675);
 x_679 = lean_box(0);
}
lean_inc(x_678);
x_680 = l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0(x_678, x_8, x_9, x_10, x_11, x_674);
if (lean_obj_tag(x_680) == 0)
{
lean_object* x_681; uint8_t x_682; 
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_unbox(x_681);
lean_dec(x_681);
if (x_682 == 0)
{
lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_683 = lean_ctor_get(x_680, 1);
lean_inc(x_683);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_684 = x_680;
} else {
 lean_dec_ref(x_680);
 x_684 = lean_box(0);
}
x_685 = lean_box(0);
if (lean_is_scalar(x_684)) {
 x_686 = lean_alloc_ctor(0, 2, 0);
} else {
 x_686 = x_684;
}
lean_ctor_set(x_686, 0, x_685);
lean_ctor_set(x_686, 1, x_683);
return x_686;
}
else
{
lean_object* x_687; lean_object* x_688; 
x_687 = lean_ctor_get(x_680, 1);
lean_inc(x_687);
lean_dec(x_680);
lean_inc(x_678);
x_688 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_678, x_8, x_9, x_10, x_11, x_687);
if (lean_obj_tag(x_688) == 0)
{
lean_object* x_689; 
x_689 = lean_ctor_get(x_688, 0);
lean_inc(x_689);
if (lean_obj_tag(x_689) == 5)
{
lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; 
x_690 = lean_ctor_get(x_688, 1);
lean_inc(x_690);
lean_dec(x_688);
x_691 = lean_ctor_get(x_689, 0);
lean_inc(x_691);
lean_dec(x_689);
lean_inc(x_1);
x_692 = lean_array_get(x_1, x_6, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_692);
x_693 = lean_infer_type(x_692, x_8, x_9, x_10, x_11, x_690);
if (lean_obj_tag(x_693) == 0)
{
lean_object* x_694; 
x_694 = lean_ctor_get(x_693, 0);
lean_inc(x_694);
if (lean_obj_tag(x_694) == 7)
{
lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; uint8_t x_699; 
x_695 = lean_ctor_get(x_693, 1);
lean_inc(x_695);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_696 = x_693;
} else {
 lean_dec_ref(x_693);
 x_696 = lean_box(0);
}
x_697 = lean_ctor_get(x_694, 1);
lean_inc(x_697);
x_698 = lean_ctor_get(x_694, 2);
lean_inc(x_698);
lean_dec(x_694);
x_699 = l_Lean_Expr_hasLooseBVars(x_698);
if (x_699 == 0)
{
switch (lean_obj_tag(x_697)) {
case 0:
{
lean_object* x_700; lean_object* x_701; lean_object* x_702; lean_object* x_703; lean_object* x_704; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_700 = lean_ctor_get(x_697, 0);
lean_inc(x_700);
lean_dec(x_697);
x_701 = l_Lean_Expr_bvar___override(x_700);
x_702 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_702, 0, x_701);
lean_ctor_set(x_702, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_703 = lean_alloc_ctor(1, 1, 0);
} else {
 x_703 = x_679;
}
lean_ctor_set(x_703, 0, x_702);
x_704 = lean_apply_6(x_4, x_703, x_8, x_9, x_10, x_11, x_695);
return x_704;
}
case 1:
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_705 = lean_ctor_get(x_697, 0);
lean_inc(x_705);
lean_dec(x_697);
x_706 = l_Lean_Expr_fvar___override(x_705);
x_707 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_707, 0, x_706);
lean_ctor_set(x_707, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_708 = lean_alloc_ctor(1, 1, 0);
} else {
 x_708 = x_679;
}
lean_ctor_set(x_708, 0, x_707);
x_709 = lean_apply_6(x_4, x_708, x_8, x_9, x_10, x_11, x_695);
return x_709;
}
case 2:
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_710 = lean_ctor_get(x_697, 0);
lean_inc(x_710);
lean_dec(x_697);
x_711 = l_Lean_Expr_mvar___override(x_710);
x_712 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_713 = lean_alloc_ctor(1, 1, 0);
} else {
 x_713 = x_679;
}
lean_ctor_set(x_713, 0, x_712);
x_714 = lean_apply_6(x_4, x_713, x_8, x_9, x_10, x_11, x_695);
return x_714;
}
case 3:
{
lean_object* x_715; lean_object* x_716; lean_object* x_717; lean_object* x_718; lean_object* x_719; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_715 = lean_ctor_get(x_697, 0);
lean_inc(x_715);
lean_dec(x_697);
x_716 = l_Lean_Expr_sort___override(x_715);
x_717 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_717, 0, x_716);
lean_ctor_set(x_717, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_718 = lean_alloc_ctor(1, 1, 0);
} else {
 x_718 = x_679;
}
lean_ctor_set(x_718, 0, x_717);
x_719 = lean_apply_6(x_4, x_718, x_8, x_9, x_10, x_11, x_695);
return x_719;
}
case 4:
{
lean_object* x_720; 
x_720 = lean_ctor_get(x_697, 1);
lean_inc(x_720);
if (lean_obj_tag(x_720) == 0)
{
switch (lean_obj_tag(x_698)) {
case 0:
{
lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_721 = lean_ctor_get(x_697, 0);
lean_inc(x_721);
lean_dec(x_697);
x_722 = lean_ctor_get(x_698, 0);
lean_inc(x_722);
lean_dec(x_698);
x_723 = l_Lean_Expr_const___override(x_721, x_720);
x_724 = l_Lean_Expr_bvar___override(x_722);
x_725 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_725, 0, x_723);
lean_ctor_set(x_725, 1, x_724);
if (lean_is_scalar(x_679)) {
 x_726 = lean_alloc_ctor(1, 1, 0);
} else {
 x_726 = x_679;
}
lean_ctor_set(x_726, 0, x_725);
x_727 = lean_apply_6(x_4, x_726, x_8, x_9, x_10, x_11, x_695);
return x_727;
}
case 1:
{
lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; lean_object* x_734; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_728 = lean_ctor_get(x_697, 0);
lean_inc(x_728);
lean_dec(x_697);
x_729 = lean_ctor_get(x_698, 0);
lean_inc(x_729);
lean_dec(x_698);
x_730 = l_Lean_Expr_const___override(x_728, x_720);
x_731 = l_Lean_Expr_fvar___override(x_729);
x_732 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
if (lean_is_scalar(x_679)) {
 x_733 = lean_alloc_ctor(1, 1, 0);
} else {
 x_733 = x_679;
}
lean_ctor_set(x_733, 0, x_732);
x_734 = lean_apply_6(x_4, x_733, x_8, x_9, x_10, x_11, x_695);
return x_734;
}
case 2:
{
lean_object* x_735; lean_object* x_736; lean_object* x_737; lean_object* x_738; lean_object* x_739; lean_object* x_740; lean_object* x_741; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_735 = lean_ctor_get(x_697, 0);
lean_inc(x_735);
lean_dec(x_697);
x_736 = lean_ctor_get(x_698, 0);
lean_inc(x_736);
lean_dec(x_698);
x_737 = l_Lean_Expr_const___override(x_735, x_720);
x_738 = l_Lean_Expr_mvar___override(x_736);
x_739 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_739, 0, x_737);
lean_ctor_set(x_739, 1, x_738);
if (lean_is_scalar(x_679)) {
 x_740 = lean_alloc_ctor(1, 1, 0);
} else {
 x_740 = x_679;
}
lean_ctor_set(x_740, 0, x_739);
x_741 = lean_apply_6(x_4, x_740, x_8, x_9, x_10, x_11, x_695);
return x_741;
}
case 3:
{
lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; 
x_742 = lean_ctor_get(x_697, 0);
lean_inc(x_742);
lean_dec(x_697);
x_743 = lean_ctor_get(x_698, 0);
lean_inc(x_743);
lean_dec(x_698);
lean_inc(x_742);
x_744 = l_Lean_Expr_const___override(x_742, x_720);
x_745 = lean_box(0);
x_746 = l_Lean_Expr_sort___override(x_745);
switch (lean_obj_tag(x_743)) {
case 0:
{
lean_object* x_747; lean_object* x_748; lean_object* x_749; 
lean_dec(x_742);
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_747 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_747, 0, x_744);
lean_ctor_set(x_747, 1, x_746);
if (lean_is_scalar(x_679)) {
 x_748 = lean_alloc_ctor(1, 1, 0);
} else {
 x_748 = x_679;
}
lean_ctor_set(x_748, 0, x_747);
x_749 = lean_apply_6(x_4, x_748, x_8, x_9, x_10, x_11, x_695);
return x_749;
}
case 1:
{
lean_object* x_750; lean_object* x_751; lean_object* x_752; lean_object* x_753; lean_object* x_754; lean_object* x_755; 
lean_dec(x_746);
lean_dec(x_742);
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_750 = lean_ctor_get(x_743, 0);
lean_inc(x_750);
lean_dec(x_743);
x_751 = l_Lean_Level_succ___override(x_750);
x_752 = l_Lean_Expr_sort___override(x_751);
x_753 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_753, 0, x_744);
lean_ctor_set(x_753, 1, x_752);
if (lean_is_scalar(x_679)) {
 x_754 = lean_alloc_ctor(1, 1, 0);
} else {
 x_754 = x_679;
}
lean_ctor_set(x_754, 0, x_753);
x_755 = lean_apply_6(x_4, x_754, x_8, x_9, x_10, x_11, x_695);
return x_755;
}
case 2:
{
lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; lean_object* x_760; lean_object* x_761; lean_object* x_762; 
lean_dec(x_746);
lean_dec(x_742);
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_756 = lean_ctor_get(x_743, 0);
lean_inc(x_756);
x_757 = lean_ctor_get(x_743, 1);
lean_inc(x_757);
lean_dec(x_743);
x_758 = l_Lean_Level_max___override(x_756, x_757);
x_759 = l_Lean_Expr_sort___override(x_758);
x_760 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_760, 0, x_744);
lean_ctor_set(x_760, 1, x_759);
if (lean_is_scalar(x_679)) {
 x_761 = lean_alloc_ctor(1, 1, 0);
} else {
 x_761 = x_679;
}
lean_ctor_set(x_761, 0, x_760);
x_762 = lean_apply_6(x_4, x_761, x_8, x_9, x_10, x_11, x_695);
return x_762;
}
case 3:
{
lean_object* x_763; lean_object* x_764; lean_object* x_765; lean_object* x_766; lean_object* x_767; lean_object* x_768; lean_object* x_769; 
lean_dec(x_746);
lean_dec(x_742);
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_763 = lean_ctor_get(x_743, 0);
lean_inc(x_763);
x_764 = lean_ctor_get(x_743, 1);
lean_inc(x_764);
lean_dec(x_743);
x_765 = l_Lean_Level_imax___override(x_763, x_764);
x_766 = l_Lean_Expr_sort___override(x_765);
x_767 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_767, 0, x_744);
lean_ctor_set(x_767, 1, x_766);
if (lean_is_scalar(x_679)) {
 x_768 = lean_alloc_ctor(1, 1, 0);
} else {
 x_768 = x_679;
}
lean_ctor_set(x_768, 0, x_767);
x_769 = lean_apply_6(x_4, x_768, x_8, x_9, x_10, x_11, x_695);
return x_769;
}
case 4:
{
uint8_t x_770; 
lean_dec(x_744);
lean_dec(x_743);
lean_dec(x_4);
x_770 = lean_name_eq(x_742, x_678);
lean_dec(x_742);
if (x_770 == 0)
{
lean_object* x_771; lean_object* x_772; 
lean_dec(x_746);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_771 = lean_box(0);
if (lean_is_scalar(x_696)) {
 x_772 = lean_alloc_ctor(0, 2, 0);
} else {
 x_772 = x_696;
}
lean_ctor_set(x_772, 0, x_771);
lean_ctor_set(x_772, 1, x_695);
return x_772;
}
else
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; uint8_t x_778; 
lean_dec(x_696);
x_773 = l_Lean_Expr_getAppNumArgs(x_7);
lean_inc(x_773);
x_774 = lean_mk_array(x_773, x_746);
x_775 = lean_nat_sub(x_773, x_2);
lean_dec(x_773);
x_776 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg(x_16, x_692, x_7, x_774, x_775, x_695);
lean_dec(x_16);
x_777 = lean_ctor_get(x_776, 0);
lean_inc(x_777);
x_778 = lean_unbox(x_777);
lean_dec(x_777);
if (x_778 == 0)
{
lean_object* x_779; lean_object* x_780; lean_object* x_781; lean_object* x_782; 
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_779 = lean_ctor_get(x_776, 1);
lean_inc(x_779);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_780 = x_776;
} else {
 lean_dec_ref(x_776);
 x_780 = lean_box(0);
}
x_781 = lean_box(0);
if (lean_is_scalar(x_780)) {
 x_782 = lean_alloc_ctor(0, 2, 0);
} else {
 x_782 = x_780;
}
lean_ctor_set(x_782, 0, x_781);
lean_ctor_set(x_782, 1, x_779);
return x_782;
}
else
{
lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_852; lean_object* x_853; uint8_t x_854; 
x_783 = lean_ctor_get(x_776, 1);
lean_inc(x_783);
if (lean_is_exclusive(x_776)) {
 lean_ctor_release(x_776, 0);
 lean_ctor_release(x_776, 1);
 x_784 = x_776;
} else {
 lean_dec_ref(x_776);
 x_784 = lean_box(0);
}
x_785 = lean_box(x_15);
lean_inc(x_692);
lean_inc(x_3);
lean_inc(x_1);
lean_inc(x_2);
x_786 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1___boxed), 13, 6);
lean_closure_set(x_786, 0, x_2);
lean_closure_set(x_786, 1, x_785);
lean_closure_set(x_786, 2, x_1);
lean_closure_set(x_786, 3, x_3);
lean_closure_set(x_786, 4, x_678);
lean_closure_set(x_786, 5, x_692);
x_852 = l_Lean_InductiveVal_numCtors(x_691);
x_853 = lean_nat_add(x_852, x_14);
x_854 = lean_nat_dec_eq(x_13, x_853);
lean_dec(x_853);
if (x_854 == 0)
{
lean_dec(x_852);
x_787 = x_8;
x_788 = x_9;
x_789 = x_10;
x_790 = x_11;
x_791 = x_783;
goto block_851;
}
else
{
lean_object* x_855; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_691);
lean_inc(x_5);
x_855 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_trySimpleEnum(x_5, x_691, x_6, x_852, x_692, x_8, x_9, x_10, x_11, x_783);
if (lean_obj_tag(x_855) == 0)
{
lean_object* x_856; 
x_856 = lean_ctor_get(x_855, 0);
lean_inc(x_856);
if (lean_obj_tag(x_856) == 0)
{
lean_object* x_857; 
x_857 = lean_ctor_get(x_855, 1);
lean_inc(x_857);
lean_dec(x_855);
x_787 = x_8;
x_788 = x_9;
x_789 = x_10;
x_790 = x_11;
x_791 = x_857;
goto block_851;
}
else
{
lean_dec(x_856);
lean_dec(x_786);
lean_dec(x_784);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_855;
}
}
else
{
lean_dec(x_786);
lean_dec(x_784);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_855;
}
}
block_851:
{
uint8_t x_792; 
x_792 = lean_nat_dec_lt(x_14, x_13);
if (x_792 == 0)
{
lean_object* x_793; lean_object* x_794; 
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_787);
lean_dec(x_786);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_793 = lean_box(0);
if (lean_is_scalar(x_784)) {
 x_794 = lean_alloc_ctor(0, 2, 0);
} else {
 x_794 = x_784;
}
lean_ctor_set(x_794, 0, x_793);
lean_ctor_set(x_794, 1, x_791);
return x_794;
}
else
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; 
lean_dec(x_784);
x_795 = lean_unsigned_to_nat(3u);
x_796 = lean_nat_sub(x_13, x_795);
x_797 = lean_mk_empty_array_with_capacity(x_796);
lean_inc(x_2);
lean_inc(x_3);
x_798 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_798, 0, x_3);
lean_ctor_set(x_798, 1, x_796);
lean_ctor_set(x_798, 2, x_2);
x_799 = lean_box(0);
x_800 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_800, 0, x_799);
lean_ctor_set(x_800, 1, x_797);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
lean_inc(x_787);
x_801 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg(x_6, x_692, x_798, x_800, x_3, x_787, x_788, x_789, x_790, x_791);
lean_dec(x_798);
lean_dec(x_692);
if (lean_obj_tag(x_801) == 0)
{
lean_object* x_802; lean_object* x_803; 
x_802 = lean_ctor_get(x_801, 0);
lean_inc(x_802);
x_803 = lean_ctor_get(x_802, 0);
lean_inc(x_803);
if (lean_obj_tag(x_803) == 0)
{
lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; 
x_804 = lean_ctor_get(x_801, 1);
lean_inc(x_804);
lean_dec(x_801);
x_805 = lean_nat_sub(x_13, x_2);
lean_dec(x_2);
lean_dec(x_13);
x_806 = lean_array_get(x_1, x_6, x_805);
lean_dec(x_805);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
lean_inc(x_787);
x_807 = lean_infer_type(x_806, x_787, x_788, x_789, x_790, x_804);
if (lean_obj_tag(x_807) == 0)
{
lean_object* x_808; lean_object* x_809; lean_object* x_810; 
x_808 = lean_ctor_get(x_807, 0);
lean_inc(x_808);
x_809 = lean_ctor_get(x_807, 1);
lean_inc(x_809);
lean_dec(x_807);
lean_inc(x_790);
lean_inc(x_789);
lean_inc(x_788);
lean_inc(x_787);
x_810 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_808, x_786, x_15, x_787, x_788, x_789, x_790, x_809);
if (lean_obj_tag(x_810) == 0)
{
lean_object* x_811; uint8_t x_812; 
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
x_812 = lean_unbox(x_811);
lean_dec(x_811);
if (x_812 == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; 
lean_dec(x_802);
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_787);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_5);
x_813 = lean_ctor_get(x_810, 1);
lean_inc(x_813);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_814 = x_810;
} else {
 lean_dec_ref(x_810);
 x_814 = lean_box(0);
}
x_815 = lean_box(0);
if (lean_is_scalar(x_814)) {
 x_816 = lean_alloc_ctor(0, 2, 0);
} else {
 x_816 = x_814;
}
lean_ctor_set(x_816, 0, x_815);
lean_ctor_set(x_816, 1, x_813);
return x_816;
}
else
{
lean_object* x_817; lean_object* x_818; lean_object* x_819; 
x_817 = lean_ctor_get(x_810, 1);
lean_inc(x_817);
lean_dec(x_810);
x_818 = lean_ctor_get(x_802, 1);
lean_inc(x_818);
lean_dec(x_802);
lean_inc(x_818);
lean_inc(x_691);
x_819 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_verifyEnumWithDefault(x_5, x_691, x_818, x_787, x_788, x_789, x_790, x_817);
if (lean_obj_tag(x_819) == 0)
{
lean_object* x_820; uint8_t x_821; 
x_820 = lean_ctor_get(x_819, 0);
lean_inc(x_820);
x_821 = lean_unbox(x_820);
lean_dec(x_820);
if (x_821 == 0)
{
lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; 
lean_dec(x_818);
lean_dec(x_691);
lean_dec(x_679);
x_822 = lean_ctor_get(x_819, 1);
lean_inc(x_822);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_823 = x_819;
} else {
 lean_dec_ref(x_819);
 x_823 = lean_box(0);
}
x_824 = lean_box(0);
if (lean_is_scalar(x_823)) {
 x_825 = lean_alloc_ctor(0, 2, 0);
} else {
 x_825 = x_823;
}
lean_ctor_set(x_825, 0, x_824);
lean_ctor_set(x_825, 1, x_822);
return x_825;
}
else
{
lean_object* x_826; lean_object* x_827; lean_object* x_828; lean_object* x_829; lean_object* x_830; 
x_826 = lean_ctor_get(x_819, 1);
lean_inc(x_826);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_827 = x_819;
} else {
 lean_dec_ref(x_819);
 x_827 = lean_box(0);
}
x_828 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_828, 0, x_691);
lean_ctor_set(x_828, 1, x_818);
if (lean_is_scalar(x_679)) {
 x_829 = lean_alloc_ctor(1, 1, 0);
} else {
 x_829 = x_679;
}
lean_ctor_set(x_829, 0, x_828);
if (lean_is_scalar(x_827)) {
 x_830 = lean_alloc_ctor(0, 2, 0);
} else {
 x_830 = x_827;
}
lean_ctor_set(x_830, 0, x_829);
lean_ctor_set(x_830, 1, x_826);
return x_830;
}
}
else
{
lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; 
lean_dec(x_818);
lean_dec(x_691);
lean_dec(x_679);
x_831 = lean_ctor_get(x_819, 0);
lean_inc(x_831);
x_832 = lean_ctor_get(x_819, 1);
lean_inc(x_832);
if (lean_is_exclusive(x_819)) {
 lean_ctor_release(x_819, 0);
 lean_ctor_release(x_819, 1);
 x_833 = x_819;
} else {
 lean_dec_ref(x_819);
 x_833 = lean_box(0);
}
if (lean_is_scalar(x_833)) {
 x_834 = lean_alloc_ctor(1, 2, 0);
} else {
 x_834 = x_833;
}
lean_ctor_set(x_834, 0, x_831);
lean_ctor_set(x_834, 1, x_832);
return x_834;
}
}
}
else
{
lean_object* x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; 
lean_dec(x_802);
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_787);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_5);
x_835 = lean_ctor_get(x_810, 0);
lean_inc(x_835);
x_836 = lean_ctor_get(x_810, 1);
lean_inc(x_836);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_837 = x_810;
} else {
 lean_dec_ref(x_810);
 x_837 = lean_box(0);
}
if (lean_is_scalar(x_837)) {
 x_838 = lean_alloc_ctor(1, 2, 0);
} else {
 x_838 = x_837;
}
lean_ctor_set(x_838, 0, x_835);
lean_ctor_set(x_838, 1, x_836);
return x_838;
}
}
else
{
lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_802);
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_787);
lean_dec(x_786);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_5);
x_839 = lean_ctor_get(x_807, 0);
lean_inc(x_839);
x_840 = lean_ctor_get(x_807, 1);
lean_inc(x_840);
if (lean_is_exclusive(x_807)) {
 lean_ctor_release(x_807, 0);
 lean_ctor_release(x_807, 1);
 x_841 = x_807;
} else {
 lean_dec_ref(x_807);
 x_841 = lean_box(0);
}
if (lean_is_scalar(x_841)) {
 x_842 = lean_alloc_ctor(1, 2, 0);
} else {
 x_842 = x_841;
}
lean_ctor_set(x_842, 0, x_839);
lean_ctor_set(x_842, 1, x_840);
return x_842;
}
}
else
{
lean_object* x_843; lean_object* x_844; lean_object* x_845; lean_object* x_846; 
lean_dec(x_802);
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_787);
lean_dec(x_786);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_843 = lean_ctor_get(x_801, 1);
lean_inc(x_843);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_844 = x_801;
} else {
 lean_dec_ref(x_801);
 x_844 = lean_box(0);
}
x_845 = lean_ctor_get(x_803, 0);
lean_inc(x_845);
lean_dec(x_803);
if (lean_is_scalar(x_844)) {
 x_846 = lean_alloc_ctor(0, 2, 0);
} else {
 x_846 = x_844;
}
lean_ctor_set(x_846, 0, x_845);
lean_ctor_set(x_846, 1, x_843);
return x_846;
}
}
else
{
lean_object* x_847; lean_object* x_848; lean_object* x_849; lean_object* x_850; 
lean_dec(x_790);
lean_dec(x_789);
lean_dec(x_788);
lean_dec(x_787);
lean_dec(x_786);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_13);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_847 = lean_ctor_get(x_801, 0);
lean_inc(x_847);
x_848 = lean_ctor_get(x_801, 1);
lean_inc(x_848);
if (lean_is_exclusive(x_801)) {
 lean_ctor_release(x_801, 0);
 lean_ctor_release(x_801, 1);
 x_849 = x_801;
} else {
 lean_dec_ref(x_801);
 x_849 = lean_box(0);
}
if (lean_is_scalar(x_849)) {
 x_850 = lean_alloc_ctor(1, 2, 0);
} else {
 x_850 = x_849;
}
lean_ctor_set(x_850, 0, x_847);
lean_ctor_set(x_850, 1, x_848);
return x_850;
}
}
}
}
}
}
default: 
{
lean_object* x_858; lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; 
lean_dec(x_746);
lean_dec(x_742);
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_858 = lean_ctor_get(x_743, 0);
lean_inc(x_858);
lean_dec(x_743);
x_859 = l_Lean_Level_mvar___override(x_858);
x_860 = l_Lean_Expr_sort___override(x_859);
x_861 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_861, 0, x_744);
lean_ctor_set(x_861, 1, x_860);
if (lean_is_scalar(x_679)) {
 x_862 = lean_alloc_ctor(1, 1, 0);
} else {
 x_862 = x_679;
}
lean_ctor_set(x_862, 0, x_861);
x_863 = lean_apply_6(x_4, x_862, x_8, x_9, x_10, x_11, x_695);
return x_863;
}
}
}
case 4:
{
lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_864 = lean_ctor_get(x_697, 0);
lean_inc(x_864);
lean_dec(x_697);
x_865 = lean_ctor_get(x_698, 0);
lean_inc(x_865);
x_866 = lean_ctor_get(x_698, 1);
lean_inc(x_866);
lean_dec(x_698);
x_867 = l_Lean_Expr_const___override(x_864, x_720);
x_868 = l_Lean_Expr_const___override(x_865, x_866);
x_869 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_869, 0, x_867);
lean_ctor_set(x_869, 1, x_868);
if (lean_is_scalar(x_679)) {
 x_870 = lean_alloc_ctor(1, 1, 0);
} else {
 x_870 = x_679;
}
lean_ctor_set(x_870, 0, x_869);
x_871 = lean_apply_6(x_4, x_870, x_8, x_9, x_10, x_11, x_695);
return x_871;
}
case 5:
{
lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_872 = lean_ctor_get(x_697, 0);
lean_inc(x_872);
lean_dec(x_697);
x_873 = lean_ctor_get(x_698, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_698, 1);
lean_inc(x_874);
lean_dec(x_698);
x_875 = l_Lean_Expr_const___override(x_872, x_720);
x_876 = l_Lean_Expr_app___override(x_873, x_874);
x_877 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_877, 0, x_875);
lean_ctor_set(x_877, 1, x_876);
if (lean_is_scalar(x_679)) {
 x_878 = lean_alloc_ctor(1, 1, 0);
} else {
 x_878 = x_679;
}
lean_ctor_set(x_878, 0, x_877);
x_879 = lean_apply_6(x_4, x_878, x_8, x_9, x_10, x_11, x_695);
return x_879;
}
case 6:
{
lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; uint8_t x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_880 = lean_ctor_get(x_697, 0);
lean_inc(x_880);
lean_dec(x_697);
x_881 = lean_ctor_get(x_698, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_698, 1);
lean_inc(x_882);
x_883 = lean_ctor_get(x_698, 2);
lean_inc(x_883);
x_884 = lean_ctor_get_uint8(x_698, sizeof(void*)*3 + 8);
lean_dec(x_698);
x_885 = l_Lean_Expr_const___override(x_880, x_720);
x_886 = l_Lean_Expr_lam___override(x_881, x_882, x_883, x_884);
x_887 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_887, 0, x_885);
lean_ctor_set(x_887, 1, x_886);
if (lean_is_scalar(x_679)) {
 x_888 = lean_alloc_ctor(1, 1, 0);
} else {
 x_888 = x_679;
}
lean_ctor_set(x_888, 0, x_887);
x_889 = lean_apply_6(x_4, x_888, x_8, x_9, x_10, x_11, x_695);
return x_889;
}
case 7:
{
lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; uint8_t x_894; lean_object* x_895; lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_890 = lean_ctor_get(x_697, 0);
lean_inc(x_890);
lean_dec(x_697);
x_891 = lean_ctor_get(x_698, 0);
lean_inc(x_891);
x_892 = lean_ctor_get(x_698, 1);
lean_inc(x_892);
x_893 = lean_ctor_get(x_698, 2);
lean_inc(x_893);
x_894 = lean_ctor_get_uint8(x_698, sizeof(void*)*3 + 8);
lean_dec(x_698);
x_895 = l_Lean_Expr_const___override(x_890, x_720);
x_896 = l_Lean_Expr_forallE___override(x_891, x_892, x_893, x_894);
x_897 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_897, 0, x_895);
lean_ctor_set(x_897, 1, x_896);
if (lean_is_scalar(x_679)) {
 x_898 = lean_alloc_ctor(1, 1, 0);
} else {
 x_898 = x_679;
}
lean_ctor_set(x_898, 0, x_897);
x_899 = lean_apply_6(x_4, x_898, x_8, x_9, x_10, x_11, x_695);
return x_899;
}
case 8:
{
lean_object* x_900; lean_object* x_901; lean_object* x_902; lean_object* x_903; lean_object* x_904; uint8_t x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_900 = lean_ctor_get(x_697, 0);
lean_inc(x_900);
lean_dec(x_697);
x_901 = lean_ctor_get(x_698, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_698, 1);
lean_inc(x_902);
x_903 = lean_ctor_get(x_698, 2);
lean_inc(x_903);
x_904 = lean_ctor_get(x_698, 3);
lean_inc(x_904);
x_905 = lean_ctor_get_uint8(x_698, sizeof(void*)*4 + 8);
lean_dec(x_698);
x_906 = l_Lean_Expr_const___override(x_900, x_720);
x_907 = l_Lean_Expr_letE___override(x_901, x_902, x_903, x_904, x_905);
x_908 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_908, 0, x_906);
lean_ctor_set(x_908, 1, x_907);
if (lean_is_scalar(x_679)) {
 x_909 = lean_alloc_ctor(1, 1, 0);
} else {
 x_909 = x_679;
}
lean_ctor_set(x_909, 0, x_908);
x_910 = lean_apply_6(x_4, x_909, x_8, x_9, x_10, x_11, x_695);
return x_910;
}
case 9:
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; lean_object* x_915; lean_object* x_916; lean_object* x_917; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_911 = lean_ctor_get(x_697, 0);
lean_inc(x_911);
lean_dec(x_697);
x_912 = lean_ctor_get(x_698, 0);
lean_inc(x_912);
lean_dec(x_698);
x_913 = l_Lean_Expr_const___override(x_911, x_720);
x_914 = l_Lean_Expr_lit___override(x_912);
x_915 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_915, 0, x_913);
lean_ctor_set(x_915, 1, x_914);
if (lean_is_scalar(x_679)) {
 x_916 = lean_alloc_ctor(1, 1, 0);
} else {
 x_916 = x_679;
}
lean_ctor_set(x_916, 0, x_915);
x_917 = lean_apply_6(x_4, x_916, x_8, x_9, x_10, x_11, x_695);
return x_917;
}
case 10:
{
lean_object* x_918; lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_918 = lean_ctor_get(x_697, 0);
lean_inc(x_918);
lean_dec(x_697);
x_919 = lean_ctor_get(x_698, 0);
lean_inc(x_919);
x_920 = lean_ctor_get(x_698, 1);
lean_inc(x_920);
lean_dec(x_698);
x_921 = l_Lean_Expr_const___override(x_918, x_720);
x_922 = l_Lean_Expr_mdata___override(x_919, x_920);
x_923 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_923, 0, x_921);
lean_ctor_set(x_923, 1, x_922);
if (lean_is_scalar(x_679)) {
 x_924 = lean_alloc_ctor(1, 1, 0);
} else {
 x_924 = x_679;
}
lean_ctor_set(x_924, 0, x_923);
x_925 = lean_apply_6(x_4, x_924, x_8, x_9, x_10, x_11, x_695);
return x_925;
}
default: 
{
lean_object* x_926; lean_object* x_927; lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_926 = lean_ctor_get(x_697, 0);
lean_inc(x_926);
lean_dec(x_697);
x_927 = lean_ctor_get(x_698, 0);
lean_inc(x_927);
x_928 = lean_ctor_get(x_698, 1);
lean_inc(x_928);
x_929 = lean_ctor_get(x_698, 2);
lean_inc(x_929);
lean_dec(x_698);
x_930 = l_Lean_Expr_const___override(x_926, x_720);
x_931 = l_Lean_Expr_proj___override(x_927, x_928, x_929);
x_932 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_932, 0, x_930);
lean_ctor_set(x_932, 1, x_931);
if (lean_is_scalar(x_679)) {
 x_933 = lean_alloc_ctor(1, 1, 0);
} else {
 x_933 = x_679;
}
lean_ctor_set(x_933, 0, x_932);
x_934 = lean_apply_6(x_4, x_933, x_8, x_9, x_10, x_11, x_695);
return x_934;
}
}
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; lean_object* x_939; lean_object* x_940; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_935 = lean_ctor_get(x_697, 0);
lean_inc(x_935);
lean_dec(x_697);
lean_inc(x_720);
x_936 = l_Lean_Expr_const___override(x_935, x_720);
if (lean_is_exclusive(x_720)) {
 lean_ctor_release(x_720, 0);
 lean_ctor_release(x_720, 1);
 x_937 = x_720;
} else {
 lean_dec_ref(x_720);
 x_937 = lean_box(0);
}
if (lean_is_scalar(x_937)) {
 x_938 = lean_alloc_ctor(0, 2, 0);
} else {
 x_938 = x_937;
 lean_ctor_set_tag(x_938, 0);
}
lean_ctor_set(x_938, 0, x_936);
lean_ctor_set(x_938, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_939 = lean_alloc_ctor(1, 1, 0);
} else {
 x_939 = x_679;
}
lean_ctor_set(x_939, 0, x_938);
x_940 = lean_apply_6(x_4, x_939, x_8, x_9, x_10, x_11, x_695);
return x_940;
}
}
case 5:
{
lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_941 = lean_ctor_get(x_697, 0);
lean_inc(x_941);
x_942 = lean_ctor_get(x_697, 1);
lean_inc(x_942);
lean_dec(x_697);
x_943 = l_Lean_Expr_app___override(x_941, x_942);
x_944 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_944, 0, x_943);
lean_ctor_set(x_944, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_945 = lean_alloc_ctor(1, 1, 0);
} else {
 x_945 = x_679;
}
lean_ctor_set(x_945, 0, x_944);
x_946 = lean_apply_6(x_4, x_945, x_8, x_9, x_10, x_11, x_695);
return x_946;
}
case 6:
{
lean_object* x_947; lean_object* x_948; lean_object* x_949; uint8_t x_950; lean_object* x_951; lean_object* x_952; lean_object* x_953; lean_object* x_954; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_947 = lean_ctor_get(x_697, 0);
lean_inc(x_947);
x_948 = lean_ctor_get(x_697, 1);
lean_inc(x_948);
x_949 = lean_ctor_get(x_697, 2);
lean_inc(x_949);
x_950 = lean_ctor_get_uint8(x_697, sizeof(void*)*3 + 8);
lean_dec(x_697);
x_951 = l_Lean_Expr_lam___override(x_947, x_948, x_949, x_950);
x_952 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_952, 0, x_951);
lean_ctor_set(x_952, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_953 = lean_alloc_ctor(1, 1, 0);
} else {
 x_953 = x_679;
}
lean_ctor_set(x_953, 0, x_952);
x_954 = lean_apply_6(x_4, x_953, x_8, x_9, x_10, x_11, x_695);
return x_954;
}
case 7:
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; uint8_t x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_955 = lean_ctor_get(x_697, 0);
lean_inc(x_955);
x_956 = lean_ctor_get(x_697, 1);
lean_inc(x_956);
x_957 = lean_ctor_get(x_697, 2);
lean_inc(x_957);
x_958 = lean_ctor_get_uint8(x_697, sizeof(void*)*3 + 8);
lean_dec(x_697);
x_959 = l_Lean_Expr_forallE___override(x_955, x_956, x_957, x_958);
x_960 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_960, 0, x_959);
lean_ctor_set(x_960, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_961 = lean_alloc_ctor(1, 1, 0);
} else {
 x_961 = x_679;
}
lean_ctor_set(x_961, 0, x_960);
x_962 = lean_apply_6(x_4, x_961, x_8, x_9, x_10, x_11, x_695);
return x_962;
}
case 8:
{
lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; uint8_t x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_963 = lean_ctor_get(x_697, 0);
lean_inc(x_963);
x_964 = lean_ctor_get(x_697, 1);
lean_inc(x_964);
x_965 = lean_ctor_get(x_697, 2);
lean_inc(x_965);
x_966 = lean_ctor_get(x_697, 3);
lean_inc(x_966);
x_967 = lean_ctor_get_uint8(x_697, sizeof(void*)*4 + 8);
lean_dec(x_697);
x_968 = l_Lean_Expr_letE___override(x_963, x_964, x_965, x_966, x_967);
x_969 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_969, 0, x_968);
lean_ctor_set(x_969, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_970 = lean_alloc_ctor(1, 1, 0);
} else {
 x_970 = x_679;
}
lean_ctor_set(x_970, 0, x_969);
x_971 = lean_apply_6(x_4, x_970, x_8, x_9, x_10, x_11, x_695);
return x_971;
}
case 9:
{
lean_object* x_972; lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_972 = lean_ctor_get(x_697, 0);
lean_inc(x_972);
lean_dec(x_697);
x_973 = l_Lean_Expr_lit___override(x_972);
x_974 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_974, 0, x_973);
lean_ctor_set(x_974, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_975 = lean_alloc_ctor(1, 1, 0);
} else {
 x_975 = x_679;
}
lean_ctor_set(x_975, 0, x_974);
x_976 = lean_apply_6(x_4, x_975, x_8, x_9, x_10, x_11, x_695);
return x_976;
}
case 10:
{
lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_977 = lean_ctor_get(x_697, 0);
lean_inc(x_977);
x_978 = lean_ctor_get(x_697, 1);
lean_inc(x_978);
lean_dec(x_697);
x_979 = l_Lean_Expr_mdata___override(x_977, x_978);
x_980 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_980, 0, x_979);
lean_ctor_set(x_980, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_981 = lean_alloc_ctor(1, 1, 0);
} else {
 x_981 = x_679;
}
lean_ctor_set(x_981, 0, x_980);
x_982 = lean_apply_6(x_4, x_981, x_8, x_9, x_10, x_11, x_695);
return x_982;
}
default: 
{
lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; 
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_983 = lean_ctor_get(x_697, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_697, 1);
lean_inc(x_984);
x_985 = lean_ctor_get(x_697, 2);
lean_inc(x_985);
lean_dec(x_697);
x_986 = l_Lean_Expr_proj___override(x_983, x_984, x_985);
x_987 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_987, 0, x_986);
lean_ctor_set(x_987, 1, x_698);
if (lean_is_scalar(x_679)) {
 x_988 = lean_alloc_ctor(1, 1, 0);
} else {
 x_988 = x_679;
}
lean_ctor_set(x_988, 0, x_987);
x_989 = lean_apply_6(x_4, x_988, x_8, x_9, x_10, x_11, x_695);
return x_989;
}
}
}
else
{
lean_object* x_990; lean_object* x_991; 
lean_dec(x_698);
lean_dec(x_697);
lean_dec(x_696);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_990 = lean_box(0);
x_991 = lean_apply_6(x_4, x_990, x_8, x_9, x_10, x_11, x_695);
return x_991;
}
}
else
{
lean_object* x_992; lean_object* x_993; lean_object* x_994; 
lean_dec(x_694);
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_992 = lean_ctor_get(x_693, 1);
lean_inc(x_992);
lean_dec(x_693);
x_993 = lean_box(0);
x_994 = lean_apply_6(x_4, x_993, x_8, x_9, x_10, x_11, x_992);
return x_994;
}
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; 
lean_dec(x_692);
lean_dec(x_691);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_995 = lean_ctor_get(x_693, 0);
lean_inc(x_995);
x_996 = lean_ctor_get(x_693, 1);
lean_inc(x_996);
if (lean_is_exclusive(x_693)) {
 lean_ctor_release(x_693, 0);
 lean_ctor_release(x_693, 1);
 x_997 = x_693;
} else {
 lean_dec_ref(x_693);
 x_997 = lean_box(0);
}
if (lean_is_scalar(x_997)) {
 x_998 = lean_alloc_ctor(1, 2, 0);
} else {
 x_998 = x_997;
}
lean_ctor_set(x_998, 0, x_995);
lean_ctor_set(x_998, 1, x_996);
return x_998;
}
}
else
{
lean_object* x_999; lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
lean_dec(x_689);
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_999 = lean_ctor_get(x_688, 1);
lean_inc(x_999);
lean_dec(x_688);
x_1000 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_1001 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.isSupportedMatch", 61, 61);
x_1002 = lean_unsigned_to_nat(36u);
x_1003 = lean_unsigned_to_nat(65u);
x_1004 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_1005 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1000, x_1001, x_1002, x_1003, x_1004);
lean_dec(x_1004);
lean_dec(x_1001);
lean_dec(x_1000);
x_1006 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__5(x_1005, x_8, x_9, x_10, x_11, x_999);
return x_1006;
}
}
else
{
lean_object* x_1007; lean_object* x_1008; lean_object* x_1009; lean_object* x_1010; 
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1007 = lean_ctor_get(x_688, 0);
lean_inc(x_1007);
x_1008 = lean_ctor_get(x_688, 1);
lean_inc(x_1008);
if (lean_is_exclusive(x_688)) {
 lean_ctor_release(x_688, 0);
 lean_ctor_release(x_688, 1);
 x_1009 = x_688;
} else {
 lean_dec_ref(x_688);
 x_1009 = lean_box(0);
}
if (lean_is_scalar(x_1009)) {
 x_1010 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1010 = x_1009;
}
lean_ctor_set(x_1010, 0, x_1007);
lean_ctor_set(x_1010, 1, x_1008);
return x_1010;
}
}
}
else
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_679);
lean_dec(x_678);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1011 = lean_ctor_get(x_680, 0);
lean_inc(x_1011);
x_1012 = lean_ctor_get(x_680, 1);
lean_inc(x_1012);
if (lean_is_exclusive(x_680)) {
 lean_ctor_release(x_680, 0);
 lean_ctor_release(x_680, 1);
 x_1013 = x_680;
} else {
 lean_dec_ref(x_680);
 x_1013 = lean_box(0);
}
if (lean_is_scalar(x_1013)) {
 x_1014 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1014 = x_1013;
}
lean_ctor_set(x_1014, 0, x_1011);
lean_ctor_set(x_1014, 1, x_1012);
return x_1014;
}
}
}
}
else
{
uint8_t x_1015; 
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1015 = !lean_is_exclusive(x_17);
if (x_1015 == 0)
{
return x_17;
}
else
{
lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; 
x_1016 = lean_ctor_get(x_17, 0);
x_1017 = lean_ctor_get(x_17, 1);
lean_inc(x_1017);
lean_inc(x_1016);
lean_dec(x_17);
x_1018 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1018, 0, x_1016);
lean_ctor_set(x_1018, 1, x_1017);
return x_1018;
}
}
}
else
{
lean_object* x_1019; lean_object* x_1020; 
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_1019 = lean_box(0);
x_1020 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1020, 0, x_1019);
lean_ctor_set(x_1020, 1, x_12);
return x_1020;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
lean_inc(x_1);
x_7 = l_Lean_Meta_getMatcherInfo_x3f___at___Lean_Meta_reduceMatcher_x3f_spec__0___redArg(x_1, x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_7);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; uint8_t x_23; 
x_16 = lean_ctor_get(x_7, 1);
x_17 = lean_ctor_get(x_7, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = lean_ctor_get(x_18, 4);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_array_get_size(x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_dec_eq(x_20, x_21);
lean_dec(x_20);
x_23 = l_instDecidableNot___redArg(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = l_Lean_Meta_Match_instInhabitedDiscrInfo;
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_array_get(x_24, x_19, x_25);
lean_dec(x_19);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_free_object(x_7);
x_27 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_16);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
if (lean_obj_tag(x_28) == 1)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__0___boxed), 6, 0);
x_32 = l_Lean_instInhabitedExpr;
lean_inc(x_30);
x_33 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__2___boxed), 12, 5);
lean_closure_set(x_33, 0, x_32);
lean_closure_set(x_33, 1, x_21);
lean_closure_set(x_33, 2, x_25);
lean_closure_set(x_33, 3, x_31);
lean_closure_set(x_33, 4, x_30);
x_34 = lean_ctor_get(x_30, 0);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
lean_dec(x_34);
x_36 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_35, x_33, x_23, x_2, x_3, x_4, x_5, x_29);
return x_36;
}
else
{
uint8_t x_37; 
lean_dec(x_28);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_27);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_27, 0);
lean_dec(x_38);
x_39 = lean_box(0);
lean_ctor_set(x_27, 0, x_39);
return x_27;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
lean_dec(x_27);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_43 = !lean_is_exclusive(x_27);
if (x_43 == 0)
{
return x_27;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_27, 0);
x_45 = lean_ctor_get(x_27, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_27);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_47; 
lean_dec(x_26);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_47 = lean_box(0);
lean_ctor_set(x_7, 0, x_47);
return x_7;
}
}
else
{
lean_object* x_48; 
lean_dec(x_19);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
lean_ctor_set(x_7, 0, x_48);
return x_7;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_49 = lean_ctor_get(x_7, 1);
lean_inc(x_49);
lean_dec(x_7);
x_50 = lean_ctor_get(x_8, 0);
lean_inc(x_50);
lean_dec(x_8);
x_51 = lean_ctor_get(x_50, 4);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_array_get_size(x_51);
x_53 = lean_unsigned_to_nat(1u);
x_54 = lean_nat_dec_eq(x_52, x_53);
lean_dec(x_52);
x_55 = l_instDecidableNot___redArg(x_54);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = l_Lean_Meta_Match_instInhabitedDiscrInfo;
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_array_get(x_56, x_51, x_57);
lean_dec(x_51);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; 
x_59 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_2, x_3, x_4, x_5, x_49);
if (lean_obj_tag(x_59) == 0)
{
lean_object* x_60; 
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
if (lean_obj_tag(x_60) == 1)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 0);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__0___boxed), 6, 0);
x_64 = l_Lean_instInhabitedExpr;
lean_inc(x_62);
x_65 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__2___boxed), 12, 5);
lean_closure_set(x_65, 0, x_64);
lean_closure_set(x_65, 1, x_53);
lean_closure_set(x_65, 2, x_57);
lean_closure_set(x_65, 3, x_63);
lean_closure_set(x_65, 4, x_62);
x_66 = lean_ctor_get(x_62, 0);
lean_inc(x_66);
lean_dec(x_62);
x_67 = lean_ctor_get(x_66, 2);
lean_inc(x_67);
lean_dec(x_66);
x_68 = l_Lean_Meta_forallTelescope___at___Lean_Meta_mapForallTelescope_x27_spec__0(lean_box(0), x_67, x_65, x_55, x_2, x_3, x_4, x_5, x_61);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
lean_dec(x_60);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_69 = lean_ctor_get(x_59, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_70 = x_59;
} else {
 lean_dec_ref(x_59);
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
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
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
lean_dec(x_58);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_77 = lean_box(0);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_49);
return x_78;
}
}
else
{
lean_object* x_79; lean_object* x_80; 
lean_dec(x_51);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_49);
return x_80;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_1);
lean_dec(x_1);
x_9 = l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0_spec__0(x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Expr_withAppAux___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch___lam__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_builtinTypes() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_1 = lean_mk_string_unchecked("BitVec", 6, 6);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_mk_string_unchecked("Bool", 4, 4);
x_4 = l_Lean_Name_mkStr1(x_3);
x_5 = lean_mk_string_unchecked("UInt8", 5, 5);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_mk_string_unchecked("UInt16", 6, 6);
x_8 = l_Lean_Name_mkStr1(x_7);
x_9 = lean_mk_string_unchecked("UInt32", 6, 6);
x_10 = l_Lean_Name_mkStr1(x_9);
x_11 = lean_mk_string_unchecked("UInt64", 6, 6);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_mk_string_unchecked("USize", 5, 5);
x_14 = l_Lean_Name_mkStr1(x_13);
x_15 = lean_mk_string_unchecked("Int8", 4, 4);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = lean_mk_string_unchecked("Int16", 5, 5);
x_18 = l_Lean_Name_mkStr1(x_17);
x_19 = lean_mk_string_unchecked("Int32", 5, 5);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_mk_string_unchecked("Int64", 5, 5);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = lean_mk_string_unchecked("ISize", 5, 5);
x_24 = l_Lean_Name_mkStr1(x_23);
x_25 = lean_unsigned_to_nat(12u);
x_26 = lean_mk_empty_array_with_capacity(x_25);
x_27 = lean_array_push(x_26, x_2);
x_28 = lean_array_push(x_27, x_4);
x_29 = lean_array_push(x_28, x_6);
x_30 = lean_array_push(x_29, x_8);
x_31 = lean_array_push(x_30, x_10);
x_32 = lean_array_push(x_31, x_12);
x_33 = lean_array_push(x_32, x_14);
x_34 = lean_array_push(x_33, x_16);
x_35 = lean_array_push(x_34, x_18);
x_36 = lean_array_push(x_35, x_20);
x_37 = lean_array_push(x_36, x_22);
x_38 = lean_array_push(x_37, x_24);
return x_38;
}
}
LEAN_EXPORT uint8_t l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isBuiltIn(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = l_Lean_Name_instBEq;
x_3 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_builtinTypes;
x_4 = l_Array_contains___redArg(x_2, x_3, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isBuiltIn___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isBuiltIn(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_7, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
lean_inc(x_1);
x_16 = l_Lean_Environment_find_x3f(x_13, x_1, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_free_object(x_9);
x_17 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_unbox(x_14);
x_20 = l_Lean_MessageData_ofConstName(x_1, x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_mk_string_unchecked("'", 1, 1);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(x_24, x_4, x_5, x_6, x_7, x_12);
return x_25;
}
else
{
lean_object* x_26; 
lean_dec(x_1);
x_26 = lean_ctor_get(x_16, 0);
lean_inc(x_26);
lean_dec(x_16);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_1);
x_32 = l_Lean_Environment_find_x3f(x_29, x_1, x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_unbox(x_30);
x_36 = l_Lean_MessageData_ofConstName(x_1, x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("'", 1, 1);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(x_40, x_4, x_5, x_6, x_7, x_28);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_1);
x_42 = lean_ctor_get(x_32, 0);
lean_inc(x_42);
lean_dec(x_32);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_28);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__2(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_box(1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0(x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
if (lean_obj_tag(x_16) == 6)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
lean_dec(x_16);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_ctor_get(x_22, 4);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_nat_dec_eq(x_24, x_23);
lean_dec(x_24);
x_26 = lean_box(x_25);
lean_inc(x_17);
lean_ctor_set(x_14, 0, x_26);
x_18 = x_14;
x_19 = x_25;
goto block_21;
}
else
{
lean_object* x_27; 
lean_dec(x_16);
x_27 = lean_box(x_1);
lean_inc(x_17);
lean_ctor_set(x_14, 0, x_27);
x_18 = x_14;
x_19 = x_1;
goto block_21;
}
block_21:
{
if (x_19 == 0)
{
lean_dec(x_17);
lean_dec(x_13);
return x_18;
}
else
{
lean_dec(x_18);
x_2 = x_13;
x_9 = x_17;
goto _start;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
if (lean_obj_tag(x_28) == 6)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_28, 0);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_ctor_get(x_34, 4);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_nat_dec_eq(x_36, x_35);
lean_dec(x_36);
x_38 = lean_box(x_37);
lean_inc(x_29);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_29);
x_30 = x_39;
x_31 = x_37;
goto block_33;
}
else
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_28);
x_40 = lean_box(x_1);
lean_inc(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_29);
x_30 = x_41;
x_31 = x_1;
goto block_33;
}
block_33:
{
if (x_31 == 0)
{
lean_dec(x_29);
lean_dec(x_13);
return x_30;
}
else
{
lean_dec(x_30);
x_2 = x_13;
x_9 = x_29;
goto _start;
}
}
}
}
else
{
uint8_t x_42; 
lean_dec(x_13);
x_42 = !lean_is_exclusive(x_14);
if (x_42 == 0)
{
return x_14;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_14, 0);
x_44 = lean_ctor_get(x_14, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_14);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 5)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_9, 0);
lean_dec(x_13);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_15, 2);
lean_inc(x_16);
lean_dec(x_15);
x_17 = l_Lean_Expr_isProp(x_16);
lean_dec(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_18 = l_Lean_InductiveVal_numTypeFormers(x_14);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_dec_eq(x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_14);
x_21 = lean_box(x_20);
lean_ctor_set(x_9, 0, x_21);
return x_9;
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_14, 2);
lean_inc(x_22);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_nat_dec_eq(x_22, x_23);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_14);
x_25 = lean_box(x_24);
lean_ctor_set(x_9, 0, x_25);
return x_9;
}
else
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_ctor_get(x_14, 1);
lean_inc(x_26);
x_27 = lean_nat_dec_eq(x_26, x_23);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_14);
x_28 = lean_box(x_27);
lean_ctor_set(x_9, 0, x_28);
return x_9;
}
else
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_14, 4);
lean_inc(x_29);
x_30 = l_List_isEmpty___redArg(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
x_31 = lean_ctor_get_uint8(x_14, sizeof(void*)*6);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = lean_ctor_get_uint8(x_14, sizeof(void*)*6 + 1);
lean_dec(x_14);
if (x_32 == 0)
{
lean_object* x_33; 
lean_free_object(x_9);
x_33 = l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__2(x_32, x_29, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
return x_33;
}
else
{
lean_object* x_34; 
lean_dec(x_29);
x_34 = lean_box(x_31);
lean_ctor_set(x_9, 0, x_34);
return x_9;
}
}
else
{
lean_object* x_35; 
lean_dec(x_29);
lean_dec(x_14);
x_35 = lean_box(x_30);
lean_ctor_set(x_9, 0, x_35);
return x_9;
}
}
else
{
lean_object* x_36; 
lean_dec(x_29);
lean_dec(x_14);
x_36 = lean_box(x_17);
lean_ctor_set(x_9, 0, x_36);
return x_9;
}
}
}
}
}
else
{
lean_object* x_37; 
lean_dec(x_14);
x_37 = lean_box(0);
lean_ctor_set(x_9, 0, x_37);
return x_9;
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_38 = lean_ctor_get(x_9, 1);
lean_inc(x_38);
lean_dec(x_9);
x_39 = lean_ctor_get(x_10, 0);
lean_inc(x_39);
lean_dec(x_10);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_40, 2);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_Expr_isProp(x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = l_Lean_InductiveVal_numTypeFormers(x_39);
x_44 = lean_unsigned_to_nat(1u);
x_45 = lean_nat_dec_eq(x_43, x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_39);
x_46 = lean_box(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_38);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_ctor_get(x_39, 2);
lean_inc(x_48);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_nat_dec_eq(x_48, x_49);
lean_dec(x_48);
if (x_50 == 0)
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_39);
x_51 = lean_box(x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_38);
return x_52;
}
else
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_39, 1);
lean_inc(x_53);
x_54 = lean_nat_dec_eq(x_53, x_49);
lean_dec(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
lean_dec(x_39);
x_55 = lean_box(x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_38);
return x_56;
}
else
{
lean_object* x_57; uint8_t x_58; 
x_57 = lean_ctor_get(x_39, 4);
lean_inc(x_57);
x_58 = l_List_isEmpty___redArg(x_57);
if (x_58 == 0)
{
uint8_t x_59; 
x_59 = lean_ctor_get_uint8(x_39, sizeof(void*)*6);
if (x_59 == 0)
{
uint8_t x_60; 
x_60 = lean_ctor_get_uint8(x_39, sizeof(void*)*6 + 1);
lean_dec(x_39);
if (x_60 == 0)
{
lean_object* x_61; 
x_61 = l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__2(x_60, x_57, x_2, x_3, x_4, x_5, x_6, x_7, x_38);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; 
lean_dec(x_57);
x_62 = lean_box(x_59);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_38);
return x_63;
}
}
else
{
lean_object* x_64; lean_object* x_65; 
lean_dec(x_57);
lean_dec(x_39);
x_64 = lean_box(x_58);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_38);
return x_65;
}
}
else
{
lean_object* x_66; lean_object* x_67; 
lean_dec(x_57);
lean_dec(x_39);
x_66 = lean_box(x_42);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_66);
lean_ctor_set(x_67, 1, x_38);
return x_67;
}
}
}
}
}
else
{
lean_object* x_68; lean_object* x_69; 
lean_dec(x_39);
x_68 = lean_box(0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_38);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_10);
x_70 = !lean_is_exclusive(x_9);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_9, 0);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set(x_9, 0, x_72);
return x_9;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_9, 1);
lean_inc(x_73);
lean_dec(x_9);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
}
else
{
uint8_t x_76; 
x_76 = !lean_is_exclusive(x_9);
if (x_76 == 0)
{
return x_9;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_9, 0);
x_78 = lean_ctor_get(x_9, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_9);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; lean_object* x_16; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; uint8_t x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_102; uint8_t x_103; 
x_102 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_builtinTypes;
x_103 = l_Array_contains___at___Lean_registerInternalExceptionId_spec__0(x_102, x_1);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; uint8_t x_109; lean_object* x_472; uint8_t x_473; lean_object* x_505; lean_object* x_506; lean_object* x_507; uint64_t x_508; lean_object* x_509; uint64_t x_510; uint64_t x_511; uint64_t x_512; lean_object* x_513; uint64_t x_514; uint64_t x_515; uint64_t x_516; size_t x_517; size_t x_518; lean_object* x_519; size_t x_520; size_t x_521; size_t x_522; lean_object* x_523; uint8_t x_524; 
x_104 = lean_st_ref_get(x_3, x_8);
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_107 = x_104;
} else {
 lean_dec_ref(x_104);
 x_107 = lean_box(0);
}
x_472 = lean_ctor_get(x_105, 2);
lean_inc(x_472);
lean_dec(x_105);
x_505 = lean_ctor_get(x_472, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_505, 1);
lean_inc(x_506);
lean_dec(x_505);
x_507 = lean_array_get_size(x_506);
x_508 = l_Lean_Name_hash___override(x_1);
x_509 = lean_unsigned_to_nat(32u);
x_510 = lean_uint64_of_nat(x_509);
x_511 = lean_uint64_shift_right(x_508, x_510);
x_512 = lean_uint64_xor(x_508, x_511);
x_513 = lean_unsigned_to_nat(16u);
x_514 = lean_uint64_of_nat(x_513);
x_515 = lean_uint64_shift_right(x_512, x_514);
x_516 = lean_uint64_xor(x_512, x_515);
x_517 = lean_uint64_to_usize(x_516);
x_518 = lean_usize_of_nat(x_507);
lean_dec(x_507);
x_519 = lean_unsigned_to_nat(1u);
x_520 = lean_usize_of_nat(x_519);
x_521 = lean_usize_sub(x_518, x_520);
x_522 = lean_usize_land(x_517, x_521);
x_523 = lean_array_uget(x_506, x_522);
lean_dec(x_506);
x_524 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_523);
lean_dec(x_523);
if (x_524 == 0)
{
lean_object* x_525; lean_object* x_526; lean_object* x_527; size_t x_528; size_t x_529; size_t x_530; lean_object* x_531; uint8_t x_532; 
x_525 = lean_ctor_get(x_472, 1);
lean_inc(x_525);
x_526 = lean_ctor_get(x_525, 1);
lean_inc(x_526);
lean_dec(x_525);
x_527 = lean_array_get_size(x_526);
x_528 = lean_usize_of_nat(x_527);
lean_dec(x_527);
x_529 = lean_usize_sub(x_528, x_520);
x_530 = lean_usize_land(x_517, x_529);
x_531 = lean_array_uget(x_526, x_530);
lean_dec(x_526);
x_532 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_531);
lean_dec(x_531);
x_473 = x_532;
goto block_504;
}
else
{
x_473 = x_524;
goto block_504;
}
block_471:
{
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; uint8_t x_114; lean_object* x_115; 
lean_dec(x_107);
x_110 = lean_st_ref_get(x_7, x_106);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_110, 1);
lean_inc(x_112);
lean_dec(x_110);
x_113 = lean_ctor_get(x_111, 0);
lean_inc(x_113);
lean_dec(x_111);
lean_inc(x_1);
x_114 = l_Lean_isStructure(x_113, x_1);
x_115 = lean_box(1);
if (x_114 == 0)
{
lean_object* x_116; 
lean_inc(x_1);
x_116 = l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_112);
lean_dec(x_2);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; uint8_t x_118; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_unbox(x_117);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; 
x_119 = lean_ctor_get(x_116, 1);
lean_inc(x_119);
lean_dec(x_116);
lean_inc(x_1);
x_120 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_isSupportedMatch(x_1, x_4, x_5, x_6, x_7, x_119);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; 
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint64_t x_136; lean_object* x_137; uint64_t x_138; uint64_t x_139; uint64_t x_140; lean_object* x_141; uint64_t x_142; uint64_t x_143; uint64_t x_144; size_t x_145; size_t x_146; lean_object* x_147; size_t x_148; size_t x_149; size_t x_150; lean_object* x_151; uint8_t x_152; 
x_122 = lean_ctor_get(x_120, 1);
lean_inc(x_122);
lean_dec(x_120);
x_123 = lean_st_ref_take(x_3, x_122);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_124, 2);
lean_inc(x_125);
x_126 = lean_ctor_get(x_125, 3);
lean_inc(x_126);
x_127 = lean_ctor_get(x_123, 1);
lean_inc(x_127);
lean_dec(x_123);
x_128 = lean_ctor_get(x_126, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_124, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_124, 1);
lean_inc(x_131);
lean_dec(x_124);
x_132 = lean_ctor_get(x_125, 0);
lean_inc(x_132);
x_133 = lean_ctor_get(x_125, 1);
lean_inc(x_133);
x_134 = lean_ctor_get(x_125, 2);
lean_inc(x_134);
lean_dec(x_125);
x_135 = lean_array_get_size(x_129);
x_136 = l_Lean_Name_hash___override(x_1);
x_137 = lean_unsigned_to_nat(32u);
x_138 = lean_uint64_of_nat(x_137);
x_139 = lean_uint64_shift_right(x_136, x_138);
x_140 = lean_uint64_xor(x_136, x_139);
x_141 = lean_unsigned_to_nat(16u);
x_142 = lean_uint64_of_nat(x_141);
x_143 = lean_uint64_shift_right(x_140, x_142);
x_144 = lean_uint64_xor(x_140, x_143);
x_145 = lean_uint64_to_usize(x_144);
x_146 = lean_usize_of_nat(x_135);
lean_dec(x_135);
x_147 = lean_unsigned_to_nat(1u);
x_148 = lean_usize_of_nat(x_147);
x_149 = lean_usize_sub(x_146, x_148);
x_150 = lean_usize_land(x_145, x_149);
x_151 = lean_array_uget(x_129, x_150);
x_152 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_151);
if (x_152 == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_126);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_154 = lean_ctor_get(x_126, 1);
lean_dec(x_154);
x_155 = lean_ctor_get(x_126, 0);
lean_dec(x_155);
x_156 = lean_box(0);
x_157 = lean_nat_add(x_128, x_147);
lean_dec(x_128);
x_158 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_158, 0, x_1);
lean_ctor_set(x_158, 1, x_156);
lean_ctor_set(x_158, 2, x_151);
x_159 = lean_array_uset(x_129, x_150, x_158);
x_160 = lean_unsigned_to_nat(2u);
x_161 = lean_nat_shiftl(x_157, x_160);
x_162 = lean_unsigned_to_nat(3u);
x_163 = lean_nat_div(x_161, x_162);
lean_dec(x_161);
x_164 = lean_array_get_size(x_159);
x_165 = lean_nat_dec_le(x_163, x_164);
lean_dec(x_164);
lean_dec(x_163);
if (x_165 == 0)
{
lean_object* x_166; uint8_t x_167; 
x_166 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_159);
lean_ctor_set(x_126, 1, x_166);
lean_ctor_set(x_126, 0, x_157);
x_167 = lean_unbox(x_117);
lean_dec(x_117);
x_9 = x_134;
x_10 = x_131;
x_11 = x_127;
x_12 = x_132;
x_13 = x_130;
x_14 = x_167;
x_15 = x_133;
x_16 = x_126;
goto block_26;
}
else
{
uint8_t x_168; 
lean_ctor_set(x_126, 1, x_159);
lean_ctor_set(x_126, 0, x_157);
x_168 = lean_unbox(x_117);
lean_dec(x_117);
x_9 = x_134;
x_10 = x_131;
x_11 = x_127;
x_12 = x_132;
x_13 = x_130;
x_14 = x_168;
x_15 = x_133;
x_16 = x_126;
goto block_26;
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_dec(x_126);
x_169 = lean_box(0);
x_170 = lean_nat_add(x_128, x_147);
lean_dec(x_128);
x_171 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_171, 0, x_1);
lean_ctor_set(x_171, 1, x_169);
lean_ctor_set(x_171, 2, x_151);
x_172 = lean_array_uset(x_129, x_150, x_171);
x_173 = lean_unsigned_to_nat(2u);
x_174 = lean_nat_shiftl(x_170, x_173);
x_175 = lean_unsigned_to_nat(3u);
x_176 = lean_nat_div(x_174, x_175);
lean_dec(x_174);
x_177 = lean_array_get_size(x_172);
x_178 = lean_nat_dec_le(x_176, x_177);
lean_dec(x_177);
lean_dec(x_176);
if (x_178 == 0)
{
lean_object* x_179; lean_object* x_180; uint8_t x_181; 
x_179 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_172);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_170);
lean_ctor_set(x_180, 1, x_179);
x_181 = lean_unbox(x_117);
lean_dec(x_117);
x_9 = x_134;
x_10 = x_131;
x_11 = x_127;
x_12 = x_132;
x_13 = x_130;
x_14 = x_181;
x_15 = x_133;
x_16 = x_180;
goto block_26;
}
else
{
lean_object* x_182; uint8_t x_183; 
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_170);
lean_ctor_set(x_182, 1, x_172);
x_183 = lean_unbox(x_117);
lean_dec(x_117);
x_9 = x_134;
x_10 = x_131;
x_11 = x_127;
x_12 = x_132;
x_13 = x_130;
x_14 = x_183;
x_15 = x_133;
x_16 = x_182;
goto block_26;
}
}
}
else
{
uint8_t x_184; 
lean_dec(x_151);
lean_dec(x_129);
lean_dec(x_128);
lean_dec(x_1);
x_184 = lean_unbox(x_117);
lean_dec(x_117);
x_9 = x_134;
x_10 = x_131;
x_11 = x_127;
x_12 = x_132;
x_13 = x_130;
x_14 = x_184;
x_15 = x_133;
x_16 = x_126;
goto block_26;
}
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_185 = lean_ctor_get(x_120, 1);
lean_inc(x_185);
lean_dec(x_120);
x_186 = lean_ctor_get(x_121, 0);
lean_inc(x_186);
lean_dec(x_121);
x_187 = lean_st_ref_take(x_3, x_185);
x_188 = lean_ctor_get(x_187, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_188, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 2);
lean_inc(x_190);
x_191 = lean_ctor_get(x_187, 1);
lean_inc(x_191);
lean_dec(x_187);
x_192 = !lean_is_exclusive(x_190);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; uint64_t x_202; uint64_t x_203; uint64_t x_204; lean_object* x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; size_t x_209; size_t x_210; lean_object* x_211; size_t x_212; size_t x_213; size_t x_214; lean_object* x_215; uint8_t x_216; 
x_193 = lean_ctor_get(x_190, 0);
x_194 = lean_ctor_get(x_190, 1);
x_195 = lean_ctor_get(x_188, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_188, 1);
lean_inc(x_196);
lean_dec(x_188);
x_197 = lean_ctor_get(x_189, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_189, 1);
lean_inc(x_198);
x_199 = lean_array_get_size(x_194);
x_200 = l_Lean_Name_hash___override(x_1);
x_201 = lean_unsigned_to_nat(32u);
x_202 = lean_uint64_of_nat(x_201);
x_203 = lean_uint64_shift_right(x_200, x_202);
x_204 = lean_uint64_xor(x_200, x_203);
x_205 = lean_unsigned_to_nat(16u);
x_206 = lean_uint64_of_nat(x_205);
x_207 = lean_uint64_shift_right(x_204, x_206);
x_208 = lean_uint64_xor(x_204, x_207);
x_209 = lean_uint64_to_usize(x_208);
x_210 = lean_usize_of_nat(x_199);
lean_dec(x_199);
x_211 = lean_unsigned_to_nat(1u);
x_212 = lean_usize_of_nat(x_211);
x_213 = lean_usize_sub(x_210, x_212);
x_214 = lean_usize_land(x_209, x_213);
x_215 = lean_array_uget(x_194, x_214);
x_216 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_217 = lean_nat_add(x_193, x_211);
lean_dec(x_193);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_1);
lean_ctor_set(x_218, 1, x_186);
lean_ctor_set(x_218, 2, x_215);
x_219 = lean_array_uset(x_194, x_214, x_218);
x_220 = lean_unsigned_to_nat(2u);
x_221 = lean_nat_shiftl(x_217, x_220);
x_222 = lean_unsigned_to_nat(3u);
x_223 = lean_nat_div(x_221, x_222);
lean_dec(x_221);
x_224 = lean_array_get_size(x_219);
x_225 = lean_nat_dec_le(x_223, x_224);
lean_dec(x_224);
lean_dec(x_223);
if (x_225 == 0)
{
lean_object* x_226; uint8_t x_227; 
x_226 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_219);
lean_ctor_set(x_190, 1, x_226);
lean_ctor_set(x_190, 0, x_217);
x_227 = lean_unbox(x_117);
lean_dec(x_117);
x_27 = x_198;
x_28 = x_196;
x_29 = x_197;
x_30 = x_191;
x_31 = x_195;
x_32 = x_227;
x_33 = x_189;
x_34 = x_190;
goto block_45;
}
else
{
uint8_t x_228; 
lean_ctor_set(x_190, 1, x_219);
lean_ctor_set(x_190, 0, x_217);
x_228 = lean_unbox(x_117);
lean_dec(x_117);
x_27 = x_198;
x_28 = x_196;
x_29 = x_197;
x_30 = x_191;
x_31 = x_195;
x_32 = x_228;
x_33 = x_189;
x_34 = x_190;
goto block_45;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; uint8_t x_233; 
x_229 = lean_box(0);
x_230 = lean_array_uset(x_194, x_214, x_229);
x_231 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_186, x_215);
x_232 = lean_array_uset(x_230, x_214, x_231);
lean_ctor_set(x_190, 1, x_232);
x_233 = lean_unbox(x_117);
lean_dec(x_117);
x_27 = x_198;
x_28 = x_196;
x_29 = x_197;
x_30 = x_191;
x_31 = x_195;
x_32 = x_233;
x_33 = x_189;
x_34 = x_190;
goto block_45;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; uint64_t x_241; lean_object* x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; lean_object* x_246; uint64_t x_247; uint64_t x_248; uint64_t x_249; size_t x_250; size_t x_251; lean_object* x_252; size_t x_253; size_t x_254; size_t x_255; lean_object* x_256; uint8_t x_257; 
x_234 = lean_ctor_get(x_190, 0);
x_235 = lean_ctor_get(x_190, 1);
lean_inc(x_235);
lean_inc(x_234);
lean_dec(x_190);
x_236 = lean_ctor_get(x_188, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_188, 1);
lean_inc(x_237);
lean_dec(x_188);
x_238 = lean_ctor_get(x_189, 0);
lean_inc(x_238);
x_239 = lean_ctor_get(x_189, 1);
lean_inc(x_239);
x_240 = lean_array_get_size(x_235);
x_241 = l_Lean_Name_hash___override(x_1);
x_242 = lean_unsigned_to_nat(32u);
x_243 = lean_uint64_of_nat(x_242);
x_244 = lean_uint64_shift_right(x_241, x_243);
x_245 = lean_uint64_xor(x_241, x_244);
x_246 = lean_unsigned_to_nat(16u);
x_247 = lean_uint64_of_nat(x_246);
x_248 = lean_uint64_shift_right(x_245, x_247);
x_249 = lean_uint64_xor(x_245, x_248);
x_250 = lean_uint64_to_usize(x_249);
x_251 = lean_usize_of_nat(x_240);
lean_dec(x_240);
x_252 = lean_unsigned_to_nat(1u);
x_253 = lean_usize_of_nat(x_252);
x_254 = lean_usize_sub(x_251, x_253);
x_255 = lean_usize_land(x_250, x_254);
x_256 = lean_array_uget(x_235, x_255);
x_257 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_256);
if (x_257 == 0)
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; uint8_t x_266; 
x_258 = lean_nat_add(x_234, x_252);
lean_dec(x_234);
x_259 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_259, 0, x_1);
lean_ctor_set(x_259, 1, x_186);
lean_ctor_set(x_259, 2, x_256);
x_260 = lean_array_uset(x_235, x_255, x_259);
x_261 = lean_unsigned_to_nat(2u);
x_262 = lean_nat_shiftl(x_258, x_261);
x_263 = lean_unsigned_to_nat(3u);
x_264 = lean_nat_div(x_262, x_263);
lean_dec(x_262);
x_265 = lean_array_get_size(x_260);
x_266 = lean_nat_dec_le(x_264, x_265);
lean_dec(x_265);
lean_dec(x_264);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; uint8_t x_269; 
x_267 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_260);
x_268 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_268, 0, x_258);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_unbox(x_117);
lean_dec(x_117);
x_27 = x_239;
x_28 = x_237;
x_29 = x_238;
x_30 = x_191;
x_31 = x_236;
x_32 = x_269;
x_33 = x_189;
x_34 = x_268;
goto block_45;
}
else
{
lean_object* x_270; uint8_t x_271; 
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_258);
lean_ctor_set(x_270, 1, x_260);
x_271 = lean_unbox(x_117);
lean_dec(x_117);
x_27 = x_239;
x_28 = x_237;
x_29 = x_238;
x_30 = x_191;
x_31 = x_236;
x_32 = x_271;
x_33 = x_189;
x_34 = x_270;
goto block_45;
}
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; uint8_t x_277; 
x_272 = lean_box(0);
x_273 = lean_array_uset(x_235, x_255, x_272);
x_274 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_186, x_256);
x_275 = lean_array_uset(x_273, x_255, x_274);
x_276 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_276, 0, x_234);
lean_ctor_set(x_276, 1, x_275);
x_277 = lean_unbox(x_117);
lean_dec(x_117);
x_27 = x_239;
x_28 = x_237;
x_29 = x_238;
x_30 = x_191;
x_31 = x_236;
x_32 = x_277;
x_33 = x_189;
x_34 = x_276;
goto block_45;
}
}
}
}
else
{
uint8_t x_278; 
lean_dec(x_117);
lean_dec(x_3);
lean_dec(x_1);
x_278 = !lean_is_exclusive(x_120);
if (x_278 == 0)
{
return x_120;
}
else
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_120, 0);
x_280 = lean_ctor_get(x_120, 1);
lean_inc(x_280);
lean_inc(x_279);
lean_dec(x_120);
x_281 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_281, 0, x_279);
lean_ctor_set(x_281, 1, x_280);
return x_281;
}
}
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; uint64_t x_294; lean_object* x_295; uint64_t x_296; uint64_t x_297; uint64_t x_298; lean_object* x_299; uint64_t x_300; uint64_t x_301; uint64_t x_302; size_t x_303; size_t x_304; lean_object* x_305; size_t x_306; size_t x_307; size_t x_308; lean_object* x_309; uint8_t x_310; 
lean_dec(x_117);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_282 = lean_ctor_get(x_116, 1);
lean_inc(x_282);
lean_dec(x_116);
x_283 = lean_st_ref_take(x_3, x_282);
x_284 = lean_ctor_get(x_283, 0);
lean_inc(x_284);
x_285 = lean_ctor_get(x_284, 2);
lean_inc(x_285);
x_286 = lean_ctor_get(x_285, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_283, 1);
lean_inc(x_287);
lean_dec(x_283);
x_288 = lean_ctor_get(x_286, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 1);
lean_inc(x_289);
x_290 = lean_ctor_get(x_284, 0);
lean_inc(x_290);
x_291 = lean_ctor_get(x_284, 1);
lean_inc(x_291);
lean_dec(x_284);
x_292 = lean_ctor_get(x_285, 0);
lean_inc(x_292);
x_293 = lean_array_get_size(x_289);
x_294 = l_Lean_Name_hash___override(x_1);
x_295 = lean_unsigned_to_nat(32u);
x_296 = lean_uint64_of_nat(x_295);
x_297 = lean_uint64_shift_right(x_294, x_296);
x_298 = lean_uint64_xor(x_294, x_297);
x_299 = lean_unsigned_to_nat(16u);
x_300 = lean_uint64_of_nat(x_299);
x_301 = lean_uint64_shift_right(x_298, x_300);
x_302 = lean_uint64_xor(x_298, x_301);
x_303 = lean_uint64_to_usize(x_302);
x_304 = lean_usize_of_nat(x_293);
lean_dec(x_293);
x_305 = lean_unsigned_to_nat(1u);
x_306 = lean_usize_of_nat(x_305);
x_307 = lean_usize_sub(x_304, x_306);
x_308 = lean_usize_land(x_303, x_307);
x_309 = lean_array_uget(x_289, x_308);
x_310 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_309);
if (x_310 == 0)
{
uint8_t x_311; 
x_311 = !lean_is_exclusive(x_286);
if (x_311 == 0)
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
x_312 = lean_ctor_get(x_286, 1);
lean_dec(x_312);
x_313 = lean_ctor_get(x_286, 0);
lean_dec(x_313);
x_314 = lean_box(0);
x_315 = lean_nat_add(x_288, x_305);
lean_dec(x_288);
x_316 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_316, 0, x_1);
lean_ctor_set(x_316, 1, x_314);
lean_ctor_set(x_316, 2, x_309);
x_317 = lean_array_uset(x_289, x_308, x_316);
x_318 = lean_unsigned_to_nat(2u);
x_319 = lean_nat_shiftl(x_315, x_318);
x_320 = lean_unsigned_to_nat(3u);
x_321 = lean_nat_div(x_319, x_320);
lean_dec(x_319);
x_322 = lean_array_get_size(x_317);
x_323 = lean_nat_dec_le(x_321, x_322);
lean_dec(x_322);
lean_dec(x_321);
if (x_323 == 0)
{
lean_object* x_324; uint8_t x_325; 
x_324 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_317);
lean_ctor_set(x_286, 1, x_324);
lean_ctor_set(x_286, 0, x_315);
x_325 = lean_unbox(x_115);
x_46 = x_325;
x_47 = x_292;
x_48 = x_285;
x_49 = x_287;
x_50 = x_291;
x_51 = x_290;
x_52 = x_286;
goto block_64;
}
else
{
uint8_t x_326; 
lean_ctor_set(x_286, 1, x_317);
lean_ctor_set(x_286, 0, x_315);
x_326 = lean_unbox(x_115);
x_46 = x_326;
x_47 = x_292;
x_48 = x_285;
x_49 = x_287;
x_50 = x_291;
x_51 = x_290;
x_52 = x_286;
goto block_64;
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; 
lean_dec(x_286);
x_327 = lean_box(0);
x_328 = lean_nat_add(x_288, x_305);
lean_dec(x_288);
x_329 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_329, 0, x_1);
lean_ctor_set(x_329, 1, x_327);
lean_ctor_set(x_329, 2, x_309);
x_330 = lean_array_uset(x_289, x_308, x_329);
x_331 = lean_unsigned_to_nat(2u);
x_332 = lean_nat_shiftl(x_328, x_331);
x_333 = lean_unsigned_to_nat(3u);
x_334 = lean_nat_div(x_332, x_333);
lean_dec(x_332);
x_335 = lean_array_get_size(x_330);
x_336 = lean_nat_dec_le(x_334, x_335);
lean_dec(x_335);
lean_dec(x_334);
if (x_336 == 0)
{
lean_object* x_337; lean_object* x_338; uint8_t x_339; 
x_337 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_330);
x_338 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_338, 0, x_328);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_unbox(x_115);
x_46 = x_339;
x_47 = x_292;
x_48 = x_285;
x_49 = x_287;
x_50 = x_291;
x_51 = x_290;
x_52 = x_338;
goto block_64;
}
else
{
lean_object* x_340; uint8_t x_341; 
x_340 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_340, 0, x_328);
lean_ctor_set(x_340, 1, x_330);
x_341 = lean_unbox(x_115);
x_46 = x_341;
x_47 = x_292;
x_48 = x_285;
x_49 = x_287;
x_50 = x_291;
x_51 = x_290;
x_52 = x_340;
goto block_64;
}
}
}
else
{
uint8_t x_342; 
lean_dec(x_309);
lean_dec(x_289);
lean_dec(x_288);
lean_dec(x_1);
x_342 = lean_unbox(x_115);
x_46 = x_342;
x_47 = x_292;
x_48 = x_285;
x_49 = x_287;
x_50 = x_291;
x_51 = x_290;
x_52 = x_286;
goto block_64;
}
}
}
else
{
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_116;
}
}
else
{
lean_object* x_343; 
lean_inc(x_3);
lean_inc(x_1);
x_343 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_112);
if (lean_obj_tag(x_343) == 0)
{
lean_object* x_344; uint8_t x_345; 
x_344 = lean_ctor_get(x_343, 0);
lean_inc(x_344);
x_345 = lean_unbox(x_344);
if (x_345 == 0)
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; uint64_t x_360; lean_object* x_361; uint64_t x_362; uint64_t x_363; uint64_t x_364; lean_object* x_365; uint64_t x_366; uint64_t x_367; uint64_t x_368; size_t x_369; size_t x_370; lean_object* x_371; size_t x_372; size_t x_373; size_t x_374; lean_object* x_375; uint8_t x_376; 
x_346 = lean_ctor_get(x_343, 1);
lean_inc(x_346);
lean_dec(x_343);
x_347 = lean_st_ref_take(x_3, x_346);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_348, 2);
lean_inc(x_349);
x_350 = lean_ctor_get(x_349, 3);
lean_inc(x_350);
x_351 = lean_ctor_get(x_347, 1);
lean_inc(x_351);
lean_dec(x_347);
x_352 = lean_ctor_get(x_350, 0);
lean_inc(x_352);
x_353 = lean_ctor_get(x_350, 1);
lean_inc(x_353);
x_354 = lean_ctor_get(x_348, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_348, 1);
lean_inc(x_355);
lean_dec(x_348);
x_356 = lean_ctor_get(x_349, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_349, 1);
lean_inc(x_357);
x_358 = lean_ctor_get(x_349, 2);
lean_inc(x_358);
lean_dec(x_349);
x_359 = lean_array_get_size(x_353);
x_360 = l_Lean_Name_hash___override(x_1);
x_361 = lean_unsigned_to_nat(32u);
x_362 = lean_uint64_of_nat(x_361);
x_363 = lean_uint64_shift_right(x_360, x_362);
x_364 = lean_uint64_xor(x_360, x_363);
x_365 = lean_unsigned_to_nat(16u);
x_366 = lean_uint64_of_nat(x_365);
x_367 = lean_uint64_shift_right(x_364, x_366);
x_368 = lean_uint64_xor(x_364, x_367);
x_369 = lean_uint64_to_usize(x_368);
x_370 = lean_usize_of_nat(x_359);
lean_dec(x_359);
x_371 = lean_unsigned_to_nat(1u);
x_372 = lean_usize_of_nat(x_371);
x_373 = lean_usize_sub(x_370, x_372);
x_374 = lean_usize_land(x_369, x_373);
x_375 = lean_array_uget(x_353, x_374);
x_376 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_375);
if (x_376 == 0)
{
uint8_t x_377; 
x_377 = !lean_is_exclusive(x_350);
if (x_377 == 0)
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; uint8_t x_389; 
x_378 = lean_ctor_get(x_350, 1);
lean_dec(x_378);
x_379 = lean_ctor_get(x_350, 0);
lean_dec(x_379);
x_380 = lean_box(0);
x_381 = lean_nat_add(x_352, x_371);
lean_dec(x_352);
x_382 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_382, 0, x_1);
lean_ctor_set(x_382, 1, x_380);
lean_ctor_set(x_382, 2, x_375);
x_383 = lean_array_uset(x_353, x_374, x_382);
x_384 = lean_unsigned_to_nat(2u);
x_385 = lean_nat_shiftl(x_381, x_384);
x_386 = lean_unsigned_to_nat(3u);
x_387 = lean_nat_div(x_385, x_386);
lean_dec(x_385);
x_388 = lean_array_get_size(x_383);
x_389 = lean_nat_dec_le(x_387, x_388);
lean_dec(x_388);
lean_dec(x_387);
if (x_389 == 0)
{
lean_object* x_390; uint8_t x_391; 
x_390 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_383);
lean_ctor_set(x_350, 1, x_390);
lean_ctor_set(x_350, 0, x_381);
x_391 = lean_unbox(x_344);
lean_dec(x_344);
x_65 = x_391;
x_66 = x_354;
x_67 = x_356;
x_68 = x_357;
x_69 = x_355;
x_70 = x_351;
x_71 = x_358;
x_72 = x_350;
goto block_82;
}
else
{
uint8_t x_392; 
lean_ctor_set(x_350, 1, x_383);
lean_ctor_set(x_350, 0, x_381);
x_392 = lean_unbox(x_344);
lean_dec(x_344);
x_65 = x_392;
x_66 = x_354;
x_67 = x_356;
x_68 = x_357;
x_69 = x_355;
x_70 = x_351;
x_71 = x_358;
x_72 = x_350;
goto block_82;
}
}
else
{
lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; uint8_t x_402; 
lean_dec(x_350);
x_393 = lean_box(0);
x_394 = lean_nat_add(x_352, x_371);
lean_dec(x_352);
x_395 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_395, 0, x_1);
lean_ctor_set(x_395, 1, x_393);
lean_ctor_set(x_395, 2, x_375);
x_396 = lean_array_uset(x_353, x_374, x_395);
x_397 = lean_unsigned_to_nat(2u);
x_398 = lean_nat_shiftl(x_394, x_397);
x_399 = lean_unsigned_to_nat(3u);
x_400 = lean_nat_div(x_398, x_399);
lean_dec(x_398);
x_401 = lean_array_get_size(x_396);
x_402 = lean_nat_dec_le(x_400, x_401);
lean_dec(x_401);
lean_dec(x_400);
if (x_402 == 0)
{
lean_object* x_403; lean_object* x_404; uint8_t x_405; 
x_403 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_396);
x_404 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_404, 0, x_394);
lean_ctor_set(x_404, 1, x_403);
x_405 = lean_unbox(x_344);
lean_dec(x_344);
x_65 = x_405;
x_66 = x_354;
x_67 = x_356;
x_68 = x_357;
x_69 = x_355;
x_70 = x_351;
x_71 = x_358;
x_72 = x_404;
goto block_82;
}
else
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_406, 0, x_394);
lean_ctor_set(x_406, 1, x_396);
x_407 = lean_unbox(x_344);
lean_dec(x_344);
x_65 = x_407;
x_66 = x_354;
x_67 = x_356;
x_68 = x_357;
x_69 = x_355;
x_70 = x_351;
x_71 = x_358;
x_72 = x_406;
goto block_82;
}
}
}
else
{
uint8_t x_408; 
lean_dec(x_375);
lean_dec(x_353);
lean_dec(x_352);
lean_dec(x_1);
x_408 = lean_unbox(x_344);
lean_dec(x_344);
x_65 = x_408;
x_66 = x_354;
x_67 = x_356;
x_68 = x_357;
x_69 = x_355;
x_70 = x_351;
x_71 = x_358;
x_72 = x_350;
goto block_82;
}
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; uint64_t x_420; lean_object* x_421; uint64_t x_422; uint64_t x_423; uint64_t x_424; lean_object* x_425; uint64_t x_426; uint64_t x_427; uint64_t x_428; size_t x_429; size_t x_430; lean_object* x_431; size_t x_432; size_t x_433; size_t x_434; lean_object* x_435; uint8_t x_436; 
lean_dec(x_344);
x_409 = lean_ctor_get(x_343, 1);
lean_inc(x_409);
lean_dec(x_343);
x_410 = lean_st_ref_take(x_3, x_409);
x_411 = lean_ctor_get(x_410, 0);
lean_inc(x_411);
x_412 = lean_ctor_get(x_411, 2);
lean_inc(x_412);
x_413 = lean_ctor_get(x_412, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_410, 1);
lean_inc(x_414);
lean_dec(x_410);
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
x_416 = lean_ctor_get(x_413, 1);
lean_inc(x_416);
x_417 = lean_ctor_get(x_411, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_411, 1);
lean_inc(x_418);
lean_dec(x_411);
x_419 = lean_array_get_size(x_416);
x_420 = l_Lean_Name_hash___override(x_1);
x_421 = lean_unsigned_to_nat(32u);
x_422 = lean_uint64_of_nat(x_421);
x_423 = lean_uint64_shift_right(x_420, x_422);
x_424 = lean_uint64_xor(x_420, x_423);
x_425 = lean_unsigned_to_nat(16u);
x_426 = lean_uint64_of_nat(x_425);
x_427 = lean_uint64_shift_right(x_424, x_426);
x_428 = lean_uint64_xor(x_424, x_427);
x_429 = lean_uint64_to_usize(x_428);
x_430 = lean_usize_of_nat(x_419);
lean_dec(x_419);
x_431 = lean_unsigned_to_nat(1u);
x_432 = lean_usize_of_nat(x_431);
x_433 = lean_usize_sub(x_430, x_432);
x_434 = lean_usize_land(x_429, x_433);
x_435 = lean_array_uget(x_416, x_434);
x_436 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_435);
if (x_436 == 0)
{
uint8_t x_437; 
x_437 = !lean_is_exclusive(x_413);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; uint8_t x_449; 
x_438 = lean_ctor_get(x_413, 1);
lean_dec(x_438);
x_439 = lean_ctor_get(x_413, 0);
lean_dec(x_439);
x_440 = lean_box(0);
x_441 = lean_nat_add(x_415, x_431);
lean_dec(x_415);
x_442 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_442, 0, x_1);
lean_ctor_set(x_442, 1, x_440);
lean_ctor_set(x_442, 2, x_435);
x_443 = lean_array_uset(x_416, x_434, x_442);
x_444 = lean_unsigned_to_nat(2u);
x_445 = lean_nat_shiftl(x_441, x_444);
x_446 = lean_unsigned_to_nat(3u);
x_447 = lean_nat_div(x_445, x_446);
lean_dec(x_445);
x_448 = lean_array_get_size(x_443);
x_449 = lean_nat_dec_le(x_447, x_448);
lean_dec(x_448);
lean_dec(x_447);
if (x_449 == 0)
{
lean_object* x_450; uint8_t x_451; 
x_450 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_443);
lean_ctor_set(x_413, 1, x_450);
lean_ctor_set(x_413, 0, x_441);
x_451 = lean_unbox(x_115);
x_83 = x_451;
x_84 = x_412;
x_85 = x_418;
x_86 = x_414;
x_87 = x_417;
x_88 = x_413;
goto block_101;
}
else
{
uint8_t x_452; 
lean_ctor_set(x_413, 1, x_443);
lean_ctor_set(x_413, 0, x_441);
x_452 = lean_unbox(x_115);
x_83 = x_452;
x_84 = x_412;
x_85 = x_418;
x_86 = x_414;
x_87 = x_417;
x_88 = x_413;
goto block_101;
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; uint8_t x_462; 
lean_dec(x_413);
x_453 = lean_box(0);
x_454 = lean_nat_add(x_415, x_431);
lean_dec(x_415);
x_455 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_455, 0, x_1);
lean_ctor_set(x_455, 1, x_453);
lean_ctor_set(x_455, 2, x_435);
x_456 = lean_array_uset(x_416, x_434, x_455);
x_457 = lean_unsigned_to_nat(2u);
x_458 = lean_nat_shiftl(x_454, x_457);
x_459 = lean_unsigned_to_nat(3u);
x_460 = lean_nat_div(x_458, x_459);
lean_dec(x_458);
x_461 = lean_array_get_size(x_456);
x_462 = lean_nat_dec_le(x_460, x_461);
lean_dec(x_461);
lean_dec(x_460);
if (x_462 == 0)
{
lean_object* x_463; lean_object* x_464; uint8_t x_465; 
x_463 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_456);
x_464 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_464, 0, x_454);
lean_ctor_set(x_464, 1, x_463);
x_465 = lean_unbox(x_115);
x_83 = x_465;
x_84 = x_412;
x_85 = x_418;
x_86 = x_414;
x_87 = x_417;
x_88 = x_464;
goto block_101;
}
else
{
lean_object* x_466; uint8_t x_467; 
x_466 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_466, 0, x_454);
lean_ctor_set(x_466, 1, x_456);
x_467 = lean_unbox(x_115);
x_83 = x_467;
x_84 = x_412;
x_85 = x_418;
x_86 = x_414;
x_87 = x_417;
x_88 = x_466;
goto block_101;
}
}
}
else
{
uint8_t x_468; 
lean_dec(x_435);
lean_dec(x_416);
lean_dec(x_415);
lean_dec(x_1);
x_468 = lean_unbox(x_115);
x_83 = x_468;
x_84 = x_412;
x_85 = x_418;
x_86 = x_414;
x_87 = x_417;
x_88 = x_413;
goto block_101;
}
}
}
else
{
lean_dec(x_3);
lean_dec(x_1);
return x_343;
}
}
}
else
{
lean_object* x_469; lean_object* x_470; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_469 = lean_box(x_108);
if (lean_is_scalar(x_107)) {
 x_470 = lean_alloc_ctor(0, 2, 0);
} else {
 x_470 = x_107;
}
lean_ctor_set(x_470, 0, x_469);
lean_ctor_set(x_470, 1, x_106);
return x_470;
}
}
block_504:
{
if (x_473 == 0)
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint64_t x_477; lean_object* x_478; uint64_t x_479; uint64_t x_480; uint64_t x_481; lean_object* x_482; uint64_t x_483; uint64_t x_484; uint64_t x_485; size_t x_486; size_t x_487; lean_object* x_488; size_t x_489; size_t x_490; size_t x_491; lean_object* x_492; uint8_t x_493; 
x_474 = lean_ctor_get(x_472, 3);
lean_inc(x_474);
x_475 = lean_ctor_get(x_474, 1);
lean_inc(x_475);
lean_dec(x_474);
x_476 = lean_array_get_size(x_475);
x_477 = l_Lean_Name_hash___override(x_1);
x_478 = lean_unsigned_to_nat(32u);
x_479 = lean_uint64_of_nat(x_478);
x_480 = lean_uint64_shift_right(x_477, x_479);
x_481 = lean_uint64_xor(x_477, x_480);
x_482 = lean_unsigned_to_nat(16u);
x_483 = lean_uint64_of_nat(x_482);
x_484 = lean_uint64_shift_right(x_481, x_483);
x_485 = lean_uint64_xor(x_481, x_484);
x_486 = lean_uint64_to_usize(x_485);
x_487 = lean_usize_of_nat(x_476);
lean_dec(x_476);
x_488 = lean_unsigned_to_nat(1u);
x_489 = lean_usize_of_nat(x_488);
x_490 = lean_usize_sub(x_487, x_489);
x_491 = lean_usize_land(x_486, x_490);
x_492 = lean_array_uget(x_475, x_491);
lean_dec(x_475);
x_493 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_492);
lean_dec(x_492);
if (x_493 == 0)
{
lean_object* x_494; lean_object* x_495; lean_object* x_496; size_t x_497; size_t x_498; size_t x_499; lean_object* x_500; uint8_t x_501; 
x_494 = lean_ctor_get(x_472, 2);
lean_inc(x_494);
lean_dec(x_472);
x_495 = lean_ctor_get(x_494, 1);
lean_inc(x_495);
lean_dec(x_494);
x_496 = lean_array_get_size(x_495);
x_497 = lean_usize_of_nat(x_496);
lean_dec(x_496);
x_498 = lean_usize_sub(x_497, x_489);
x_499 = lean_usize_land(x_486, x_498);
x_500 = lean_array_uget(x_495, x_499);
lean_dec(x_495);
x_501 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_500);
lean_dec(x_500);
x_108 = x_473;
x_109 = x_501;
goto block_471;
}
else
{
lean_dec(x_472);
x_108 = x_473;
x_109 = x_493;
goto block_471;
}
}
else
{
lean_object* x_502; lean_object* x_503; 
lean_dec(x_472);
lean_dec(x_107);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_502 = lean_box(x_473);
x_503 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_106);
return x_503;
}
}
}
else
{
lean_object* x_533; lean_object* x_534; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_533 = lean_box(x_103);
x_534 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_534, 0, x_533);
lean_ctor_set(x_534, 1, x_8);
return x_534;
}
block_26:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_9);
lean_ctor_set(x_17, 3, x_16);
x_18 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_18, 0, x_13);
lean_ctor_set(x_18, 1, x_10);
lean_ctor_set(x_18, 2, x_17);
x_19 = lean_st_ref_set(x_3, x_18, x_11);
lean_dec(x_3);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
x_22 = lean_box(x_14);
lean_ctor_set(x_19, 0, x_22);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_box(x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
block_45:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_33, 3);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_36, 0, x_29);
lean_ctor_set(x_36, 1, x_27);
lean_ctor_set(x_36, 2, x_34);
lean_ctor_set(x_36, 3, x_35);
x_37 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_37, 0, x_31);
lean_ctor_set(x_37, 1, x_28);
lean_ctor_set(x_37, 2, x_36);
x_38 = lean_st_ref_set(x_3, x_37, x_30);
lean_dec(x_3);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_38, 0);
lean_dec(x_40);
x_41 = lean_box(x_32);
lean_ctor_set(x_38, 0, x_41);
return x_38;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_38, 1);
lean_inc(x_42);
lean_dec(x_38);
x_43 = lean_box(x_32);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_42);
return x_44;
}
}
block_64:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_53 = lean_ctor_get(x_48, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 3);
lean_inc(x_54);
lean_dec(x_48);
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_47);
lean_ctor_set(x_55, 1, x_52);
lean_ctor_set(x_55, 2, x_53);
lean_ctor_set(x_55, 3, x_54);
x_56 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_56, 0, x_51);
lean_ctor_set(x_56, 1, x_50);
lean_ctor_set(x_56, 2, x_55);
x_57 = lean_st_ref_set(x_3, x_56, x_49);
lean_dec(x_3);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; 
x_59 = lean_ctor_get(x_57, 0);
lean_dec(x_59);
x_60 = lean_box(x_46);
lean_ctor_set(x_57, 0, x_60);
return x_57;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_57, 1);
lean_inc(x_61);
lean_dec(x_57);
x_62 = lean_box(x_46);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_61);
return x_63;
}
}
block_82:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_73 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_73, 0, x_67);
lean_ctor_set(x_73, 1, x_68);
lean_ctor_set(x_73, 2, x_71);
lean_ctor_set(x_73, 3, x_72);
x_74 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_74, 0, x_66);
lean_ctor_set(x_74, 1, x_69);
lean_ctor_set(x_74, 2, x_73);
x_75 = lean_st_ref_set(x_3, x_74, x_70);
lean_dec(x_3);
x_76 = !lean_is_exclusive(x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_ctor_get(x_75, 0);
lean_dec(x_77);
x_78 = lean_box(x_65);
lean_ctor_set(x_75, 0, x_78);
return x_75;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_dec(x_75);
x_80 = lean_box(x_65);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
block_101:
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_89 = lean_ctor_get(x_84, 1);
lean_inc(x_89);
x_90 = lean_ctor_get(x_84, 2);
lean_inc(x_90);
x_91 = lean_ctor_get(x_84, 3);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_91);
x_93 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_93, 0, x_87);
lean_ctor_set(x_93, 1, x_85);
lean_ctor_set(x_93, 2, x_92);
x_94 = lean_st_ref_set(x_3, x_93, x_86);
lean_dec(x_3);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
x_97 = lean_box(x_83);
lean_ctor_set(x_94, 0, x_97);
return x_94;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_94, 1);
lean_inc(x_98);
lean_dec(x_94);
x_99 = lean_box(x_83);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 5)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_MessageData_ofConstName(x_1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("' is not a inductive type", 25, 25);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(x_26, x_4, x_5, x_6, x_7, x_17);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__1(lean_object* x_1, size_t x_2, size_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; lean_object* x_19; uint8_t x_24; 
x_24 = lean_usize_dec_eq(x_2, x_3);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_array_uget(x_1, x_2);
x_26 = l_Lean_Expr_fvarId_x21(x_25);
lean_dec(x_25);
lean_inc(x_7);
x_27 = l_Lean_FVarId_getType___redArg(x_26, x_7, x_9, x_10, x_11);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_30 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_typeCasesRelevant(x_28, x_5, x_6, x_7, x_8, x_9, x_10, x_29);
if (lean_obj_tag(x_30) == 0)
{
if (x_4 == 0)
{
x_19 = x_30;
goto block_23;
}
else
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_12 = x_4;
x_13 = x_31;
goto block_18;
}
}
else
{
x_19 = x_30;
goto block_23;
}
}
else
{
uint8_t x_32; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_32 = !lean_is_exclusive(x_27);
if (x_32 == 0)
{
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_36 = lean_box(x_4);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_11);
return x_37;
}
block_18:
{
lean_object* x_14; size_t x_15; size_t x_16; 
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_12;
x_11 = x_13;
goto _start;
}
block_23:
{
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = lean_unbox(x_20);
lean_dec(x_20);
x_12 = x_22;
x_13 = x_21;
goto block_18;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
lean_inc(x_1);
x_9 = l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 6)
{
uint8_t x_11; 
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec(x_10);
lean_ctor_set(x_9, 0, x_13);
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 1);
lean_inc(x_14);
lean_dec(x_9);
x_15 = lean_ctor_get(x_10, 0);
lean_inc(x_15);
lean_dec(x_10);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_14);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_10);
x_17 = lean_ctor_get(x_9, 1);
lean_inc(x_17);
lean_dec(x_9);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_box(0);
x_21 = lean_unbox(x_20);
x_22 = l_Lean_MessageData_ofConstName(x_1, x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_19);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_mk_string_unchecked("' is not a constructor", 22, 22);
x_25 = l_Lean_stringToMessageData(x_24);
lean_dec(x_24);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_23);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(x_26, x_4, x_5, x_6, x_7, x_17);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
return x_9;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_9, 0);
x_30 = lean_ctor_get(x_9, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_9);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = lean_apply_9(x_1, x_4, x_5, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg___lam__0), 10, 3);
lean_closure_set(x_11, 0, x_2);
lean_closure_set(x_11, 1, x_4);
lean_closure_set(x_11, 2, x_5);
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_unbox(x_12);
x_15 = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux___redArg(x_14, x_13, x_1, x_11, x_3, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
return x_15;
}
else
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
return x_15;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_15);
x_19 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure___lam__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_array_get_size(x_2);
x_13 = lean_nat_dec_lt(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = lean_box(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_12, x_12);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_17 = lean_box(x_1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_10);
return x_18;
}
else
{
size_t x_19; size_t x_20; lean_object* x_21; 
x_19 = lean_usize_of_nat(x_11);
x_20 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_21 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__1(x_2, x_19, x_20, x_1, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoInduct___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*6);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_10, 4);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_List_head_x21(lean_box(0), x_13, x_14);
lean_dec(x_14);
x_16 = l_Lean_getConstInfoCtor___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__2(x_15, x_2, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(x_11);
x_20 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure___lam__0___boxed), 10, 1);
lean_closure_set(x_20, 0, x_19);
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_ctor_get(x_21, 2);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg(x_22, x_20, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_18);
return x_23;
}
else
{
uint8_t x_24; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_24 = !lean_is_exclusive(x_16);
if (x_24 == 0)
{
return x_16;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_16, 0);
x_26 = lean_ctor_get(x_16, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_16);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = !lean_is_exclusive(x_9);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_9, 0);
lean_dec(x_29);
x_30 = lean_box(0);
lean_ctor_set(x_9, 0, x_30);
return x_9;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_9, 1);
lean_inc(x_31);
lean_dec(x_9);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_9);
if (x_34 == 0)
{
return x_9;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_9, 0);
x_36 = lean_ctor_get(x_9, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_9);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_typeCasesRelevant(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_26; uint8_t x_27; 
lean_inc(x_1);
x_9 = l_Lean_Meta_instantiateMVarsIfMVarApp___redArg(x_1, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
if (lean_is_exclusive(x_9)) {
 lean_ctor_release(x_9, 0);
 lean_ctor_release(x_9, 1);
 x_12 = x_9;
} else {
 lean_dec_ref(x_9);
 x_12 = lean_box(0);
}
x_26 = l_Lean_Expr_cleanupAnnotations(x_10);
x_27 = l_Lean_Expr_isApp(x_26);
if (x_27 == 0)
{
lean_dec(x_26);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_25;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc(x_26);
x_28 = l_Lean_Expr_appFnCleanup___redArg(x_26);
x_29 = lean_mk_string_unchecked("BitVec", 6, 6);
x_30 = l_Lean_Name_mkStr1(x_29);
x_31 = l_Lean_Expr_isConstOf(x_28, x_30);
lean_dec(x_30);
lean_dec(x_28);
if (x_31 == 0)
{
lean_dec(x_26);
x_13 = x_2;
x_14 = x_3;
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_25;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_12);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_32 = lean_ctor_get(x_26, 1);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l_Lean_Meta_getNatValue_x3f(x_32, x_4, x_5, x_6, x_7, x_11);
lean_dec(x_4);
lean_dec(x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
uint8_t x_35; 
x_35 = !lean_is_exclusive(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_33, 0);
lean_dec(x_36);
x_37 = lean_box(0);
lean_ctor_set(x_33, 0, x_37);
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 1);
lean_inc(x_38);
lean_dec(x_33);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_38);
return x_40;
}
}
else
{
uint8_t x_41; 
lean_dec(x_34);
x_41 = !lean_is_exclusive(x_33);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; 
x_42 = lean_ctor_get(x_33, 0);
lean_dec(x_42);
x_43 = lean_box(x_31);
lean_ctor_set(x_33, 0, x_43);
return x_33;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_33, 1);
lean_inc(x_44);
lean_dec(x_33);
x_45 = lean_box(x_31);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
}
}
else
{
uint8_t x_47; 
x_47 = !lean_is_exclusive(x_33);
if (x_47 == 0)
{
return x_33;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_33, 0);
x_49 = lean_ctor_get(x_33, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_33);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
block_25:
{
lean_object* x_19; lean_object* x_20; 
x_19 = l_Lean_Expr_getAppFn(x_1);
lean_dec(x_1);
x_20 = l_Lean_Expr_constName_x3f(x_19);
lean_dec(x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_21 = lean_box(0);
if (lean_is_scalar(x_12)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_12;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_11);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_24 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst(x_23, x_13, x_14, x_15, x_16, x_17, x_18, x_11);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfo___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = l_List_allM___at___Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0_spec__2(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isEnumType___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoInduct___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoInduct___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__1(x_1, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfoCtor___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_getConstInfoCtor___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___redArg(x_1, x_2, x_11, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_forallTelescope___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure_spec__3(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeStructure___lam__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__0___boxed), 7, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_instMonadMetaM___lam__1), 9, 0);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_13 = l_instMonadEIO(lean_box(0));
x_14 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
lean_inc(x_16);
x_17 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_17, 0, x_16);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_18, 0, x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_22, 0, x_21);
x_23 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_24 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_24, 0, x_23);
x_25 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_26, 0, lean_box(0));
lean_closure_set(x_26, 1, lean_box(0));
x_27 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_28, 0, x_27);
lean_inc(x_28);
lean_inc(x_25);
lean_inc(x_22);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_19);
lean_ctor_set(x_29, 1, x_11);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_25);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_12);
x_31 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
lean_dec(x_32);
lean_inc(x_33);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_35, 0, x_33);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_37, 0, x_22);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_38, 0, x_37);
x_39 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_39, 0, x_25);
x_40 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_40, 0, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_41, 0, x_28);
x_42 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_43, 0, x_36);
lean_ctor_set(x_43, 1, x_9);
lean_ctor_set(x_43, 2, x_38);
lean_ctor_set(x_43, 3, x_40);
lean_ctor_set(x_43, 4, x_42);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_10);
x_45 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_44);
x_46 = lean_box(0);
x_47 = l_instInhabitedOfMonad___redArg(x_45, x_46);
x_48 = lean_alloc_closure((void*)(l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_panic_fn(x_48, x_1);
x_50 = lean_apply_7(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_50;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; size_t x_13; size_t x_14; lean_object* x_15; lean_object* x_16; size_t x_17; uint8_t x_18; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ptr_addr(x_1);
x_9 = lean_unsigned_to_nat(8192u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_sub(x_10, x_12);
x_14 = lean_usize_mod(x_8, x_13);
x_15 = lean_ctor_get(x_6, 0);
lean_inc(x_15);
lean_dec(x_6);
x_16 = lean_array_uget(x_15, x_14);
lean_dec(x_15);
x_17 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_18 = lean_usize_dec_eq(x_17, x_8);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
lean_free_object(x_4);
x_19 = lean_st_ref_take(x_2, x_7);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
x_24 = lean_array_uset(x_23, x_14, x_1);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
lean_ctor_set(x_19, 1, x_25);
lean_ctor_set(x_19, 0, x_24);
x_26 = lean_st_ref_set(x_2, x_19, x_22);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_26, 0);
lean_dec(x_28);
x_29 = lean_box(x_18);
lean_ctor_set(x_26, 0, x_29);
return x_26;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_26, 1);
lean_inc(x_30);
lean_dec(x_26);
x_31 = lean_box(x_18);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_33 = lean_ctor_get(x_19, 0);
x_34 = lean_ctor_get(x_19, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_19);
x_35 = lean_ctor_get(x_33, 0);
lean_inc(x_35);
x_36 = lean_array_uset(x_35, x_14, x_1);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_dec(x_33);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_st_ref_set(x_2, x_38, x_34);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_41 = x_39;
} else {
 lean_dec_ref(x_39);
 x_41 = lean_box(0);
}
x_42 = lean_box(x_18);
if (lean_is_scalar(x_41)) {
 x_43 = lean_alloc_ctor(0, 2, 0);
} else {
 x_43 = x_41;
}
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_40);
return x_43;
}
}
else
{
lean_object* x_44; 
lean_dec(x_1);
x_44 = lean_box(x_18);
lean_ctor_set(x_4, 0, x_44);
return x_4;
}
}
else
{
lean_object* x_45; lean_object* x_46; size_t x_47; lean_object* x_48; size_t x_49; lean_object* x_50; size_t x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; size_t x_56; uint8_t x_57; 
x_45 = lean_ctor_get(x_4, 0);
x_46 = lean_ctor_get(x_4, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_4);
x_47 = lean_ptr_addr(x_1);
x_48 = lean_unsigned_to_nat(8192u);
x_49 = lean_usize_of_nat(x_48);
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_usize_of_nat(x_50);
x_52 = lean_usize_sub(x_49, x_51);
x_53 = lean_usize_mod(x_47, x_52);
x_54 = lean_ctor_get(x_45, 0);
lean_inc(x_54);
lean_dec(x_45);
x_55 = lean_array_uget(x_54, x_53);
lean_dec(x_54);
x_56 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_57 = lean_usize_dec_eq(x_56, x_47);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_58 = lean_st_ref_take(x_2, x_46);
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_61 = x_58;
} else {
 lean_dec_ref(x_58);
 x_61 = lean_box(0);
}
x_62 = lean_ctor_get(x_59, 0);
lean_inc(x_62);
x_63 = lean_array_uset(x_62, x_53, x_1);
x_64 = lean_ctor_get(x_59, 1);
lean_inc(x_64);
lean_dec(x_59);
if (lean_is_scalar(x_61)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_61;
}
lean_ctor_set(x_65, 0, x_63);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_st_ref_set(x_2, x_65, x_60);
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_68 = x_66;
} else {
 lean_dec_ref(x_66);
 x_68 = lean_box(0);
}
x_69 = lean_box(x_57);
if (lean_is_scalar(x_68)) {
 x_70 = lean_alloc_ctor(0, 2, 0);
} else {
 x_70 = x_68;
}
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_67);
return x_70;
}
else
{
lean_object* x_71; lean_object* x_72; 
lean_dec(x_1);
x_71 = lean_box(x_57);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_46);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_12 = l_Lean_Expr_hash(x_1);
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
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_1, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_47; size_t x_48; size_t x_49; size_t x_50; lean_object* x_51; uint8_t x_52; 
lean_free_object(x_4);
x_29 = lean_st_ref_take(x_2, x_8);
x_30 = lean_ctor_get(x_29, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_29, 1);
lean_inc(x_32);
if (lean_is_exclusive(x_29)) {
 lean_ctor_release(x_29, 0);
 lean_ctor_release(x_29, 1);
 x_33 = x_29;
} else {
 lean_dec_ref(x_29);
 x_33 = lean_box(0);
}
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
x_47 = lean_array_get_size(x_35);
x_48 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_49 = lean_usize_sub(x_48, x_24);
x_50 = lean_usize_land(x_21, x_49);
x_51 = lean_array_uget(x_35, x_50);
x_52 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_1, x_51);
if (x_52 == 0)
{
uint8_t x_53; 
x_53 = !lean_is_exclusive(x_31);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_54 = lean_ctor_get(x_31, 1);
lean_dec(x_54);
x_55 = lean_ctor_get(x_31, 0);
lean_dec(x_55);
x_56 = lean_box(0);
x_57 = lean_nat_add(x_34, x_23);
lean_dec(x_34);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_56);
lean_ctor_set(x_58, 2, x_51);
x_59 = lean_array_uset(x_35, x_50, x_58);
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_nat_shiftl(x_57, x_60);
x_62 = lean_unsigned_to_nat(3u);
x_63 = lean_nat_div(x_61, x_62);
lean_dec(x_61);
x_64 = lean_array_get_size(x_59);
x_65 = lean_nat_dec_le(x_63, x_64);
lean_dec(x_64);
lean_dec(x_63);
if (x_65 == 0)
{
lean_object* x_66; 
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_59);
lean_ctor_set(x_31, 1, x_66);
lean_ctor_set(x_31, 0, x_57);
x_37 = x_31;
goto block_46;
}
else
{
lean_ctor_set(x_31, 1, x_59);
lean_ctor_set(x_31, 0, x_57);
x_37 = x_31;
goto block_46;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
lean_dec(x_31);
x_67 = lean_box(0);
x_68 = lean_nat_add(x_34, x_23);
lean_dec(x_34);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_67);
lean_ctor_set(x_69, 2, x_51);
x_70 = lean_array_uset(x_35, x_50, x_69);
x_71 = lean_unsigned_to_nat(2u);
x_72 = lean_nat_shiftl(x_68, x_71);
x_73 = lean_unsigned_to_nat(3u);
x_74 = lean_nat_div(x_72, x_73);
lean_dec(x_72);
x_75 = lean_array_get_size(x_70);
x_76 = lean_nat_dec_le(x_74, x_75);
lean_dec(x_75);
lean_dec(x_74);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; 
x_77 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_70);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_68);
lean_ctor_set(x_78, 1, x_77);
x_37 = x_78;
goto block_46;
}
else
{
lean_object* x_79; 
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_68);
lean_ctor_set(x_79, 1, x_70);
x_37 = x_79;
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
x_37 = x_31;
goto block_46;
}
block_46:
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
if (lean_is_scalar(x_33)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_33;
}
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = lean_st_ref_set(x_2, x_38, x_32);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_39, 0);
lean_dec(x_41);
x_42 = lean_box(x_28);
lean_ctor_set(x_39, 0, x_42);
return x_39;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_39, 1);
lean_inc(x_43);
lean_dec(x_39);
x_44 = lean_box(x_28);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
else
{
lean_object* x_80; 
lean_dec(x_1);
x_80 = lean_box(x_28);
lean_ctor_set(x_4, 0, x_80);
return x_4;
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; uint64_t x_84; lean_object* x_85; uint64_t x_86; uint64_t x_87; uint64_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; size_t x_93; size_t x_94; lean_object* x_95; size_t x_96; size_t x_97; size_t x_98; lean_object* x_99; uint8_t x_100; 
x_81 = lean_ctor_get(x_4, 1);
lean_inc(x_81);
lean_dec(x_4);
x_82 = lean_ctor_get(x_6, 1);
lean_inc(x_82);
lean_dec(x_6);
x_83 = lean_array_get_size(x_82);
x_84 = l_Lean_Expr_hash(x_1);
x_85 = lean_unsigned_to_nat(32u);
x_86 = lean_uint64_of_nat(x_85);
x_87 = lean_uint64_shift_right(x_84, x_86);
x_88 = lean_uint64_xor(x_84, x_87);
x_89 = lean_unsigned_to_nat(16u);
x_90 = lean_uint64_of_nat(x_89);
x_91 = lean_uint64_shift_right(x_88, x_90);
x_92 = lean_uint64_xor(x_88, x_91);
x_93 = lean_uint64_to_usize(x_92);
x_94 = lean_usize_of_nat(x_83);
lean_dec(x_83);
x_95 = lean_unsigned_to_nat(1u);
x_96 = lean_usize_of_nat(x_95);
x_97 = lean_usize_sub(x_94, x_96);
x_98 = lean_usize_land(x_93, x_97);
x_99 = lean_array_uget(x_82, x_98);
lean_dec(x_82);
x_100 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_1, x_99);
lean_dec(x_99);
if (x_100 == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_117; size_t x_118; size_t x_119; size_t x_120; lean_object* x_121; uint8_t x_122; 
x_101 = lean_st_ref_take(x_2, x_81);
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
x_104 = lean_ctor_get(x_101, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_105 = x_101;
} else {
 lean_dec_ref(x_101);
 x_105 = lean_box(0);
}
x_106 = lean_ctor_get(x_103, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_103, 1);
lean_inc(x_107);
x_108 = lean_ctor_get(x_102, 0);
lean_inc(x_108);
lean_dec(x_102);
x_117 = lean_array_get_size(x_107);
x_118 = lean_usize_of_nat(x_117);
lean_dec(x_117);
x_119 = lean_usize_sub(x_118, x_96);
x_120 = lean_usize_land(x_93, x_119);
x_121 = lean_array_uget(x_107, x_120);
x_122 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_CollectFVars_visit_spec__0(lean_box(0), x_1, x_121);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_123 = x_103;
} else {
 lean_dec_ref(x_103);
 x_123 = lean_box(0);
}
x_124 = lean_box(0);
x_125 = lean_nat_add(x_106, x_95);
lean_dec(x_106);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_1);
lean_ctor_set(x_126, 1, x_124);
lean_ctor_set(x_126, 2, x_121);
x_127 = lean_array_uset(x_107, x_120, x_126);
x_128 = lean_unsigned_to_nat(2u);
x_129 = lean_nat_shiftl(x_125, x_128);
x_130 = lean_unsigned_to_nat(3u);
x_131 = lean_nat_div(x_129, x_130);
lean_dec(x_129);
x_132 = lean_array_get_size(x_127);
x_133 = lean_nat_dec_le(x_131, x_132);
lean_dec(x_132);
lean_dec(x_131);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; 
x_134 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_CollectFVars_visit_spec__1___redArg(x_127);
if (lean_is_scalar(x_123)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_123;
}
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
x_109 = x_135;
goto block_116;
}
else
{
lean_object* x_136; 
if (lean_is_scalar(x_123)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_123;
}
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_127);
x_109 = x_136;
goto block_116;
}
}
else
{
lean_dec(x_121);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_1);
x_109 = x_103;
goto block_116;
}
block_116:
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
if (lean_is_scalar(x_105)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_105;
}
lean_ctor_set(x_110, 0, x_108);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_st_ref_set(x_2, x_110, x_104);
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
x_114 = lean_box(x_100);
if (lean_is_scalar(x_113)) {
 x_115 = lean_alloc_ctor(0, 2, 0);
} else {
 x_115 = x_113;
}
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_112);
return x_115;
}
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_1);
x_137 = lean_box(x_100);
x_138 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_81);
return x_138;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_16 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_1, x_2, x_3, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_1, x_2, x_3, x_6, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
return x_18;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 5:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 1);
lean_inc(x_16);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_17 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_2, x_3, x_4, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_2, x_3, x_4, x_16, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_18);
return x_19;
}
else
{
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
case 6:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_3);
lean_dec(x_2);
x_20 = lean_ctor_get(x_1, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_1, 2);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_24 = lean_box(x_23);
x_25 = lean_apply_12(x_5, x_20, x_21, x_22, x_24, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_25;
}
case 7:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_3);
lean_dec(x_2);
x_26 = lean_ctor_get(x_1, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_1, 2);
lean_inc(x_28);
x_29 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_30 = lean_box(x_29);
x_31 = lean_apply_12(x_5, x_26, x_27, x_28, x_30, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_31;
}
case 8:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_5);
x_32 = lean_ctor_get(x_1, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 3);
lean_inc(x_34);
lean_dec(x_1);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_35 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_2, x_3, x_4, x_32, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_3);
lean_inc(x_2);
x_37 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_2, x_3, x_4, x_33, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_2, x_3, x_4, x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_38);
return x_39;
}
else
{
lean_dec(x_34);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_37;
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
return x_35;
}
}
case 10:
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_5);
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_2, x_3, x_4, x_40, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_41;
}
case 11:
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_5);
x_42 = lean_ctor_get(x_1, 2);
lean_inc(x_42);
lean_dec(x_1);
x_43 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_2, x_3, x_4, x_42, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
return x_43;
}
default: 
{
lean_object* x_44; lean_object* x_45; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_14);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_4);
x_13 = l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___redArg(x_4, x_5, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_18 = lean_alloc_closure((void*)(l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__0___boxed), 15, 3);
lean_closure_set(x_18, 0, x_1);
lean_closure_set(x_18, 1, x_2);
lean_closure_set(x_18, 2, x_17);
lean_inc(x_1);
lean_inc(x_4);
x_19 = lean_apply_1(x_1, x_4);
x_20 = lean_unbox(x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1(x_4, x_1, x_2, x_3, x_18, x_21, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_16);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; uint8_t x_25; 
lean_inc(x_4);
x_23 = l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___redArg(x_4, x_5, x_16);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_unbox(x_24);
lean_dec(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
lean_dec(x_23);
lean_inc(x_2);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_4);
x_27 = lean_apply_8(x_2, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_26);
if (lean_obj_tag(x_27) == 0)
{
if (x_3 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 1);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1(x_4, x_1, x_2, x_3, x_18, x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_28);
return x_30;
}
else
{
uint8_t x_31; 
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_31 = !lean_is_exclusive(x_27);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_27, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_27, 0, x_33);
return x_27;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_dec(x_27);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_27;
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 1);
lean_inc(x_37);
lean_dec(x_23);
x_38 = lean_box(0);
x_39 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1(x_4, x_1, x_2, x_3, x_18, x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_37);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_13);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_13, 0);
lean_dec(x_41);
x_42 = lean_box(0);
lean_ctor_set(x_13, 0, x_42);
return x_13;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_13, 1);
lean_inc(x_43);
lean_dec(x_13);
x_44 = lean_box(0);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_43);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = l_Lean_ForEachExprWhere_initCache;
x_13 = lean_st_mk_ref(x_12, x_11);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
lean_inc(x_14);
x_16 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_1, x_2, x_4, x_3, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_15);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_st_ref_get(x_14, x_18);
lean_dec(x_14);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_17);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
lean_dec(x_14);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeConst(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_10, 0);
lean_dec(x_12);
x_13 = lean_box(0);
lean_ctor_set(x_10, 0, x_13);
return x_10;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
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
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_1);
x_21 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.TypeAnalysis", 57, 57);
x_22 = lean_mk_string_unchecked("Lean.Elab.Tactic.BVDecide.Frontend.Normalize.typeAnalysisPass.analyzeType", 73, 73);
x_23 = lean_unsigned_to_nat(198u);
x_24 = lean_unsigned_to_nat(36u);
x_25 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_26 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_21, x_22, x_23, x_24, x_25);
lean_dec(x_25);
lean_dec(x_22);
lean_dec(x_21);
x_27 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0(x_26, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType___lam__0), 8, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Expr_isConst___boxed), 1, 0);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
x_13 = l_Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1(x_10, x_9, x_1, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_13;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__0___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_visited___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_ForEachExprWhere_checked___at___Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_3);
lean_dec(x_3);
x_17 = lean_unbox(x_7);
lean_dec(x_7);
x_18 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__0(x_1, x_2, x_16, x_4, x_5, x_6, x_17, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_4);
lean_dec(x_4);
x_16 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___lam__1(x_1, x_2, x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Lean_ForEachExprWhere_visit_go___at___Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1_spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_ForEachExprWhere_visit___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType_spec__1(x_1, x_2, x_3, x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_Expr_hasMVar(x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_1);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_6 = lean_st_ref_get(x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
lean_dec(x_7);
x_10 = l_Lean_instantiateMVarsCore(x_9, x_1);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_st_ref_take(x_2, x_8);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 2);
lean_inc(x_17);
x_18 = lean_ctor_get(x_14, 3);
lean_inc(x_18);
x_19 = lean_ctor_get(x_14, 4);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_20, 0, x_12);
lean_ctor_set(x_20, 1, x_16);
lean_ctor_set(x_20, 2, x_17);
lean_ctor_set(x_20, 3, x_18);
lean_ctor_set(x_20, 4, x_19);
x_21 = lean_st_ref_set(x_2, x_20, x_15);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
lean_ctor_set(x_21, 0, x_11);
return x_21;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_21, 1);
lean_inc(x_24);
lean_dec(x_21);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_11);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(x_1, x_5, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_4, x_3);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_array_uget(x_2, x_4);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_16);
x_17 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1(x_1, x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_21, 0, x_18);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_16);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_24, 0, x_18);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_16);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_23);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; 
lean_dec(x_16);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
x_28 = lean_ctor_get(x_18, 0);
lean_inc(x_28);
lean_dec(x_18);
x_29 = lean_box(0);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_usize_of_nat(x_31);
x_33 = lean_usize_add(x_4, x_32);
x_4 = x_33;
x_5 = x_30;
x_12 = x_27;
goto _start;
}
}
else
{
uint8_t x_35; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_35 = !lean_is_exclusive(x_17);
if (x_35 == 0)
{
return x_17;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_17, 0);
x_37 = lean_ctor_get(x_17, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_17);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_38; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_38 = l_Lean_LocalDecl_isLet(x_25);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_LocalDecl_isImplementationDetail(x_25);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_25, 3);
lean_inc(x_40);
lean_dec(x_25);
x_27 = x_40;
goto block_37;
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
block_37:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(x_27, x_8, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_15 = x_26;
x_16 = x_32;
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_38; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_38 = l_Lean_LocalDecl_isLet(x_25);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_LocalDecl_isImplementationDetail(x_25);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_25, 3);
lean_inc(x_40);
lean_dec(x_25);
x_27 = x_40;
goto block_37;
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
block_37:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(x_27, x_8, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_15 = x_26;
x_16 = x_32;
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2_spec__2(x_1, x_2, x_20, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; size_t x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_3);
x_15 = lean_array_size(x_12);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_usize_of_nat(x_16);
x_18 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__1(x_1, x_12, x_15, x_17, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_12);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_18, 0);
lean_dec(x_22);
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_23);
lean_ctor_set(x_18, 0, x_2);
return x_18;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
lean_dec(x_18);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
lean_ctor_set_tag(x_2, 1);
lean_ctor_set(x_2, 0, x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_2);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_19);
lean_free_object(x_2);
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
lean_free_object(x_2);
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
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; size_t x_40; lean_object* x_41; size_t x_42; lean_object* x_43; 
x_37 = lean_ctor_get(x_2, 0);
lean_inc(x_37);
lean_dec(x_2);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_3);
x_40 = lean_array_size(x_37);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_usize_of_nat(x_41);
x_43 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__1(x_1, x_37, x_40, x_42, x_39, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_37);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_47 = x_43;
} else {
 lean_dec_ref(x_43);
 x_47 = lean_box(0);
}
x_48 = lean_ctor_get(x_44, 1);
lean_inc(x_48);
lean_dec(x_44);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
if (lean_is_scalar(x_47)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_47;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_44);
x_51 = lean_ctor_get(x_43, 1);
lean_inc(x_51);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_52 = x_43;
} else {
 lean_dec_ref(x_43);
 x_52 = lean_box(0);
}
x_53 = lean_ctor_get(x_45, 0);
lean_inc(x_53);
lean_dec(x_45);
if (lean_is_scalar(x_52)) {
 x_54 = lean_alloc_ctor(0, 2, 0);
} else {
 x_54 = x_52;
}
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_43, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_43, 1);
lean_inc(x_56);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_57 = x_43;
} else {
 lean_dec_ref(x_43);
 x_57 = lean_box(0);
}
if (lean_is_scalar(x_57)) {
 x_58 = lean_alloc_ctor(1, 2, 0);
} else {
 x_58 = x_57;
}
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_56);
return x_58;
}
}
}
else
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; lean_object* x_66; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_box(0);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_61);
lean_ctor_set(x_62, 1, x_3);
x_63 = lean_array_size(x_60);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_usize_of_nat(x_64);
x_66 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2(x_60, x_63, x_65, x_62, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_67, 0);
lean_inc(x_68);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_66);
if (x_69 == 0)
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = lean_ctor_get(x_67, 1);
lean_inc(x_71);
lean_dec(x_67);
lean_ctor_set(x_2, 0, x_71);
lean_ctor_set(x_66, 0, x_2);
return x_66;
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_72 = lean_ctor_get(x_66, 1);
lean_inc(x_72);
lean_dec(x_66);
x_73 = lean_ctor_get(x_67, 1);
lean_inc(x_73);
lean_dec(x_67);
lean_ctor_set(x_2, 0, x_73);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_72);
return x_74;
}
}
else
{
uint8_t x_75; 
lean_dec(x_67);
lean_free_object(x_2);
x_75 = !lean_is_exclusive(x_66);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = lean_ctor_get(x_66, 0);
lean_dec(x_76);
x_77 = lean_ctor_get(x_68, 0);
lean_inc(x_77);
lean_dec(x_68);
lean_ctor_set(x_66, 0, x_77);
return x_66;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_66, 1);
lean_inc(x_78);
lean_dec(x_66);
x_79 = lean_ctor_get(x_68, 0);
lean_inc(x_79);
lean_dec(x_68);
x_80 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_78);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_free_object(x_2);
x_81 = !lean_is_exclusive(x_66);
if (x_81 == 0)
{
return x_66;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_66, 0);
x_83 = lean_ctor_get(x_66, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_66);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; size_t x_88; lean_object* x_89; size_t x_90; lean_object* x_91; 
x_85 = lean_ctor_get(x_2, 0);
lean_inc(x_85);
lean_dec(x_2);
x_86 = lean_box(0);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set(x_87, 1, x_3);
x_88 = lean_array_size(x_85);
x_89 = lean_unsigned_to_nat(0u);
x_90 = lean_usize_of_nat(x_89);
x_91 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2(x_85, x_88, x_90, x_87, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_85);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; 
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
if (lean_obj_tag(x_93) == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_95 = x_91;
} else {
 lean_dec_ref(x_91);
 x_95 = lean_box(0);
}
x_96 = lean_ctor_get(x_92, 1);
lean_inc(x_96);
lean_dec(x_92);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_96);
if (lean_is_scalar(x_95)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_95;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_94);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_dec(x_92);
x_99 = lean_ctor_get(x_91, 1);
lean_inc(x_99);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_100 = x_91;
} else {
 lean_dec_ref(x_91);
 x_100 = lean_box(0);
}
x_101 = lean_ctor_get(x_93, 0);
lean_inc(x_101);
lean_dec(x_93);
if (lean_is_scalar(x_100)) {
 x_102 = lean_alloc_ctor(0, 2, 0);
} else {
 x_102 = x_100;
}
lean_ctor_set(x_102, 0, x_101);
lean_ctor_set(x_102, 1, x_99);
return x_102;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_103 = lean_ctor_get(x_91, 0);
lean_inc(x_103);
x_104 = lean_ctor_get(x_91, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_91)) {
 lean_ctor_release(x_91, 0);
 lean_ctor_release(x_91, 1);
 x_105 = x_91;
} else {
 lean_dec_ref(x_91);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(1, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_38; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_38 = l_Lean_LocalDecl_isLet(x_25);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_LocalDecl_isImplementationDetail(x_25);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_25, 3);
lean_inc(x_40);
lean_dec(x_25);
x_27 = x_40;
goto block_37;
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
block_37:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(x_27, x_8, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_15 = x_26;
x_16 = x_32;
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_4 = x_17;
x_11 = x_16;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_4);
lean_ctor_set(x_13, 1, x_11);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_23; 
x_14 = lean_box(0);
x_23 = lean_array_uget(x_1, x_3);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_4, 1);
lean_inc(x_24);
lean_dec(x_4);
x_15 = x_24;
x_16 = x_11;
goto block_22;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_38; 
lean_dec(x_4);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_box(0);
x_38 = l_Lean_LocalDecl_isLet(x_25);
if (x_38 == 0)
{
uint8_t x_39; 
x_39 = l_Lean_LocalDecl_isImplementationDetail(x_25);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_25, 3);
lean_inc(x_40);
lean_dec(x_25);
x_27 = x_40;
goto block_37;
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
}
else
{
lean_dec(x_25);
x_15 = x_26;
x_16 = x_11;
goto block_22;
}
block_37:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(x_27, x_8, x_11);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_31 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_analyzeType(x_29, x_5, x_6, x_7, x_8, x_9, x_10, x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_15 = x_26;
x_16 = x_32;
goto block_22;
}
else
{
uint8_t x_33; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_33 = !lean_is_exclusive(x_31);
if (x_33 == 0)
{
return x_31;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_31);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
}
}
block_22:
{
lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5_spec__5(x_1, x_2, x_20, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_16);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1(x_2, x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_ctor_get(x_12, 0);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; size_t x_24; lean_object* x_25; size_t x_26; lean_object* x_27; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_1, 1);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_20);
x_24 = lean_array_size(x_21);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_usize_of_nat(x_25);
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5(x_21, x_24, x_26, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_27);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
x_31 = lean_ctor_get(x_27, 0);
lean_dec(x_31);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
lean_dec(x_28);
lean_ctor_set(x_27, 0, x_32);
return x_27;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_27, 1);
lean_inc(x_33);
lean_dec(x_27);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_33);
return x_35;
}
}
else
{
uint8_t x_36; 
lean_dec(x_28);
x_36 = !lean_is_exclusive(x_27);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_27, 0);
lean_dec(x_37);
x_38 = lean_ctor_get(x_29, 0);
lean_inc(x_38);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_38);
return x_27;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_27, 1);
lean_inc(x_39);
lean_dec(x_27);
x_40 = lean_ctor_get(x_29, 0);
lean_inc(x_40);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_27);
if (x_42 == 0)
{
return x_27;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_27, 0);
x_44 = lean_ctor_get(x_27, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_27);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_11);
if (x_46 == 0)
{
return x_11;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_11, 0);
x_48 = lean_ctor_get(x_11, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_11);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = lean_apply_7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_closure((void*)(l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg___lam__0), 8, 3);
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
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 2);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = l_Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1(x_10, x_9, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_9);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_9);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
else
{
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext___lam__0), 7, 0);
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg(x_1, x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_instantiateMVars___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__1(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2_spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1_spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_PersistentArray_forInAux___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5_spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_PersistentArray_forIn___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__1_spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_MVarId_withContext___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext_spec__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__0(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__0(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__0(x_4, x_9);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__2(lean_object* x_1, lean_object* x_2) {
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
x_5 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__2(x_1, x_4);
lean_inc(x_3);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_10 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__2(x_4, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_13; 
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_13 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_checkContext(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_114; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_st_ref_get(x_3, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
if (lean_is_exclusive(x_15)) {
 lean_ctor_release(x_15, 0);
 lean_ctor_release(x_15, 1);
 x_18 = x_15;
} else {
 lean_dec_ref(x_15);
 x_18 = lean_box(0);
}
x_19 = lean_mk_string_unchecked("Meta", 4, 4);
x_20 = lean_mk_string_unchecked("Tactic", 6, 6);
x_21 = lean_mk_string_unchecked("bv", 2, 2);
x_22 = l_Lean_Name_mkStr3(x_19, x_20, x_21);
lean_inc(x_22);
x_42 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___redArg(x_22, x_6, x_17);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_45 = x_42;
} else {
 lean_dec_ref(x_42);
 x_45 = lean_box(0);
}
x_46 = lean_ctor_get(x_16, 2);
lean_inc(x_46);
lean_dec(x_16);
x_114 = lean_unbox(x_43);
lean_dec(x_43);
if (x_114 == 0)
{
x_90 = x_2;
x_91 = x_3;
x_92 = x_4;
x_93 = x_5;
x_94 = x_6;
x_95 = x_7;
x_96 = x_44;
goto block_113;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_115 = lean_mk_string_unchecked("Type analysis found structures: ", 32, 32);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_128 = lean_ctor_get(x_46, 0);
lean_inc(x_128);
x_129 = lean_box(0);
x_130 = lean_ctor_get(x_128, 1);
lean_inc(x_130);
lean_dec(x_128);
x_131 = lean_array_get_size(x_130);
x_132 = lean_unsigned_to_nat(0u);
x_133 = lean_nat_dec_lt(x_132, x_131);
if (x_133 == 0)
{
lean_dec(x_131);
lean_dec(x_130);
x_117 = x_129;
goto block_127;
}
else
{
size_t x_134; size_t x_135; lean_object* x_136; 
x_134 = lean_usize_of_nat(x_131);
lean_dec(x_131);
x_135 = lean_usize_of_nat(x_132);
x_136 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__3(x_130, x_134, x_135, x_129);
lean_dec(x_130);
x_117 = x_136;
goto block_127;
}
block_127:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_118 = lean_box(0);
x_119 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_117, x_118);
x_120 = l_Lean_MessageData_ofList(x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_116);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked("", 0, 0);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
lean_inc(x_22);
x_125 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(x_22, x_124, x_2, x_3, x_4, x_5, x_6, x_7, x_44);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_90 = x_2;
x_91 = x_3;
x_92 = x_4;
x_93 = x_5;
x_94 = x_6;
x_95 = x_7;
x_96 = x_126;
goto block_113;
}
}
block_41:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_32 = lean_box(0);
x_33 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_31, x_32);
x_34 = l_Lean_MessageData_ofList(x_33);
if (lean_is_scalar(x_18)) {
 x_35 = lean_alloc_ctor(7, 2, 0);
} else {
 x_35 = x_18;
 lean_ctor_set_tag(x_35, 7);
}
lean_ctor_set(x_35, 0, x_29);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_mk_string_unchecked("", 0, 0);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_38, 0, x_35);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(x_22, x_38, x_26, x_27, x_30, x_23, x_28, x_24, x_25);
lean_dec(x_24);
lean_dec(x_28);
lean_dec(x_23);
lean_dec(x_27);
lean_dec(x_26);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_9 = x_40;
goto block_12;
}
block_70:
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_inc(x_22);
x_54 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___redArg(x_22, x_51, x_53);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_dec(x_52);
lean_dec(x_51);
lean_dec(x_50);
lean_dec(x_48);
lean_dec(x_47);
lean_dec(x_46);
lean_dec(x_22);
lean_dec(x_18);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_9 = x_57;
goto block_12;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_ctor_get(x_54, 1);
lean_inc(x_58);
lean_dec(x_54);
x_59 = lean_mk_string_unchecked("Type analysis found matchers: ", 30, 30);
x_60 = l_Lean_stringToMessageData(x_59);
lean_dec(x_59);
x_61 = lean_ctor_get(x_46, 2);
lean_inc(x_61);
lean_dec(x_46);
x_62 = lean_box(0);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_array_get_size(x_63);
x_65 = lean_unsigned_to_nat(0u);
x_66 = lean_nat_dec_lt(x_65, x_64);
if (x_66 == 0)
{
lean_dec(x_64);
lean_dec(x_63);
x_23 = x_50;
x_24 = x_52;
x_25 = x_58;
x_26 = x_47;
x_27 = x_48;
x_28 = x_51;
x_29 = x_60;
x_30 = x_49;
x_31 = x_62;
goto block_41;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_68 = lean_usize_of_nat(x_65);
x_69 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__1(x_63, x_67, x_68, x_62);
lean_dec(x_63);
x_23 = x_50;
x_24 = x_52;
x_25 = x_58;
x_26 = x_47;
x_27 = x_48;
x_28 = x_51;
x_29 = x_60;
x_30 = x_49;
x_31 = x_69;
goto block_41;
}
}
}
block_89:
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_80 = lean_box(0);
x_81 = l_List_mapTR_loop___at___Lean_compileDecls_doCompile_spec__0(x_79, x_80);
x_82 = l_Lean_MessageData_ofList(x_81);
if (lean_is_scalar(x_45)) {
 x_83 = lean_alloc_ctor(7, 2, 0);
} else {
 x_83 = x_45;
 lean_ctor_set_tag(x_83, 7);
}
lean_ctor_set(x_83, 0, x_75);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_mk_string_unchecked("", 0, 0);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_83);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_22);
x_87 = l_Lean_addTrace___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__5(x_22, x_86, x_72, x_77, x_78, x_73, x_74, x_76, x_71);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_47 = x_72;
x_48 = x_77;
x_49 = x_78;
x_50 = x_73;
x_51 = x_74;
x_52 = x_76;
x_53 = x_88;
goto block_70;
}
block_113:
{
lean_object* x_97; lean_object* x_98; uint8_t x_99; 
lean_inc(x_22);
x_97 = l_Lean_isTracingEnabledFor___at___Lean_withTraceNode___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Pass_fixpointPipeline_spec__0_spec__0___redArg(x_22, x_94, x_96);
x_98 = lean_ctor_get(x_97, 0);
lean_inc(x_98);
x_99 = lean_unbox(x_98);
lean_dec(x_98);
if (x_99 == 0)
{
lean_object* x_100; 
lean_dec(x_45);
x_100 = lean_ctor_get(x_97, 1);
lean_inc(x_100);
lean_dec(x_97);
x_47 = x_90;
x_48 = x_91;
x_49 = x_92;
x_50 = x_93;
x_51 = x_94;
x_52 = x_95;
x_53 = x_100;
goto block_70;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint8_t x_109; 
x_101 = lean_ctor_get(x_97, 1);
lean_inc(x_101);
lean_dec(x_97);
x_102 = lean_mk_string_unchecked("Type analysis found enums: ", 27, 27);
x_103 = l_Lean_stringToMessageData(x_102);
lean_dec(x_102);
x_104 = lean_ctor_get(x_46, 1);
lean_inc(x_104);
x_105 = lean_box(0);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
x_107 = lean_array_get_size(x_106);
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_nat_dec_lt(x_108, x_107);
if (x_109 == 0)
{
lean_dec(x_107);
lean_dec(x_106);
x_71 = x_101;
x_72 = x_90;
x_73 = x_93;
x_74 = x_94;
x_75 = x_103;
x_76 = x_95;
x_77 = x_91;
x_78 = x_92;
x_79 = x_105;
goto block_89;
}
else
{
size_t x_110; size_t x_111; lean_object* x_112; 
x_110 = lean_usize_of_nat(x_107);
lean_dec(x_107);
x_111 = lean_usize_of_nat(x_108);
x_112 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__3(x_106, x_110, x_111, x_105);
lean_dec(x_106);
x_71 = x_101;
x_72 = x_90;
x_73 = x_93;
x_74 = x_94;
x_75 = x_103;
x_76 = x_95;
x_77 = x_91;
x_78 = x_92;
x_79 = x_112;
goto block_89;
}
}
}
}
else
{
uint8_t x_137; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_137 = !lean_is_exclusive(x_13);
if (x_137 == 0)
{
return x_13;
}
else
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_13, 0);
x_139 = lean_ctor_get(x_13, 1);
lean_inc(x_139);
lean_inc(x_138);
lean_dec(x_13);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_139);
return x_140;
}
}
block_12:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
}
static lean_object* _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass___lam__0___boxed), 8, 0);
x_2 = lean_mk_string_unchecked("typeAnalysis", 12, 12);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_foldrM___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass_spec__3(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
return x_9;
}
}
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_TypeAnalysis(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_SInt_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_builtinTypes = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_builtinTypes();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_builtinTypes);
l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass = _init_l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass();
lean_mark_persistent(l_Lean_Elab_Tactic_BVDecide_Frontend_Normalize_typeAnalysisPass);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
