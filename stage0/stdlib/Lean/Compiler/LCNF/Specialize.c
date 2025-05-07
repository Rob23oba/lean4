// Lean compiler output
// Module: Lean.Compiler.LCNF.Specialize
// Imports: Lean.Compiler.Specialize Lean.Compiler.LCNF.Simp Lean.Compiler.LCNF.SpecInfo Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.ToExpr Lean.Compiler.LCNF.Level Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.MonadScope Lean.Compiler.LCNF.Closure Lean.Compiler.LCNF.FVarUtil
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__0(size_t, size_t, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_read(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_SMap_contains___at___Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_1145__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_saveSpecParamInfo_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_eqv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at___Lean_Compiler_LCNF_Specialize_mkKey_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__2(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveBase___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4406_(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0___lam__0(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedDecl;
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_setLevelParams(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specCacheExt;
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(lean_object*, lean_object*, uint8_t);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry;
lean_object* l_Lean_Compiler_LCNF_allFVar___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_paramsToVarSet(lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_saveSpecParamInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_addEntry(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1(lean_object*, lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_Compiler_LCNF_normLevelParams(lean_object*);
uint8_t l_Lean_Expr_hasLooseBVars(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_collectArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Internalize_internalizeParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6___lam__0___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_main(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_switch___at___Lean_Compiler_SpecState_switch_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Closure_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getSpecParamInfoCore_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_getRemainingArgs_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_OptionT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_name_append_index_after(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__2____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_Collector_collect_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__1____x40_Lean_Compiler_LCNF_Specialize___hyg_49____boxed(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at___Lean_Compiler_LCNF_Specialize_mkKey_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_appendCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0___boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_Collector_collect_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_OptionT_pure(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
extern lean_object* l_Lean_Expr_instHashable;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM;
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_specialize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_initFn___lam__1____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_instantiate_rev(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_specialize_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickCmp(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__0____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object*);
uint8_t l_Lean_Expr_hasFVar(lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instTraverseFVarLetValue;
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs___boxed(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsNoCache(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_paramsToVarSet___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_toExpr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_specialize_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__2____x40_Lean_Compiler_LCNF_Specialize___hyg_49____boxed(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_getRemainingArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_expr_abstract_range(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize;
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__7(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0___boxed(lean_object*, lean_object*);
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_2 = l_Lean_Name_mkStr1(x_1);
x_3 = lean_box(0);
x_4 = l_Lean_Expr_const___override(x_2, x_3);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_addEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = l_Lean_SMap_insert___at___Lean_Compiler_SpecState_addEntry_spec__0(lean_box(0), x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Compiler_LCNF_Specialize_addEntry(x_4, x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_2, x_9);
x_2 = x_10;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_13);
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__0(x_12, x_17, x_18, x_4);
lean_dec(x_12);
x_5 = x_19;
goto block_10;
}
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_12 = lean_array_uget(x_1, x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
uint8_t x_16; 
x_16 = lean_nat_dec_le(x_14, x_14);
if (x_16 == 0)
{
lean_dec(x_14);
lean_dec(x_12);
x_5 = x_4;
goto block_10;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_13);
x_18 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__0(x_12, x_17, x_18, x_4);
lean_dec(x_12);
x_5 = x_19;
goto block_10;
}
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_9 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1_spec__1(x_1, x_8, x_3, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_2);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_1;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1(x_2, x_7, x_8, x_1);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__0____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_array_mk(x_1);
return x_2;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_initFn___lam__1____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = l_Lean_SMap_contains___at___Lean_Compiler_initFn____x40_Lean_Compiler_Specialize___hyg_1145__spec__0___redArg(x_1, x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
return x_6;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__2____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; 
x_2 = lean_box(1);
x_3 = lean_unsigned_to_nat(8u);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_unsigned_to_nat(2u);
x_6 = lean_nat_shiftl(x_3, x_5);
x_7 = lean_unsigned_to_nat(3u);
x_8 = lean_nat_div(x_6, x_7);
lean_dec(x_6);
x_9 = l_Nat_nextPowerOfTwo(x_8);
lean_dec(x_8);
x_10 = lean_box(0);
x_11 = lean_mk_array(x_9, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_11);
x_13 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_unbox(x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*2, x_16);
x_17 = l_Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0(x_15, x_1);
x_18 = l_Lean_SMap_switch___at___Lean_Compiler_SpecState_switch_spec__0(lean_box(0), x_17);
lean_dec(x_17);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; lean_object* x_22; 
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_initFn___lam__0____x40_Lean_Compiler_LCNF_Specialize___hyg_49_), 1, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_initFn___lam__1____x40_Lean_Compiler_LCNF_Specialize___hyg_49____boxed), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_initFn___lam__2____x40_Lean_Compiler_LCNF_Specialize___hyg_49____boxed), 1, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_6 = l_Lean_Expr_instHashable;
x_7 = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), x_5, x_6);
lean_dec(x_5);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Compiler", 8, 8);
x_10 = lean_mk_string_unchecked("LCNF", 4, 4);
x_11 = lean_mk_string_unchecked("Specialize", 10, 10);
x_12 = lean_mk_string_unchecked("specCacheExt", 12, 12);
x_13 = l_Lean_Name_mkStr5(x_8, x_9, x_10, x_11, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_addEntry), 2, 0);
x_15 = lean_box(0);
lean_inc(x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_SimplePersistentEnvExtension_replayOfFilter___boxed), 7, 4);
lean_closure_set(x_16, 0, lean_box(0));
lean_closure_set(x_16, 1, lean_box(0));
lean_closure_set(x_16, 2, x_3);
lean_closure_set(x_16, 3, x_14);
x_17 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_17, 0, x_16);
x_18 = lean_box(1);
x_19 = lean_alloc_ctor(0, 5, 2);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_14);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_2);
lean_ctor_set(x_19, 4, x_17);
x_20 = lean_unbox(x_15);
lean_ctor_set_uint8(x_19, sizeof(void*)*5, x_20);
x_21 = lean_unbox(x_18);
lean_ctor_set_uint8(x_19, sizeof(void*)*5 + 1, x_21);
x_22 = l_Lean_registerSimplePersistentEnvExtension(lean_box(0), lean_box(0), x_7, x_19, x_1);
lean_dec(x_7);
return x_22;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_mkStateFromImportedEntries___at___Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49__spec__0(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__1____x40_Lean_Compiler_LCNF_Specialize___hyg_49____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Specialize_initFn___lam__1____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_initFn___lam__2____x40_Lean_Compiler_LCNF_Specialize___hyg_49____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Specialize_initFn___lam__2____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_Specialize_specCacheExt;
lean_ctor_set(x_5, 1, x_2);
lean_ctor_set(x_5, 0, x_1);
x_11 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_10, x_9, x_5);
x_12 = lean_ctor_get(x_7, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 2);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 3);
lean_inc(x_14);
x_15 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
lean_inc(x_16);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_ctor_get(x_7, 5);
lean_inc(x_18);
x_19 = lean_ctor_get(x_7, 6);
lean_inc(x_19);
x_20 = lean_ctor_get(x_7, 7);
lean_inc(x_20);
lean_dec(x_7);
x_21 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_21, 0, x_11);
lean_ctor_set(x_21, 1, x_12);
lean_ctor_set(x_21, 2, x_13);
lean_ctor_set(x_21, 3, x_14);
lean_ctor_set(x_21, 4, x_17);
lean_ctor_set(x_21, 5, x_18);
lean_ctor_set(x_21, 6, x_19);
lean_ctor_set(x_21, 7, x_20);
x_22 = lean_st_ref_set(x_3, x_21, x_8);
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_22, 0);
lean_dec(x_24);
x_25 = lean_box(0);
lean_ctor_set(x_22, 0, x_25);
return x_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_22, 1);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
return x_28;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_29 = lean_ctor_get(x_5, 0);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_5);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = l_Lean_Compiler_LCNF_Specialize_specCacheExt;
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_1);
lean_ctor_set(x_33, 1, x_2);
x_34 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_32, x_31, x_33);
x_35 = lean_ctor_get(x_29, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 3);
lean_inc(x_37);
x_38 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
lean_inc(x_39);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_ctor_get(x_29, 5);
lean_inc(x_41);
x_42 = lean_ctor_get(x_29, 6);
lean_inc(x_42);
x_43 = lean_ctor_get(x_29, 7);
lean_inc(x_43);
lean_dec(x_29);
x_44 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_44, 0, x_34);
lean_ctor_set(x_44, 1, x_35);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_37);
lean_ctor_set(x_44, 4, x_40);
lean_ctor_set(x_44, 5, x_41);
lean_ctor_set(x_44, 6, x_42);
lean_ctor_set(x_44, 7, x_43);
x_45 = lean_st_ref_set(x_3, x_44, x_30);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_45)) {
 lean_ctor_release(x_45, 0);
 lean_ctor_release(x_45, 1);
 x_47 = x_45;
} else {
 lean_dec_ref(x_45);
 x_47 = lean_box(0);
}
x_48 = lean_box(0);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
return x_49;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_cacheSpec___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Specialize_cacheSpec(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_8 = l_Lean_Expr_instHashable;
x_9 = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), x_7, x_8);
lean_dec(x_7);
x_10 = lean_ctor_get(x_6, 0);
lean_inc(x_10);
lean_dec(x_6);
x_11 = l_Lean_Compiler_LCNF_Specialize_specCacheExt;
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*3);
lean_dec(x_12);
x_14 = l_Lean_SimplePersistentEnvExtension_getState(lean_box(0), lean_box(0), x_9, x_11, x_10, x_13);
x_15 = l_Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0___redArg(x_14, x_1);
lean_ctor_set(x_4, 0, x_15);
return x_4;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_16 = lean_ctor_get(x_4, 0);
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_4);
x_18 = lean_alloc_closure((void*)(l_Lean_Expr_eqv___boxed), 2, 0);
x_19 = l_Lean_Expr_instHashable;
x_20 = l_Lean_SMap_instInhabited(lean_box(0), lean_box(0), x_18, x_19);
lean_dec(x_18);
x_21 = lean_ctor_get(x_16, 0);
lean_inc(x_21);
lean_dec(x_16);
x_22 = l_Lean_Compiler_LCNF_Specialize_specCacheExt;
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*3);
lean_dec(x_23);
x_25 = l_Lean_SimplePersistentEnvExtension_getState(lean_box(0), lean_box(0), x_20, x_22, x_21, x_24);
x_26 = l_Lean_SMap_find_x3f___at___Lean_Compiler_getCachedSpecialization_spec__0___redArg(x_25, x_1);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
return x_27;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_4, 0);
lean_inc(x_11);
x_12 = lean_apply_1(x_2, x_11);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_4, 2);
lean_inc(x_14);
lean_dec(x_4);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_13);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_apply_7(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10);
return x_16;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_1 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__0___boxed), 8, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__1), 10, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_7 = l_instMonadEIO(lean_box(0));
x_8 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
lean_dec(x_9);
lean_inc(x_10);
x_11 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_11, 0, x_10);
x_12 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_12, 0, x_10);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_15 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_16, 0, x_15);
x_17 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_18 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_18, 0, x_17);
x_19 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_19, 0, x_18);
x_20 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, lean_box(0));
x_21 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_21, 0, x_20);
x_22 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_22, 0, x_21);
lean_inc(x_22);
lean_inc(x_19);
lean_inc(x_16);
x_23 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_5);
lean_ctor_set(x_23, 2, x_16);
lean_ctor_set(x_23, 3, x_19);
lean_ctor_set(x_23, 4, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
x_25 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
lean_dec(x_26);
lean_inc(x_27);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_28, 0, x_27);
x_29 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_29, 0, x_27);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_31, 0, x_16);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_33, 0, x_19);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_35, 0, x_22);
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_30);
lean_ctor_set(x_37, 1, x_3);
lean_ctor_set(x_37, 2, x_32);
lean_ctor_set(x_37, 3, x_34);
lean_ctor_set(x_37, 4, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_4);
x_39 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_38);
lean_inc(x_39);
x_40 = lean_alloc_closure((void*)(l_ReaderT_read), 4, 3);
lean_closure_set(x_40, 0, lean_box(0));
lean_closure_set(x_40, 1, lean_box(0));
lean_closure_set(x_40, 2, x_39);
x_41 = lean_alloc_closure((void*)(l_ReaderT_bind), 8, 7);
lean_closure_set(x_41, 0, lean_box(0));
lean_closure_set(x_41, 1, lean_box(0));
lean_closure_set(x_41, 2, x_39);
lean_closure_set(x_41, 3, lean_box(0));
lean_closure_set(x_41, 4, lean_box(0));
lean_closure_set(x_41, 5, x_40);
lean_closure_set(x_41, 6, x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_2);
return x_42;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Name_quickCmp(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_RBNode_findCore___redArg(x_1, x_2, x_3);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__0___boxed), 2, 0);
x_6 = lean_ctor_get(x_3, 1);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__1___boxed), 3, 2);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
x_8 = l_Lean_Compiler_LCNF_allFVar___redArg(x_1, x_7, x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Specialize_isGround___redArg(x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_Specialize_isGround___redArg___lam__1(x_1, x_2, x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Specialize_isGround(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_10 = l_Lean_Compiler_LCNF_instTraverseFVarLetValue;
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_inc(x_3);
x_12 = l_Lean_Compiler_LCNF_Specialize_isGround___redArg(x_10, x_11, x_3, x_9);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = !lean_is_exclusive(x_3);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_3, 0);
x_17 = lean_ctor_get(x_3, 1);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_18);
x_19 = l_Lean_FVarIdSet_insert(x_16, x_18);
x_20 = lean_unbox(x_13);
lean_dec(x_13);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_18);
lean_ctor_set(x_3, 0, x_19);
x_21 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = l_Lean_FVarIdSet_insert(x_17, x_18);
lean_ctor_set(x_3, 1, x_22);
lean_ctor_set(x_3, 0, x_19);
x_23 = lean_apply_7(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_14);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_24 = lean_ctor_get(x_3, 0);
x_25 = lean_ctor_get(x_3, 1);
x_26 = lean_ctor_get(x_3, 2);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_3);
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
lean_inc(x_27);
x_28 = l_Lean_FVarIdSet_insert(x_24, x_27);
x_29 = lean_unbox(x_13);
lean_dec(x_13);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_27);
x_30 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_25);
lean_ctor_set(x_30, 2, x_26);
x_31 = lean_apply_7(x_2, x_30, x_4, x_5, x_6, x_7, x_8, x_14);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = l_Lean_FVarIdSet_insert(x_25, x_27);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_28);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_26);
x_34 = lean_apply_7(x_2, x_33, x_4, x_5, x_6, x_7, x_8, x_14);
return x_34;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_withLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = l_Lean_Compiler_LCNF_instTraverseFVarLetValue;
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_4);
x_13 = l_Lean_Compiler_LCNF_Specialize_isGround___redArg(x_11, x_12, x_4, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = !lean_is_exclusive(x_4);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
lean_dec(x_2);
lean_inc(x_19);
x_20 = l_Lean_FVarIdSet_insert(x_17, x_19);
x_21 = lean_unbox(x_14);
lean_dec(x_14);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_19);
lean_ctor_set(x_4, 0, x_20);
x_22 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = l_Lean_FVarIdSet_insert(x_18, x_19);
lean_ctor_set(x_4, 1, x_23);
lean_ctor_set(x_4, 0, x_20);
x_24 = lean_apply_7(x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_15);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_4, 0);
x_26 = lean_ctor_get(x_4, 1);
x_27 = lean_ctor_get(x_4, 2);
lean_inc(x_27);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_4);
x_28 = lean_ctor_get(x_2, 0);
lean_inc(x_28);
lean_dec(x_2);
lean_inc(x_28);
x_29 = l_Lean_FVarIdSet_insert(x_25, x_28);
x_30 = lean_unbox(x_14);
lean_dec(x_14);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_28);
x_31 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_27);
x_32 = lean_apply_7(x_3, x_31, x_5, x_6, x_7, x_8, x_9, x_15);
return x_32;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = l_Lean_FVarIdSet_insert(x_26, x_28);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_27);
x_35 = lean_apply_7(x_3, x_34, x_5, x_6, x_7, x_8, x_9, x_15);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_Collector_collect_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_3, x_2);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_11);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_21, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_array_uget(x_1, x_3);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_21, 0);
lean_inc(x_30);
lean_dec(x_21);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_23, x_31);
lean_inc(x_30);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
x_34 = lean_box(x_29);
if (lean_obj_tag(x_34) == 4)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
lean_dec(x_30);
lean_dec(x_23);
x_35 = lean_box(0);
x_36 = lean_array_push(x_22, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_33);
lean_ctor_set(x_37, 1, x_36);
x_12 = x_37;
x_13 = x_11;
goto block_18;
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_34);
x_38 = lean_array_fget(x_30, x_23);
lean_dec(x_23);
lean_dec(x_30);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_38);
x_39 = l_Lean_Compiler_LCNF_Closure_collectArg(x_38, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_38);
x_42 = lean_array_push(x_22, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_33);
lean_ctor_set(x_43, 1, x_42);
x_12 = x_43;
x_13 = x_40;
goto block_18;
}
else
{
uint8_t x_44; 
lean_dec(x_38);
lean_dec(x_33);
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_44 = !lean_is_exclusive(x_39);
if (x_44 == 0)
{
return x_39;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_39, 0);
x_46 = lean_ctor_get(x_39, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_39);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
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
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_4 = lean_ctor_get(x_1, 2);
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_array_get_size(x_5);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_3);
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
x_22 = lean_array_uget(x_5, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_3, x_22);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_2, 1);
x_25 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_24, x_3);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; uint8_t x_27; 
x_26 = lean_box(1);
x_27 = lean_unbox(x_26);
return x_27;
}
else
{
lean_dec(x_25);
return x_23;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_box(0);
x_29 = lean_unbox(x_28);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_Collector_collect_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
lean_ctor_set(x_12, 0, x_15);
return x_12;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_12);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
return x_12;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = lean_ctor_get(x_12, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_12);
x_23 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_23, 0, x_21);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_st_ref_get(x_5, x_8);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
lean_inc(x_3);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_14, 0, x_13);
lean_closure_set(x_14, 1, x_3);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_mk_empty_array_with_capacity(x_15);
x_17 = lean_array_get_size(x_2);
x_18 = l_Array_toSubarray___redArg(x_2, x_15, x_17);
lean_ctor_set(x_9, 1, x_16);
lean_ctor_set(x_9, 0, x_18);
x_19 = lean_array_size(x_1);
x_20 = lean_usize_of_nat(x_15);
x_21 = lean_box_usize(x_19);
x_22 = lean_box_usize(x_20);
x_23 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__1___boxed), 11, 4);
lean_closure_set(x_23, 0, x_1);
lean_closure_set(x_23, 1, x_21);
lean_closure_set(x_23, 2, x_22);
lean_closure_set(x_23, 3, x_9);
x_24 = lean_ctor_get(x_3, 0);
lean_inc(x_24);
lean_dec(x_3);
x_25 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_25, 0, x_24);
x_26 = l_Lean_Compiler_LCNF_Closure_run(lean_box(0), x_23, x_25, x_14, x_4, x_5, x_6, x_7, x_12);
return x_26;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; size_t x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_27 = lean_ctor_get(x_9, 0);
x_28 = lean_ctor_get(x_9, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_9);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_3);
x_30 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_30, 0, x_29);
lean_closure_set(x_30, 1, x_3);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_mk_empty_array_with_capacity(x_31);
x_33 = lean_array_get_size(x_2);
x_34 = l_Array_toSubarray___redArg(x_2, x_31, x_33);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_array_size(x_1);
x_37 = lean_usize_of_nat(x_31);
x_38 = lean_box_usize(x_36);
x_39 = lean_box_usize(x_37);
x_40 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__1___boxed), 11, 4);
lean_closure_set(x_40, 0, x_1);
lean_closure_set(x_40, 1, x_38);
lean_closure_set(x_40, 2, x_39);
lean_closure_set(x_40, 3, x_35);
x_41 = lean_ctor_get(x_3, 0);
lean_inc(x_41);
lean_dec(x_3);
x_42 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__2___boxed), 2, 1);
lean_closure_set(x_42, 0, x_41);
x_43 = l_Lean_Compiler_LCNF_Closure_run(lean_box(0), x_40, x_42, x_30, x_4, x_5, x_6, x_7, x_28);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg(x_1, x_2, x_3, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_Collector_collect_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_Collector_collect_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg___lam__2(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_Collector_collect___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Specialize_Collector_collect(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM_go___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_apply_1(x_1, x_2);
x_4 = lean_unbox(x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_apply_1(x_3, x_6);
lean_ctor_set(x_4, 0, x_7);
return x_4;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_4, 0);
lean_inc(x_8);
lean_dec(x_4);
x_9 = lean_apply_1(x_3, x_8);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_4) == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_4, 0);
lean_dec(x_6);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
else
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_3);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_5; 
lean_dec(x_4);
x_5 = lean_box(0);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
lean_dec(x_3);
x_7 = lean_box(0);
x_8 = lean_apply_1(x_4, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_6);
return x_8;
}
else
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_apply_1(x_6, x_10);
lean_ctor_set(x_8, 0, x_11);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_apply_1(x_6, x_12);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
if (lean_obj_tag(x_6) == 0)
{
return x_6;
}
else
{
lean_dec(x_6);
lean_inc(x_3);
return x_3;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_4);
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_box(0);
x_6 = lean_apply_1(x_4, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_2 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__0), 4, 0);
x_3 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__1), 4, 0);
x_4 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__2), 4, 0);
x_5 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__3___boxed), 4, 0);
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__4___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_8 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_9 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_10 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_11 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_12 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_13 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
x_15 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_9);
lean_ctor_set(x_15, 2, x_10);
lean_ctor_set(x_15, 3, x_11);
lean_ctor_set(x_15, 4, x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_3);
lean_inc(x_16);
x_18 = lean_alloc_closure((void*)(l_OptionT_pure), 4, 2);
lean_closure_set(x_18, 0, lean_box(0));
lean_closure_set(x_18, 1, x_16);
x_19 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_19, 0, x_17);
lean_ctor_set(x_19, 1, x_18);
lean_ctor_set(x_19, 2, x_4);
lean_ctor_set(x_19, 3, x_5);
lean_ctor_set(x_19, 4, x_6);
x_20 = lean_alloc_closure((void*)(l_OptionT_bind), 6, 2);
lean_closure_set(x_20, 0, lean_box(0));
lean_closure_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
x_22 = lean_box(0);
x_23 = l_instInhabitedOfMonad___redArg(x_21, x_22);
x_24 = lean_panic_fn(x_23, x_1);
return x_24;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_1);
x_6 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_3);
if (lean_obj_tag(x_6) == 0)
{
lean_dec(x_4);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_7; 
lean_dec(x_6);
x_7 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_4);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
case 2:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_2);
lean_dec(x_1);
x_5 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_6 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_7 = lean_unsigned_to_nat(43u);
x_8 = lean_unsigned_to_nat(38u);
x_9 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_10 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
x_11 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(x_10);
return x_11;
}
case 5:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 1);
lean_inc(x_13);
lean_dec(x_2);
lean_inc(x_1);
x_14 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_12);
if (lean_obj_tag(x_14) == 0)
{
lean_dec(x_13);
lean_dec(x_1);
return x_14;
}
else
{
lean_dec(x_14);
x_2 = x_13;
goto _start;
}
}
case 6:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_20 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1___lam__0(x_1, x_16, x_17, x_18, x_19);
lean_dec(x_16);
return x_20;
}
case 7:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_2, 2);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_25 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1___lam__0(x_1, x_21, x_22, x_23, x_24);
lean_dec(x_21);
return x_25;
}
case 8:
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_2);
lean_dec(x_1);
x_26 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_27 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_28 = lean_unsigned_to_nat(43u);
x_29 = lean_unsigned_to_nat(38u);
x_30 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_31 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_26, x_27, x_28, x_29, x_30);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
x_32 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(x_31);
return x_32;
}
case 11:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_2);
lean_dec(x_1);
x_33 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_34 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_35 = lean_unsigned_to_nat(43u);
x_36 = lean_unsigned_to_nat(38u);
x_37 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_38 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_33, x_34, x_35, x_36, x_37);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1(x_38);
return x_39;
}
default: 
{
lean_object* x_40; lean_object* x_41; 
lean_dec(x_2);
lean_dec(x_1);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_41, 0, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
lean_dec(x_1);
x_3 = lean_box(0);
x_4 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_apply_1(x_1, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1(x_1, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_allFVarM_go___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_box(0);
x_5 = lean_unbox(x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
lean_dec(x_3);
x_6 = lean_box(1);
x_7 = lean_unbox(x_6);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg(x_1, x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__7(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
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
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_box(0);
x_22 = lean_ctor_get(x_4, 1);
lean_inc(x_22);
lean_dec(x_4);
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 2);
lean_inc(x_24);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_22);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_11);
return x_27;
}
else
{
lean_object* x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_37; 
x_28 = lean_array_uget(x_1, x_3);
x_29 = lean_unbox(x_28);
lean_dec(x_28);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_unsigned_to_nat(1u);
x_32 = lean_nat_add(x_23, x_31);
lean_inc(x_30);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_30);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_24);
x_37 = lean_box(x_29);
switch (lean_obj_tag(x_37)) {
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_30);
lean_dec(x_23);
lean_dec(x_5);
x_38 = lean_box(x_25);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_33);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_11);
return x_41;
}
case 2:
{
lean_dec(x_30);
lean_dec(x_23);
x_34 = x_11;
goto block_36;
}
case 4:
{
lean_dec(x_30);
lean_dec(x_23);
x_34 = x_11;
goto block_36;
}
default: 
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
lean_dec(x_37);
x_42 = lean_array_fget(x_30, x_23);
lean_dec(x_23);
lean_dec(x_30);
lean_inc(x_5);
x_43 = l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg(x_42, x_5, x_11);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_unbox(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_21);
lean_ctor_set(x_47, 1, x_33);
x_12 = x_47;
x_13 = x_46;
goto block_18;
}
else
{
uint8_t x_48; 
lean_dec(x_5);
x_48 = !lean_is_exclusive(x_43);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_43, 0);
lean_dec(x_49);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_44);
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_33);
lean_ctor_set(x_43, 0, x_51);
return x_43;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_ctor_get(x_43, 1);
lean_inc(x_52);
lean_dec(x_43);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_44);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_33);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
}
}
}
block_36:
{
lean_object* x_35; 
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_21);
lean_ctor_set(x_35, 1, x_33);
x_12 = x_35;
x_13 = x_34;
goto block_18;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_2);
x_12 = l_Array_toSubarray___redArg(x_2, x_10, x_11);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_array_size(x_1);
x_16 = lean_usize_of_nat(x_10);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__7(x_1, x_15, x_16, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_17, 0, x_22);
return x_17;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_17, 1);
lean_inc(x_23);
lean_dec(x_17);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_23);
return x_25;
}
}
else
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_17);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_17, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_19, 0);
lean_inc(x_28);
lean_dec(x_19);
lean_ctor_set(x_17, 0, x_28);
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_ctor_get(x_19, 0);
lean_inc(x_30);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__3(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1_spec__1___lam__4(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_5);
lean_dec(x_5);
x_7 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__7(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_shouldSpecialize___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_get_size(x_3);
x_7 = lean_nat_dec_lt(x_4, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
x_8 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_1);
x_9 = lean_expr_abstract(x_8, x_2);
lean_dec(x_8);
x_10 = lean_expr_instantiate_rev(x_9, x_5);
lean_dec(x_5);
lean_dec(x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_3, x_4);
x_12 = lean_expr_abstract_range(x_11, x_4, x_2);
lean_dec(x_11);
x_13 = lean_expr_instantiate_rev(x_12, x_5);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_nat_add(x_4, x_14);
lean_dec(x_4);
x_16 = lean_array_push(x_5, x_13);
x_4 = x_15;
x_5 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_5);
lean_dec(x_5);
x_9 = l_Lean_Expr_fvar___override(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_2, x_11);
x_13 = lean_array_uset(x_7, x_2, x_9);
x_2 = x_12;
x_3 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__1(size_t x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_box(0);
x_7 = lean_array_uset(x_3, x_2, x_6);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_5, 0);
lean_inc(x_20);
lean_dec(x_5);
x_21 = lean_ctor_get(x_20, 3);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_21);
x_8 = x_22;
goto block_14;
}
else
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_5, 0);
lean_inc(x_23);
lean_dec(x_5);
x_15 = x_23;
goto block_19;
}
block_14:
{
lean_object* x_9; size_t x_10; size_t x_11; lean_object* x_12; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
block_19:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_mk_empty_array_with_capacity(x_16);
x_18 = l_Lean_Compiler_LCNF_FunDeclCore_toExpr(x_15, x_17);
lean_dec(x_17);
x_8 = x_18;
goto block_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; lean_object* x_5; size_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_array_size(x_1);
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_usize_of_nat(x_5);
lean_inc(x_1);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__0(x_4, x_6, x_1);
x_8 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__1(x_4, x_6, x_1);
x_9 = lean_mk_empty_array_with_capacity(x_5);
x_10 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls_go(x_2, x_7, x_8, x_5, x_9);
lean_dec(x_8);
lean_dec(x_7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___redArg(x_1, x_2, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Specialize_expandCodeDecls_spec__1(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at___Lean_Compiler_LCNF_Specialize_mkKey_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_4, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
lean_dec(x_4);
x_9 = l___private_Lean_Compiler_LCNF_ToExpr_0__Lean_Expr_abstract_x27_go(x_6, x_5, x_1);
x_10 = lean_array_get_size(x_2);
x_11 = l_Lean_Compiler_LCNF_ToExpr_mkLambdaM_go(x_2, x_5, x_6, x_10, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_array_fget(x_3, x_4);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_nat_add(x_4, x_15);
lean_dec(x_4);
lean_inc(x_5);
x_17 = l_Lean_RBNode_insert___at___Lean_FVarIdSet_insert_spec__0___redArg(x_6, x_14, x_5);
x_18 = lean_nat_add(x_5, x_15);
lean_dec(x_5);
x_4 = x_16;
x_5 = x_18;
x_6 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_Compiler_LCNF_Specialize_expandCodeDecls___redArg(x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_ToExpr_withParams_go___at___Lean_Compiler_LCNF_Specialize_mkKey_spec__0(x_7, x_1, x_1, x_8, x_8, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = l_Lean_Compiler_LCNF_normLevelParams(x_11);
lean_ctor_set(x_5, 0, x_12);
return x_5;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_13 = lean_ctor_get(x_5, 0);
x_14 = lean_ctor_get(x_5, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_5);
x_15 = lean_unsigned_to_nat(0u);
x_16 = lean_box(0);
x_17 = l_Lean_Compiler_LCNF_ToExpr_withParams_go___at___Lean_Compiler_LCNF_Specialize_mkKey_spec__0(x_13, x_1, x_1, x_15, x_15, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
lean_dec(x_17);
x_19 = l_Lean_Compiler_LCNF_normLevelParams(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_14);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_mkKey___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ToExpr_withParams_go___at___Lean_Compiler_LCNF_Specialize_mkKey_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_ToExpr_withParams_go___at___Lean_Compiler_LCNF_Specialize_mkKey_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Specialize_mkKey___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkKey___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_mkKey(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_20; 
x_20 = lean_usize_dec_lt(x_5, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_2);
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_6);
lean_ctor_set(x_21, 1, x_12);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_6, 1);
lean_inc(x_23);
lean_dec(x_6);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_22, 2);
lean_inc(x_25);
x_26 = lean_nat_dec_lt(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_2);
lean_dec(x_1);
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
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_array_uget(x_3, x_5);
x_30 = lean_ctor_get(x_22, 0);
lean_inc(x_30);
lean_dec(x_22);
x_31 = lean_array_fget(x_30, x_24);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_nat_add(x_24, x_32);
lean_dec(x_24);
x_34 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_34, 0, x_30);
lean_ctor_set(x_34, 1, x_33);
lean_ctor_set(x_34, 2, x_25);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_ctor_get(x_29, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_29, 2);
lean_inc(x_37);
x_38 = lean_ctor_get(x_1, 1);
lean_inc(x_38);
lean_inc(x_2);
x_39 = l_Lean_Expr_instantiateLevelParamsNoCache(x_37, x_38, x_2);
x_40 = lean_ctor_get_uint8(x_29, sizeof(void*)*3);
lean_dec(x_29);
x_41 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_39);
lean_ctor_set_uint8(x_41, sizeof(void*)*3, x_40);
x_42 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_41, x_7, x_8, x_9, x_10, x_11, x_12);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_ctor_get(x_42, 1);
x_46 = lean_array_push(x_23, x_44);
lean_ctor_set(x_42, 1, x_46);
lean_ctor_set(x_42, 0, x_34);
x_13 = x_42;
x_14 = x_45;
goto block_19;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_ctor_get(x_42, 0);
x_48 = lean_ctor_get(x_42, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_42);
x_49 = lean_array_push(x_23, x_47);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_34);
lean_ctor_set(x_50, 1, x_49);
x_13 = x_50;
x_14 = x_48;
goto block_19;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_66; 
x_51 = lean_ctor_get(x_31, 0);
lean_inc(x_51);
lean_dec(x_31);
x_52 = lean_st_ref_get(x_7, x_12);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_55 = lean_st_ref_take(x_7, x_54);
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_66 = !lean_is_exclusive(x_56);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint64_t x_73; lean_object* x_74; uint64_t x_75; uint64_t x_76; uint64_t x_77; lean_object* x_78; uint64_t x_79; uint64_t x_80; uint64_t x_81; size_t x_82; size_t x_83; size_t x_84; size_t x_85; size_t x_86; lean_object* x_87; uint8_t x_88; 
x_67 = lean_ctor_get(x_56, 0);
x_68 = lean_ctor_get(x_56, 1);
x_69 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_53, x_51, x_26);
lean_dec(x_53);
x_70 = lean_ctor_get(x_29, 0);
lean_inc(x_70);
lean_dec(x_29);
x_71 = l_Lean_Compiler_LCNF_Arg_toExpr(x_69);
x_72 = lean_array_get_size(x_68);
x_73 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_70);
x_74 = lean_unsigned_to_nat(32u);
x_75 = lean_uint64_of_nat(x_74);
x_76 = lean_uint64_shift_right(x_73, x_75);
x_77 = lean_uint64_xor(x_73, x_76);
x_78 = lean_unsigned_to_nat(16u);
x_79 = lean_uint64_of_nat(x_78);
x_80 = lean_uint64_shift_right(x_77, x_79);
x_81 = lean_uint64_xor(x_77, x_80);
x_82 = lean_uint64_to_usize(x_81);
x_83 = lean_usize_of_nat(x_72);
lean_dec(x_72);
x_84 = lean_usize_of_nat(x_32);
x_85 = lean_usize_sub(x_83, x_84);
x_86 = lean_usize_land(x_82, x_85);
x_87 = lean_array_uget(x_68, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_70, x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; 
x_89 = lean_nat_add(x_67, x_32);
lean_dec(x_67);
x_90 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_90, 0, x_70);
lean_ctor_set(x_90, 1, x_71);
lean_ctor_set(x_90, 2, x_87);
x_91 = lean_array_uset(x_68, x_86, x_90);
x_92 = lean_unsigned_to_nat(2u);
x_93 = lean_nat_shiftl(x_89, x_92);
x_94 = lean_unsigned_to_nat(3u);
x_95 = lean_nat_div(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_91);
x_97 = lean_nat_dec_le(x_95, x_96);
lean_dec(x_96);
lean_dec(x_95);
if (x_97 == 0)
{
lean_object* x_98; 
x_98 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_91);
lean_ctor_set(x_56, 1, x_98);
lean_ctor_set(x_56, 0, x_89);
x_58 = x_56;
goto block_65;
}
else
{
lean_ctor_set(x_56, 1, x_91);
lean_ctor_set(x_56, 0, x_89);
x_58 = x_56;
goto block_65;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_99 = lean_box(0);
x_100 = lean_array_uset(x_68, x_86, x_99);
x_101 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_70, x_71, x_87);
x_102 = lean_array_uset(x_100, x_86, x_101);
lean_ctor_set(x_56, 1, x_102);
x_58 = x_56;
goto block_65;
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; uint64_t x_109; lean_object* x_110; uint64_t x_111; uint64_t x_112; uint64_t x_113; lean_object* x_114; uint64_t x_115; uint64_t x_116; uint64_t x_117; size_t x_118; size_t x_119; size_t x_120; size_t x_121; size_t x_122; lean_object* x_123; uint8_t x_124; 
x_103 = lean_ctor_get(x_56, 0);
x_104 = lean_ctor_get(x_56, 1);
lean_inc(x_104);
lean_inc(x_103);
lean_dec(x_56);
x_105 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgImp(x_53, x_51, x_26);
lean_dec(x_53);
x_106 = lean_ctor_get(x_29, 0);
lean_inc(x_106);
lean_dec(x_29);
x_107 = l_Lean_Compiler_LCNF_Arg_toExpr(x_105);
x_108 = lean_array_get_size(x_104);
x_109 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_106);
x_110 = lean_unsigned_to_nat(32u);
x_111 = lean_uint64_of_nat(x_110);
x_112 = lean_uint64_shift_right(x_109, x_111);
x_113 = lean_uint64_xor(x_109, x_112);
x_114 = lean_unsigned_to_nat(16u);
x_115 = lean_uint64_of_nat(x_114);
x_116 = lean_uint64_shift_right(x_113, x_115);
x_117 = lean_uint64_xor(x_113, x_116);
x_118 = lean_uint64_to_usize(x_117);
x_119 = lean_usize_of_nat(x_108);
lean_dec(x_108);
x_120 = lean_usize_of_nat(x_32);
x_121 = lean_usize_sub(x_119, x_120);
x_122 = lean_usize_land(x_118, x_121);
x_123 = lean_array_uget(x_104, x_122);
x_124 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_106, x_123);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; uint8_t x_133; 
x_125 = lean_nat_add(x_103, x_32);
lean_dec(x_103);
x_126 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_126, 0, x_106);
lean_ctor_set(x_126, 1, x_107);
lean_ctor_set(x_126, 2, x_123);
x_127 = lean_array_uset(x_104, x_122, x_126);
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
x_134 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_127);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_125);
lean_ctor_set(x_135, 1, x_134);
x_58 = x_135;
goto block_65;
}
else
{
lean_object* x_136; 
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_125);
lean_ctor_set(x_136, 1, x_127);
x_58 = x_136;
goto block_65;
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_137 = lean_box(0);
x_138 = lean_array_uset(x_104, x_122, x_137);
x_139 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_106, x_107, x_123);
x_140 = lean_array_uset(x_138, x_122, x_139);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_103);
lean_ctor_set(x_141, 1, x_140);
x_58 = x_141;
goto block_65;
}
}
block_65:
{
lean_object* x_59; uint8_t x_60; 
x_59 = lean_st_ref_set(x_7, x_58, x_57);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; 
x_61 = lean_ctor_get(x_59, 1);
x_62 = lean_ctor_get(x_59, 0);
lean_dec(x_62);
lean_ctor_set(x_59, 1, x_23);
lean_ctor_set(x_59, 0, x_34);
x_13 = x_59;
x_14 = x_61;
goto block_19;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_59, 1);
lean_inc(x_63);
lean_dec(x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_34);
lean_ctor_set(x_64, 1, x_23);
x_13 = x_64;
x_14 = x_63;
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
x_17 = lean_usize_add(x_5, x_16);
x_5 = x_17;
x_6 = x_13;
x_12 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_5, x_4);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; size_t x_29; size_t x_30; 
x_15 = lean_ctor_get(x_3, 0);
x_16 = lean_array_uget(x_15, x_5);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 2);
lean_inc(x_19);
x_20 = lean_ctor_get(x_1, 1);
lean_inc(x_20);
lean_inc(x_2);
x_21 = l_Lean_Expr_instantiateLevelParamsNoCache(x_19, x_20, x_2);
x_22 = lean_ctor_get_uint8(x_16, sizeof(void*)*3);
lean_dec(x_16);
x_23 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_23, 0, x_17);
lean_ctor_set(x_23, 1, x_18);
lean_ctor_set(x_23, 2, x_21);
lean_ctor_set_uint8(x_23, sizeof(void*)*3, x_22);
x_24 = l_Lean_Compiler_LCNF_Internalize_internalizeParam(x_23, x_7, x_8, x_9, x_10, x_11, x_12);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_push(x_6, x_25);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_add(x_5, x_29);
x_5 = x_30;
x_6 = x_27;
x_12 = x_26;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_8 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
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
x_45 = l_Lean_Compiler_LCNF_instInhabitedDecl;
x_46 = l_instInhabitedOfMonad___redArg(x_44, x_45);
x_47 = lean_panic_fn(x_46, x_1);
x_48 = lean_apply_6(x_47, x_2, x_3, x_4, x_5, x_6, x_7);
return x_48;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_6, 4);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; size_t x_17; lean_object* x_18; size_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; size_t x_23; lean_object* x_24; uint8_t x_25; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_array_size(x_3);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_usize_of_nat(x_18);
x_20 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_17, x_19, x_3, x_8, x_9, x_10, x_11, x_12, x_13);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_array_size(x_4);
x_24 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(x_23, x_19, x_4, x_8, x_9, x_10, x_11, x_12, x_22);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; size_t x_39; lean_object* x_40; size_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = lean_array_get_size(x_2);
lean_inc(x_28);
x_29 = l_Array_toSubarray___redArg(x_2, x_18, x_28);
x_30 = lean_ctor_get(x_6, 3);
lean_inc(x_30);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_24, 0, x_29);
x_31 = lean_array_size(x_30);
lean_inc(x_1);
lean_inc(x_6);
x_32 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0(x_6, x_1, x_30, x_31, x_19, x_24, x_8, x_9, x_10, x_11, x_12, x_27);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_get_size(x_30);
x_37 = l_Array_toSubarray___redArg(x_30, x_28, x_36);
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
x_39 = lean_usize_of_nat(x_38);
lean_dec(x_38);
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
x_41 = lean_usize_of_nat(x_40);
lean_dec(x_40);
lean_inc(x_1);
lean_inc(x_6);
x_42 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1(x_6, x_1, x_37, x_39, x_41, x_35, x_8, x_9, x_10, x_11, x_12, x_34);
lean_dec(x_37);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_6, 1);
lean_inc(x_45);
x_46 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_45, x_1, x_16);
x_47 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_46, x_8, x_9, x_10, x_11, x_12, x_44);
lean_dec(x_8);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = l_Lean_Compiler_LCNF_attachCodeDecls(x_26, x_48);
lean_dec(x_26);
lean_inc(x_50);
x_51 = l_Lean_Compiler_LCNF_Code_inferType(x_50, x_9, x_10, x_11, x_12, x_49);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_43);
x_54 = l_Lean_Compiler_LCNF_mkForallParams(x_43, x_52, x_9, x_10, x_11, x_12, x_53);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_52);
if (lean_obj_tag(x_54) == 0)
{
uint8_t x_55; 
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; uint8_t x_57; uint8_t x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_54, 0);
lean_ctor_set(x_14, 0, x_50);
x_57 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_58 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
lean_dec(x_6);
x_59 = lean_box(0);
x_60 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_60, 0, x_7);
lean_ctor_set(x_60, 1, x_5);
lean_ctor_set(x_60, 2, x_56);
lean_ctor_set(x_60, 3, x_43);
lean_ctor_set(x_60, 4, x_14);
lean_ctor_set(x_60, 5, x_59);
lean_ctor_set_uint8(x_60, sizeof(void*)*6, x_58);
lean_ctor_set_uint8(x_60, sizeof(void*)*6 + 1, x_57);
x_61 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_60);
lean_ctor_set(x_54, 0, x_61);
return x_54;
}
else
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; uint8_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_62 = lean_ctor_get(x_54, 0);
x_63 = lean_ctor_get(x_54, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_54);
lean_ctor_set(x_14, 0, x_50);
x_64 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_65 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
lean_dec(x_6);
x_66 = lean_box(0);
x_67 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_67, 0, x_7);
lean_ctor_set(x_67, 1, x_5);
lean_ctor_set(x_67, 2, x_62);
lean_ctor_set(x_67, 3, x_43);
lean_ctor_set(x_67, 4, x_14);
lean_ctor_set(x_67, 5, x_66);
lean_ctor_set_uint8(x_67, sizeof(void*)*6, x_65);
lean_ctor_set_uint8(x_67, sizeof(void*)*6 + 1, x_64);
x_68 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_67);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_63);
return x_69;
}
}
else
{
uint8_t x_70; 
lean_dec(x_50);
lean_dec(x_43);
lean_free_object(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_70 = !lean_is_exclusive(x_54);
if (x_70 == 0)
{
return x_54;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_54, 0);
x_72 = lean_ctor_get(x_54, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_54);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
else
{
uint8_t x_74; 
lean_dec(x_50);
lean_dec(x_43);
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_74 = !lean_is_exclusive(x_51);
if (x_74 == 0)
{
return x_51;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_51, 0);
x_76 = lean_ctor_get(x_51, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_51);
x_77 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; size_t x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; size_t x_92; lean_object* x_93; size_t x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_78 = lean_ctor_get(x_24, 0);
x_79 = lean_ctor_get(x_24, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_24);
x_80 = lean_array_get_size(x_2);
lean_inc(x_80);
x_81 = l_Array_toSubarray___redArg(x_2, x_18, x_80);
x_82 = lean_ctor_get(x_6, 3);
lean_inc(x_82);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_81);
lean_ctor_set(x_83, 1, x_21);
x_84 = lean_array_size(x_82);
lean_inc(x_1);
lean_inc(x_6);
x_85 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0(x_6, x_1, x_82, x_84, x_19, x_83, x_8, x_9, x_10, x_11, x_12, x_79);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 1);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_array_get_size(x_82);
x_90 = l_Array_toSubarray___redArg(x_82, x_80, x_89);
x_91 = lean_ctor_get(x_90, 2);
lean_inc(x_91);
x_92 = lean_usize_of_nat(x_91);
lean_dec(x_91);
x_93 = lean_ctor_get(x_90, 1);
lean_inc(x_93);
x_94 = lean_usize_of_nat(x_93);
lean_dec(x_93);
lean_inc(x_1);
lean_inc(x_6);
x_95 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1(x_6, x_1, x_90, x_92, x_94, x_88, x_8, x_9, x_10, x_11, x_12, x_87);
lean_dec(x_90);
x_96 = lean_ctor_get(x_95, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_95, 1);
lean_inc(x_97);
lean_dec(x_95);
x_98 = lean_ctor_get(x_6, 1);
lean_inc(x_98);
x_99 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_98, x_1, x_16);
x_100 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_99, x_8, x_9, x_10, x_11, x_12, x_97);
lean_dec(x_8);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Compiler_LCNF_attachCodeDecls(x_78, x_101);
lean_dec(x_78);
lean_inc(x_103);
x_104 = l_Lean_Compiler_LCNF_Code_inferType(x_103, x_9, x_10, x_11, x_12, x_102);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_104, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_104, 1);
lean_inc(x_106);
lean_dec(x_104);
lean_inc(x_96);
x_107 = l_Lean_Compiler_LCNF_mkForallParams(x_96, x_105, x_9, x_10, x_11, x_12, x_106);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_105);
if (lean_obj_tag(x_107) == 0)
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_108 = lean_ctor_get(x_107, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_107, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_110 = x_107;
} else {
 lean_dec_ref(x_107);
 x_110 = lean_box(0);
}
lean_ctor_set(x_14, 0, x_103);
x_111 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_112 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
lean_dec(x_6);
x_113 = lean_box(0);
x_114 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_114, 0, x_7);
lean_ctor_set(x_114, 1, x_5);
lean_ctor_set(x_114, 2, x_108);
lean_ctor_set(x_114, 3, x_96);
lean_ctor_set(x_114, 4, x_14);
lean_ctor_set(x_114, 5, x_113);
lean_ctor_set_uint8(x_114, sizeof(void*)*6, x_112);
lean_ctor_set_uint8(x_114, sizeof(void*)*6 + 1, x_111);
x_115 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_114);
if (lean_is_scalar(x_110)) {
 x_116 = lean_alloc_ctor(0, 2, 0);
} else {
 x_116 = x_110;
}
lean_ctor_set(x_116, 0, x_115);
lean_ctor_set(x_116, 1, x_109);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_103);
lean_dec(x_96);
lean_free_object(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_117 = lean_ctor_get(x_107, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_107, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_107)) {
 lean_ctor_release(x_107, 0);
 lean_ctor_release(x_107, 1);
 x_119 = x_107;
} else {
 lean_dec_ref(x_107);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
lean_dec(x_103);
lean_dec(x_96);
lean_free_object(x_14);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_121 = lean_ctor_get(x_104, 0);
lean_inc(x_121);
x_122 = lean_ctor_get(x_104, 1);
lean_inc(x_122);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_123 = x_104;
} else {
 lean_dec_ref(x_104);
 x_123 = lean_box(0);
}
if (lean_is_scalar(x_123)) {
 x_124 = lean_alloc_ctor(1, 2, 0);
} else {
 x_124 = x_123;
}
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_122);
return x_124;
}
}
}
else
{
lean_object* x_125; size_t x_126; lean_object* x_127; size_t x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; size_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; size_t x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_125 = lean_ctor_get(x_14, 0);
lean_inc(x_125);
lean_dec(x_14);
x_126 = lean_array_size(x_3);
x_127 = lean_unsigned_to_nat(0u);
x_128 = lean_usize_of_nat(x_127);
x_129 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_126, x_128, x_3, x_8, x_9, x_10, x_11, x_12, x_13);
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
x_132 = lean_array_size(x_4);
x_133 = l_Array_mapMUnsafe_map___at_____private_Lean_Compiler_LCNF_Simp_JpCases_0__Lean_Compiler_LCNF_Simp_mkJpAlt_go_spec__2(x_132, x_128, x_4, x_8, x_9, x_10, x_11, x_12, x_131);
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_136 = x_133;
} else {
 lean_dec_ref(x_133);
 x_136 = lean_box(0);
}
x_137 = lean_array_get_size(x_2);
lean_inc(x_137);
x_138 = l_Array_toSubarray___redArg(x_2, x_127, x_137);
x_139 = lean_ctor_get(x_6, 3);
lean_inc(x_139);
if (lean_is_scalar(x_136)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_136;
}
lean_ctor_set(x_140, 0, x_138);
lean_ctor_set(x_140, 1, x_130);
x_141 = lean_array_size(x_139);
lean_inc(x_1);
lean_inc(x_6);
x_142 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0(x_6, x_1, x_139, x_141, x_128, x_140, x_8, x_9, x_10, x_11, x_12, x_135);
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = lean_array_get_size(x_139);
x_147 = l_Array_toSubarray___redArg(x_139, x_137, x_146);
x_148 = lean_ctor_get(x_147, 2);
lean_inc(x_148);
x_149 = lean_usize_of_nat(x_148);
lean_dec(x_148);
x_150 = lean_ctor_get(x_147, 1);
lean_inc(x_150);
x_151 = lean_usize_of_nat(x_150);
lean_dec(x_150);
lean_inc(x_1);
lean_inc(x_6);
x_152 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1(x_6, x_1, x_147, x_149, x_151, x_145, x_8, x_9, x_10, x_11, x_12, x_144);
lean_dec(x_147);
x_153 = lean_ctor_get(x_152, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_152, 1);
lean_inc(x_154);
lean_dec(x_152);
x_155 = lean_ctor_get(x_6, 1);
lean_inc(x_155);
x_156 = l_Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode(x_155, x_1, x_125);
x_157 = l_Lean_Compiler_LCNF_Internalize_internalizeCode(x_156, x_8, x_9, x_10, x_11, x_12, x_154);
lean_dec(x_8);
x_158 = lean_ctor_get(x_157, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_157, 1);
lean_inc(x_159);
lean_dec(x_157);
x_160 = l_Lean_Compiler_LCNF_attachCodeDecls(x_134, x_158);
lean_dec(x_134);
lean_inc(x_160);
x_161 = l_Lean_Compiler_LCNF_Code_inferType(x_160, x_9, x_10, x_11, x_12, x_159);
if (lean_obj_tag(x_161) == 0)
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_161, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_161, 1);
lean_inc(x_163);
lean_dec(x_161);
lean_inc(x_153);
x_164 = l_Lean_Compiler_LCNF_mkForallParams(x_153, x_162, x_9, x_10, x_11, x_12, x_163);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_162);
if (lean_obj_tag(x_164) == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; uint8_t x_169; uint8_t x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_165 = lean_ctor_get(x_164, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_164, 1);
lean_inc(x_166);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_167 = x_164;
} else {
 lean_dec_ref(x_164);
 x_167 = lean_box(0);
}
x_168 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_168, 0, x_160);
x_169 = lean_ctor_get_uint8(x_6, sizeof(void*)*6 + 1);
x_170 = lean_ctor_get_uint8(x_6, sizeof(void*)*6);
lean_dec(x_6);
x_171 = lean_box(0);
x_172 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_172, 0, x_7);
lean_ctor_set(x_172, 1, x_5);
lean_ctor_set(x_172, 2, x_165);
lean_ctor_set(x_172, 3, x_153);
lean_ctor_set(x_172, 4, x_168);
lean_ctor_set(x_172, 5, x_171);
lean_ctor_set_uint8(x_172, sizeof(void*)*6, x_170);
lean_ctor_set_uint8(x_172, sizeof(void*)*6 + 1, x_169);
x_173 = l_Lean_Compiler_LCNF_Decl_setLevelParams(x_172);
if (lean_is_scalar(x_167)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_167;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_166);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_160);
lean_dec(x_153);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_175 = lean_ctor_get(x_164, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_164, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_164)) {
 lean_ctor_release(x_164, 0);
 lean_ctor_release(x_164, 1);
 x_177 = x_164;
} else {
 lean_dec_ref(x_164);
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
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; 
lean_dec(x_160);
lean_dec(x_153);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_179 = lean_ctor_get(x_161, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_161, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_181 = x_161;
} else {
 lean_dec_ref(x_161);
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
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_14);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize", 29, 29);
x_184 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize.mkSpecDecl.go", 43, 43);
x_185 = lean_unsigned_to_nat(228u);
x_186 = lean_unsigned_to_nat(35u);
x_187 = lean_mk_string_unchecked("can only specialize decls with code", 35, 35);
x_188 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_183, x_184, x_185, x_186, x_187);
lean_dec(x_187);
lean_dec(x_184);
lean_dec(x_183);
x_189 = l_panic___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__2(x_188, x_8, x_9, x_10, x_11, x_12, x_13);
return x_189;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__0(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Specialize_mkSpecDecl_go_spec__1(x_1, x_2, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_8, x_13);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_1, 0);
lean_inc(x_18);
x_19 = lean_mk_string_unchecked("_at_", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = l_Lean_Name_appendCore(x_18, x_20);
lean_dec(x_18);
x_22 = lean_ctor_get(x_7, 2);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_mk_string_unchecked("spec", 4, 4);
x_24 = lean_unsigned_to_nat(8u);
x_25 = lean_unsigned_to_nat(0u);
x_26 = lean_unsigned_to_nat(2u);
x_27 = lean_nat_shiftl(x_24, x_26);
x_28 = lean_unsigned_to_nat(3u);
x_29 = lean_nat_div(x_27, x_28);
lean_dec(x_27);
x_30 = l_Nat_nextPowerOfTwo(x_29);
lean_dec(x_29);
x_31 = lean_box(0);
x_32 = lean_mk_array(x_30, x_31);
lean_ctor_set(x_14, 1, x_32);
lean_ctor_set(x_14, 0, x_25);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_14);
x_33 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_14, x_9, x_10, x_11, x_12, x_17);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_mk_ref(x_14, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = l_Lean_Name_appendCore(x_21, x_22);
lean_dec(x_21);
x_40 = l_Lean_Name_mkStr1(x_23);
x_41 = l_Lean_Name_appendCore(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_16);
lean_dec(x_16);
x_43 = lean_name_append_index_after(x_41, x_42);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_37);
lean_inc(x_34);
x_44 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(x_2, x_3, x_4, x_5, x_6, x_34, x_43, x_37, x_9, x_10, x_11, x_12, x_38);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = lean_st_ref_get(x_37, x_46);
lean_dec(x_37);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
lean_dec(x_47);
x_49 = l_Lean_Compiler_LCNF_eraseDecl(x_34, x_9, x_10, x_11, x_12, x_48);
if (lean_obj_tag(x_49) == 0)
{
uint8_t x_50; 
x_50 = !lean_is_exclusive(x_49);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_49, 0);
lean_dec(x_51);
lean_ctor_set(x_49, 0, x_45);
return x_49;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
uint8_t x_54; 
lean_dec(x_45);
x_54 = !lean_is_exclusive(x_49);
if (x_54 == 0)
{
return x_49;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_49, 0);
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_inc(x_55);
lean_dec(x_49);
x_57 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_56);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
lean_dec(x_37);
x_58 = lean_ctor_get(x_44, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_44, 1);
lean_inc(x_59);
lean_dec(x_44);
x_60 = l_Lean_Compiler_LCNF_eraseDecl(x_34, x_9, x_10, x_11, x_12, x_59);
if (lean_obj_tag(x_60) == 0)
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_58);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_58);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
else
{
uint8_t x_65; 
lean_dec(x_58);
x_65 = !lean_is_exclusive(x_60);
if (x_65 == 0)
{
return x_60;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_60, 0);
x_67 = lean_ctor_get(x_60, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_60);
x_68 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
return x_68;
}
}
}
}
else
{
lean_dec(x_14);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_33;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_69 = lean_ctor_get(x_14, 0);
x_70 = lean_ctor_get(x_14, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_14);
x_71 = lean_ctor_get(x_1, 0);
lean_inc(x_71);
x_72 = lean_mk_string_unchecked("_at_", 4, 4);
x_73 = l_Lean_Name_mkStr1(x_72);
x_74 = l_Lean_Name_appendCore(x_71, x_73);
lean_dec(x_71);
x_75 = lean_ctor_get(x_7, 2);
lean_inc(x_75);
lean_dec(x_7);
x_76 = lean_mk_string_unchecked("spec", 4, 4);
x_77 = lean_unsigned_to_nat(8u);
x_78 = lean_unsigned_to_nat(0u);
x_79 = lean_unsigned_to_nat(2u);
x_80 = lean_nat_shiftl(x_77, x_79);
x_81 = lean_unsigned_to_nat(3u);
x_82 = lean_nat_div(x_80, x_81);
lean_dec(x_80);
x_83 = l_Nat_nextPowerOfTwo(x_82);
lean_dec(x_82);
x_84 = lean_box(0);
x_85 = lean_mk_array(x_83, x_84);
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_85);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_86);
x_87 = l_Lean_Compiler_LCNF_Decl_internalize(x_1, x_86, x_9, x_10, x_11, x_12, x_70);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = lean_st_mk_ref(x_86, x_89);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = l_Lean_Name_appendCore(x_74, x_75);
lean_dec(x_74);
x_94 = l_Lean_Name_mkStr1(x_76);
x_95 = l_Lean_Name_appendCore(x_93, x_94);
lean_dec(x_93);
x_96 = lean_array_get_size(x_69);
lean_dec(x_69);
x_97 = lean_name_append_index_after(x_95, x_96);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_91);
lean_inc(x_88);
x_98 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl_go(x_2, x_3, x_4, x_5, x_6, x_88, x_97, x_91, x_9, x_10, x_11, x_12, x_92);
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_st_ref_get(x_91, x_100);
lean_dec(x_91);
x_102 = lean_ctor_get(x_101, 1);
lean_inc(x_102);
lean_dec(x_101);
x_103 = l_Lean_Compiler_LCNF_eraseDecl(x_88, x_9, x_10, x_11, x_12, x_102);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_105 = x_103;
} else {
 lean_dec_ref(x_103);
 x_105 = lean_box(0);
}
if (lean_is_scalar(x_105)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_105;
}
lean_ctor_set(x_106, 0, x_99);
lean_ctor_set(x_106, 1, x_104);
return x_106;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_99);
x_107 = lean_ctor_get(x_103, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_103, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_109 = x_103;
} else {
 lean_dec_ref(x_103);
 x_109 = lean_box(0);
}
if (lean_is_scalar(x_109)) {
 x_110 = lean_alloc_ctor(1, 2, 0);
} else {
 x_110 = x_109;
}
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_108);
return x_110;
}
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
lean_dec(x_91);
x_111 = lean_ctor_get(x_98, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_98, 1);
lean_inc(x_112);
lean_dec(x_98);
x_113 = l_Lean_Compiler_LCNF_eraseDecl(x_88, x_9, x_10, x_11, x_12, x_112);
if (lean_obj_tag(x_113) == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_113, 1);
lean_inc(x_114);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_115 = x_113;
} else {
 lean_dec_ref(x_113);
 x_115 = lean_box(0);
}
if (lean_is_scalar(x_115)) {
 x_116 = lean_alloc_ctor(1, 2, 0);
} else {
 x_116 = x_115;
 lean_ctor_set_tag(x_116, 1);
}
lean_ctor_set(x_116, 0, x_111);
lean_ctor_set(x_116, 1, x_114);
return x_116;
}
else
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
lean_dec(x_111);
x_117 = lean_ctor_get(x_113, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_113, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_113)) {
 lean_ctor_release(x_113, 0);
 lean_ctor_release(x_113, 1);
 x_119 = x_113;
} else {
 lean_dec_ref(x_113);
 x_119 = lean_box(0);
}
if (lean_is_scalar(x_119)) {
 x_120 = lean_alloc_ctor(1, 2, 0);
} else {
 x_120 = x_119;
}
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_118);
return x_120;
}
}
}
else
{
lean_dec(x_86);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_74);
lean_dec(x_69);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_mkSpecDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_getRemainingArgs_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
return x_4;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_4, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_4, 1);
lean_inc(x_13);
lean_dec(x_4);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_12, 2);
lean_inc(x_15);
x_16 = lean_nat_dec_lt(x_14, x_15);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_15);
lean_dec(x_14);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_12);
lean_ctor_set(x_17, 1, x_13);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_array_uget(x_1, x_3);
x_19 = lean_unbox(x_18);
lean_dec(x_18);
x_20 = lean_ctor_get(x_12, 0);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_14, x_21);
lean_inc(x_20);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
lean_ctor_set(x_23, 2, x_15);
x_24 = lean_box(x_19);
if (lean_obj_tag(x_24) == 4)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_array_fget(x_20, x_14);
lean_dec(x_14);
lean_dec(x_20);
x_26 = lean_array_push(x_13, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_5 = x_27;
goto block_10;
}
else
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_20);
lean_dec(x_14);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_23);
lean_ctor_set(x_28, 1, x_13);
x_5 = x_28;
goto block_10;
}
}
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_3, x_7);
x_3 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_mk_empty_array_with_capacity(x_3);
x_5 = lean_array_get_size(x_2);
lean_inc(x_5);
lean_inc(x_2);
x_6 = l_Array_toSubarray___redArg(x_2, x_3, x_5);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_4);
x_8 = lean_array_size(x_1);
x_9 = lean_usize_of_nat(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_getRemainingArgs_spec__0(x_1, x_8, x_9, x_7);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_array_get_size(x_1);
x_13 = l_Array_toSubarray___redArg(x_2, x_12, x_5);
x_14 = l_Array_ofSubarray___redArg(x_13);
lean_dec(x_13);
x_15 = l_Array_append(lean_box(0), x_11, x_14);
lean_dec(x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_getRemainingArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Specialize_getRemainingArgs_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_getRemainingArgs___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_FVarIdSet_insert(x_4, x_7);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_paramsToVarSet(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_2 = lean_box(0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
uint8_t x_6; 
x_6 = lean_nat_dec_le(x_4, x_4);
if (x_6 == 0)
{
lean_dec(x_4);
return x_2;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
x_8 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_9 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_1, x_7, x_8, x_2);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_paramsToVarSet___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_Specialize_paramsToVarSet(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_Compiler_LCNF_getSpecParamInfoCore_x3f(x_7, x_1);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_ctor_get(x_4, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_4);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Compiler_LCNF_getSpecParamInfoCore_x3f(x_11, x_1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___redArg(x_1, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_2, x_3);
if (x_11 == 0)
{
lean_object* x_12; 
x_12 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_12) == 0)
{
x_5 = x_4;
goto block_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_array_push(x_4, x_13);
x_5 = x_14;
goto block_10;
}
}
else
{
return x_4;
}
block_10:
{
lean_object* x_6; size_t x_7; size_t x_8; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_usize_of_nat(x_6);
x_8 = lean_usize_add(x_2, x_7);
x_2 = x_8;
x_4 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_mk_empty_array_with_capacity(x_4);
x_6 = lean_nat_dec_lt(x_2, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_1);
x_8 = lean_nat_dec_le(x_3, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_usize_of_nat(x_2);
x_10 = lean_usize_of_nat(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1_spec__1(x_1, x_9, x_10, x_5);
return x_11;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_apply_8(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_12, 0);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set(x_12, 0, x_2);
return x_12;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_12, 0);
x_16 = lean_ctor_get(x_12, 1);
lean_inc(x_16);
lean_inc(x_15);
lean_dec(x_12);
lean_ctor_set(x_2, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_2);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
else
{
uint8_t x_18; 
lean_free_object(x_2);
x_18 = !lean_is_exclusive(x_12);
if (x_18 == 0)
{
return x_12;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_12, 0);
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_12);
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
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
lean_dec(x_2);
x_23 = lean_apply_8(x_1, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_26 = x_23;
} else {
 lean_dec_ref(x_23);
 x_26 = lean_box(0);
}
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_24);
if (lean_is_scalar(x_26)) {
 x_28 = lean_alloc_ctor(0, 2, 0);
} else {
 x_28 = x_26;
}
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_25);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_23, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_23)) {
 lean_ctor_release(x_23, 0);
 lean_ctor_release(x_23, 1);
 x_31 = x_23;
} else {
 lean_dec_ref(x_23);
 x_31 = lean_box(0);
}
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(1, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
return x_32;
}
}
}
else
{
lean_object* x_33; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_1, x_6, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_10, 1);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_4, 2);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_19);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_inc(x_19);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_19);
lean_inc(x_19);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_19);
lean_inc(x_19);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_19);
lean_inc(x_19);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_19);
x_25 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_25, 0, x_19);
x_26 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_18);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set(x_26, 6, x_23);
lean_ctor_set(x_26, 7, x_24);
lean_ctor_set(x_26, 8, x_25);
x_27 = lean_st_ref_take(x_5, x_13);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint64_t x_37; lean_object* x_38; double x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_17);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_26);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
x_32 = lean_ctor_get(x_4, 5);
lean_ctor_set_tag(x_27, 3);
lean_ctor_set(x_27, 1, x_2);
lean_ctor_set(x_27, 0, x_31);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_29, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_29, 2);
lean_inc(x_35);
x_36 = lean_ctor_get(x_29, 3);
lean_inc(x_36);
x_37 = lean_ctor_get_uint64(x_36, sizeof(void*)*1);
x_38 = lean_ctor_get(x_36, 0);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_float_of_nat(x_18);
x_40 = lean_box(0);
x_41 = lean_mk_string_unchecked("", 0, 0);
x_42 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_float(x_42, sizeof(void*)*2, x_39);
lean_ctor_set_float(x_42, sizeof(void*)*2 + 8, x_39);
x_43 = lean_unbox(x_40);
lean_ctor_set_uint8(x_42, sizeof(void*)*2 + 16, x_43);
x_44 = lean_mk_empty_array_with_capacity(x_18);
x_45 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_27);
lean_ctor_set(x_45, 2, x_44);
lean_inc(x_32);
lean_ctor_set(x_10, 1, x_45);
lean_ctor_set(x_10, 0, x_32);
x_46 = l_Lean_PersistentArray_push___redArg(x_38, x_10);
x_47 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set_uint64(x_47, sizeof(void*)*1, x_37);
x_48 = lean_ctor_get(x_29, 4);
lean_inc(x_48);
x_49 = lean_ctor_get(x_29, 5);
lean_inc(x_49);
x_50 = lean_ctor_get(x_29, 6);
lean_inc(x_50);
x_51 = lean_ctor_get(x_29, 7);
lean_inc(x_51);
lean_dec(x_29);
x_52 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_52, 0, x_33);
lean_ctor_set(x_52, 1, x_34);
lean_ctor_set(x_52, 2, x_35);
lean_ctor_set(x_52, 3, x_47);
lean_ctor_set(x_52, 4, x_48);
lean_ctor_set(x_52, 5, x_49);
lean_ctor_set(x_52, 6, x_50);
lean_ctor_set(x_52, 7, x_51);
x_53 = lean_st_ref_set(x_5, x_52, x_30);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_53, 0);
lean_dec(x_55);
x_56 = lean_box(0);
lean_ctor_set(x_53, 0, x_56);
return x_53;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_dec(x_53);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_57);
return x_59;
}
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint64_t x_69; lean_object* x_70; double x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_60 = lean_ctor_get(x_27, 0);
x_61 = lean_ctor_get(x_27, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_27);
lean_inc(x_17);
x_62 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_62, 0, x_14);
lean_ctor_set(x_62, 1, x_26);
lean_ctor_set(x_62, 2, x_16);
lean_ctor_set(x_62, 3, x_17);
x_63 = lean_ctor_get(x_4, 5);
x_64 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_2);
x_65 = lean_ctor_get(x_60, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_60, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_60, 2);
lean_inc(x_67);
x_68 = lean_ctor_get(x_60, 3);
lean_inc(x_68);
x_69 = lean_ctor_get_uint64(x_68, sizeof(void*)*1);
x_70 = lean_ctor_get(x_68, 0);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_float_of_nat(x_18);
x_72 = lean_box(0);
x_73 = lean_mk_string_unchecked("", 0, 0);
x_74 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_74, 0, x_1);
lean_ctor_set(x_74, 1, x_73);
lean_ctor_set_float(x_74, sizeof(void*)*2, x_71);
lean_ctor_set_float(x_74, sizeof(void*)*2 + 8, x_71);
x_75 = lean_unbox(x_72);
lean_ctor_set_uint8(x_74, sizeof(void*)*2 + 16, x_75);
x_76 = lean_mk_empty_array_with_capacity(x_18);
x_77 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_77, 0, x_74);
lean_ctor_set(x_77, 1, x_64);
lean_ctor_set(x_77, 2, x_76);
lean_inc(x_63);
lean_ctor_set(x_10, 1, x_77);
lean_ctor_set(x_10, 0, x_63);
x_78 = l_Lean_PersistentArray_push___redArg(x_70, x_10);
x_79 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set_uint64(x_79, sizeof(void*)*1, x_69);
x_80 = lean_ctor_get(x_60, 4);
lean_inc(x_80);
x_81 = lean_ctor_get(x_60, 5);
lean_inc(x_81);
x_82 = lean_ctor_get(x_60, 6);
lean_inc(x_82);
x_83 = lean_ctor_get(x_60, 7);
lean_inc(x_83);
lean_dec(x_60);
x_84 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_84, 0, x_65);
lean_ctor_set(x_84, 1, x_66);
lean_ctor_set(x_84, 2, x_67);
lean_ctor_set(x_84, 3, x_79);
lean_ctor_set(x_84, 4, x_80);
lean_ctor_set(x_84, 5, x_81);
lean_ctor_set(x_84, 6, x_82);
lean_ctor_set(x_84, 7, x_83);
x_85 = lean_st_ref_set(x_5, x_84, x_61);
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_85)) {
 lean_ctor_release(x_85, 0);
 lean_ctor_release(x_85, 1);
 x_87 = x_85;
} else {
 lean_dec_ref(x_85);
 x_87 = lean_box(0);
}
x_88 = lean_box(0);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; uint64_t x_116; lean_object* x_117; double x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
x_90 = lean_ctor_get(x_10, 0);
x_91 = lean_ctor_get(x_10, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_10);
x_92 = lean_ctor_get(x_8, 0);
lean_inc(x_92);
lean_dec(x_8);
x_93 = lean_ctor_get(x_90, 0);
lean_inc(x_93);
lean_dec(x_90);
x_94 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_93);
lean_dec(x_93);
x_95 = lean_ctor_get(x_4, 2);
x_96 = lean_unsigned_to_nat(0u);
x_97 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_97);
x_98 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_98, 0, x_97);
lean_inc(x_97);
x_99 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_99, 0, x_97);
lean_inc(x_97);
x_100 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_100, 0, x_97);
lean_inc(x_97);
x_101 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_101, 0, x_97);
lean_inc(x_97);
x_102 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_102, 0, x_97);
x_103 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_103, 0, x_97);
x_104 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_104, 0, x_96);
lean_ctor_set(x_104, 1, x_96);
lean_ctor_set(x_104, 2, x_96);
lean_ctor_set(x_104, 3, x_98);
lean_ctor_set(x_104, 4, x_99);
lean_ctor_set(x_104, 5, x_100);
lean_ctor_set(x_104, 6, x_101);
lean_ctor_set(x_104, 7, x_102);
lean_ctor_set(x_104, 8, x_103);
x_105 = lean_st_ref_take(x_5, x_91);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_108 = x_105;
} else {
 lean_dec_ref(x_105);
 x_108 = lean_box(0);
}
lean_inc(x_95);
x_109 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_109, 0, x_92);
lean_ctor_set(x_109, 1, x_104);
lean_ctor_set(x_109, 2, x_94);
lean_ctor_set(x_109, 3, x_95);
x_110 = lean_ctor_get(x_4, 5);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(3, 2, 0);
} else {
 x_111 = x_108;
 lean_ctor_set_tag(x_111, 3);
}
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_2);
x_112 = lean_ctor_get(x_106, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_106, 1);
lean_inc(x_113);
x_114 = lean_ctor_get(x_106, 2);
lean_inc(x_114);
x_115 = lean_ctor_get(x_106, 3);
lean_inc(x_115);
x_116 = lean_ctor_get_uint64(x_115, sizeof(void*)*1);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
lean_dec(x_115);
x_118 = lean_float_of_nat(x_96);
x_119 = lean_box(0);
x_120 = lean_mk_string_unchecked("", 0, 0);
x_121 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_121, 0, x_1);
lean_ctor_set(x_121, 1, x_120);
lean_ctor_set_float(x_121, sizeof(void*)*2, x_118);
lean_ctor_set_float(x_121, sizeof(void*)*2 + 8, x_118);
x_122 = lean_unbox(x_119);
lean_ctor_set_uint8(x_121, sizeof(void*)*2 + 16, x_122);
x_123 = lean_mk_empty_array_with_capacity(x_96);
x_124 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_111);
lean_ctor_set(x_124, 2, x_123);
lean_inc(x_110);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_110);
lean_ctor_set(x_125, 1, x_124);
x_126 = l_Lean_PersistentArray_push___redArg(x_117, x_125);
x_127 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set_uint64(x_127, sizeof(void*)*1, x_116);
x_128 = lean_ctor_get(x_106, 4);
lean_inc(x_128);
x_129 = lean_ctor_get(x_106, 5);
lean_inc(x_129);
x_130 = lean_ctor_get(x_106, 6);
lean_inc(x_130);
x_131 = lean_ctor_get(x_106, 7);
lean_inc(x_131);
lean_dec(x_106);
x_132 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_132, 0, x_112);
lean_ctor_set(x_132, 1, x_113);
lean_ctor_set(x_132, 2, x_114);
lean_ctor_set(x_132, 3, x_127);
lean_ctor_set(x_132, 4, x_128);
lean_ctor_set(x_132, 5, x_129);
lean_ctor_set(x_132, 6, x_130);
lean_ctor_set(x_132, 7, x_131);
x_133 = lean_st_ref_set(x_5, x_132, x_107);
x_134 = lean_ctor_get(x_133, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_135 = x_133;
} else {
 lean_dec_ref(x_133);
 x_135 = lean_box(0);
}
x_136 = lean_box(0);
if (lean_is_scalar(x_135)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_135;
}
lean_ctor_set(x_137, 0, x_136);
lean_ctor_set(x_137, 1, x_134);
return x_137;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_1, x_2, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_9 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
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
x_48 = lean_alloc_closure((void*)(l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6___lam__0___boxed), 2, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_panic_fn(x_48, x_1);
x_50 = lean_apply_7(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_50;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
if (lean_obj_tag(x_1) == 3)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_60 = lean_ctor_get(x_1, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_1, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_1, 2);
lean_inc(x_62);
x_63 = l_Array_isEmpty___redArg(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = l_Lean_Meta_isInstance___redArg(x_60, x_7, x_8);
x_65 = lean_ctor_get(x_64, 0);
lean_inc(x_65);
x_66 = lean_unbox(x_65);
if (x_66 == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
lean_inc(x_60);
x_68 = l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___redArg(x_60, x_7, x_67);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_70 = !lean_is_exclusive(x_68);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_ctor_get(x_68, 0);
lean_dec(x_71);
x_72 = lean_box(0);
lean_ctor_set(x_68, 0, x_72);
return x_68;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_68, 1);
lean_inc(x_73);
lean_dec(x_68);
x_74 = lean_box(0);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_73);
return x_75;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; 
x_76 = lean_ctor_get(x_68, 1);
lean_inc(x_76);
lean_dec(x_68);
x_77 = lean_ctor_get(x_69, 0);
lean_inc(x_77);
lean_dec(x_69);
lean_inc(x_2);
lean_inc(x_62);
x_78 = l_Lean_Compiler_LCNF_Specialize_shouldSpecialize(x_77, x_62, x_2, x_3, x_4, x_5, x_6, x_7, x_76);
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; size_t x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_144; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = lean_ctor_get(x_78, 1);
x_144 = lean_unbox(x_80);
if (x_144 == 0)
{
lean_object* x_145; 
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_145 = lean_box(0);
lean_ctor_set(x_78, 0, x_145);
return x_78;
}
else
{
lean_object* x_146; lean_object* x_147; 
lean_free_object(x_78);
lean_inc(x_60);
x_146 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_60, x_4, x_7, x_81);
x_147 = lean_ctor_get(x_146, 0);
lean_inc(x_147);
if (lean_obj_tag(x_147) == 0)
{
uint8_t x_148; 
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_148 = !lean_is_exclusive(x_146);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; 
x_149 = lean_ctor_get(x_146, 0);
lean_dec(x_149);
x_150 = lean_box(0);
lean_ctor_set(x_146, 0, x_150);
return x_146;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_146, 1);
lean_inc(x_151);
lean_dec(x_146);
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_147, 0);
lean_inc(x_154);
lean_dec(x_147);
x_155 = lean_ctor_get(x_154, 4);
lean_inc(x_155);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
lean_dec(x_155);
x_156 = lean_ctor_get(x_146, 1);
lean_inc(x_156);
lean_dec(x_146);
x_157 = lean_mk_string_unchecked("Compiler", 8, 8);
x_158 = lean_mk_string_unchecked("specialize", 10, 10);
x_312 = lean_mk_string_unchecked("candidate", 9, 9);
lean_inc(x_158);
lean_inc(x_157);
x_313 = l_Lean_Name_mkStr3(x_157, x_158, x_312);
lean_inc(x_313);
x_383 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_313, x_6, x_156);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_unbox(x_384);
lean_dec(x_384);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_1);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_314 = x_2;
x_315 = x_3;
x_316 = x_4;
x_317 = x_5;
x_318 = x_6;
x_319 = x_7;
x_320 = x_386;
goto block_382;
}
else
{
uint8_t x_387; 
x_387 = !lean_is_exclusive(x_383);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; 
x_388 = lean_ctor_get(x_383, 1);
x_389 = lean_ctor_get(x_383, 0);
lean_dec(x_389);
x_390 = lean_mk_string_unchecked("", 0, 0);
x_391 = l_Lean_stringToMessageData(x_390);
lean_dec(x_390);
x_392 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_1);
x_393 = l_Lean_MessageData_ofExpr(x_392);
lean_inc(x_391);
lean_ctor_set_tag(x_383, 7);
lean_ctor_set(x_383, 1, x_393);
lean_ctor_set(x_383, 0, x_391);
x_394 = lean_mk_string_unchecked(", ", 2, 2);
x_395 = l_Lean_stringToMessageData(x_394);
lean_dec(x_394);
x_396 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_396, 0, x_383);
lean_ctor_set(x_396, 1, x_395);
lean_inc(x_77);
x_397 = lean_array_to_list(x_77);
x_398 = lean_box(0);
x_399 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_saveSpecParamInfo_spec__13(x_397, x_398);
x_400 = l_Lean_MessageData_ofList(x_399);
x_401 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_401, 0, x_396);
lean_ctor_set(x_401, 1, x_400);
x_402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_391);
lean_inc(x_313);
x_403 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_313, x_402, x_5, x_6, x_7, x_388);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
lean_dec(x_403);
x_314 = x_2;
x_315 = x_3;
x_316 = x_4;
x_317 = x_5;
x_318 = x_6;
x_319 = x_7;
x_320 = x_404;
goto block_382;
}
else
{
lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_405 = lean_ctor_get(x_383, 1);
lean_inc(x_405);
lean_dec(x_383);
x_406 = lean_mk_string_unchecked("", 0, 0);
x_407 = l_Lean_stringToMessageData(x_406);
lean_dec(x_406);
x_408 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_1);
x_409 = l_Lean_MessageData_ofExpr(x_408);
lean_inc(x_407);
x_410 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_410, 0, x_407);
lean_ctor_set(x_410, 1, x_409);
x_411 = lean_mk_string_unchecked(", ", 2, 2);
x_412 = l_Lean_stringToMessageData(x_411);
lean_dec(x_411);
x_413 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_412);
lean_inc(x_77);
x_414 = lean_array_to_list(x_77);
x_415 = lean_box(0);
x_416 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_saveSpecParamInfo_spec__13(x_414, x_415);
x_417 = l_Lean_MessageData_ofList(x_416);
x_418 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_418, 0, x_413);
lean_ctor_set(x_418, 1, x_417);
x_419 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_419, 0, x_418);
lean_ctor_set(x_419, 1, x_407);
lean_inc(x_313);
x_420 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_313, x_419, x_5, x_6, x_7, x_405);
x_421 = lean_ctor_get(x_420, 1);
lean_inc(x_421);
lean_dec(x_420);
x_314 = x_2;
x_315 = x_3;
x_316 = x_4;
x_317 = x_5;
x_318 = x_6;
x_319 = x_7;
x_320 = x_421;
goto block_382;
}
}
block_311:
{
uint8_t x_172; 
x_172 = l_Lean_Expr_hasLooseBVars(x_162);
if (x_172 == 0)
{
uint8_t x_173; 
x_173 = l_Lean_Expr_hasFVar(x_162);
if (x_173 == 0)
{
lean_object* x_174; uint8_t x_175; 
x_174 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg(x_162, x_170, x_171);
x_175 = !lean_is_exclusive(x_174);
if (x_175 == 0)
{
lean_object* x_176; lean_object* x_177; size_t x_178; lean_object* x_179; size_t x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_176 = lean_ctor_get(x_174, 0);
x_177 = lean_ctor_get(x_174, 1);
x_178 = lean_array_size(x_159);
x_179 = lean_box(0);
x_180 = lean_usize_of_nat(x_160);
lean_inc(x_159);
x_181 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_178, x_180, x_159);
x_182 = l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(x_77, x_62);
lean_dec(x_77);
lean_inc(x_164);
x_183 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(x_164, x_179);
x_184 = l_Array_append(lean_box(0), x_181, x_182);
lean_dec(x_182);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_185; 
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
x_185 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_154, x_61, x_161, x_159, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_170, x_177);
if (lean_obj_tag(x_185) == 0)
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
x_188 = lean_mk_string_unchecked("step", 4, 4);
x_189 = l_Lean_Name_mkStr3(x_157, x_158, x_188);
lean_inc(x_189);
x_190 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_189, x_169, x_187);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_unbox(x_191);
lean_dec(x_191);
if (x_192 == 0)
{
lean_object* x_193; 
lean_dec(x_189);
lean_free_object(x_174);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_dec(x_190);
x_82 = x_160;
x_83 = x_186;
x_84 = x_162;
x_85 = x_184;
x_86 = x_183;
x_87 = x_180;
x_88 = x_166;
x_89 = x_167;
x_90 = x_168;
x_91 = x_169;
x_92 = x_170;
x_93 = x_193;
goto block_143;
}
else
{
uint8_t x_194; 
x_194 = !lean_is_exclusive(x_190);
if (x_194 == 0)
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_195 = lean_ctor_get(x_190, 1);
x_196 = lean_ctor_get(x_190, 0);
lean_dec(x_196);
x_197 = lean_mk_string_unchecked("new: ", 5, 5);
x_198 = l_Lean_stringToMessageData(x_197);
lean_dec(x_197);
x_199 = lean_ctor_get(x_186, 0);
lean_inc(x_199);
x_200 = l_Lean_MessageData_ofName(x_199);
lean_ctor_set_tag(x_190, 7);
lean_ctor_set(x_190, 1, x_200);
lean_ctor_set(x_190, 0, x_198);
x_201 = lean_mk_string_unchecked("", 0, 0);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
lean_ctor_set_tag(x_174, 7);
lean_ctor_set(x_174, 1, x_202);
lean_ctor_set(x_174, 0, x_190);
x_203 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_189, x_174, x_168, x_169, x_170, x_195);
x_204 = lean_ctor_get(x_203, 1);
lean_inc(x_204);
lean_dec(x_203);
x_82 = x_160;
x_83 = x_186;
x_84 = x_162;
x_85 = x_184;
x_86 = x_183;
x_87 = x_180;
x_88 = x_166;
x_89 = x_167;
x_90 = x_168;
x_91 = x_169;
x_92 = x_170;
x_93 = x_204;
goto block_143;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_205 = lean_ctor_get(x_190, 1);
lean_inc(x_205);
lean_dec(x_190);
x_206 = lean_mk_string_unchecked("new: ", 5, 5);
x_207 = l_Lean_stringToMessageData(x_206);
lean_dec(x_206);
x_208 = lean_ctor_get(x_186, 0);
lean_inc(x_208);
x_209 = l_Lean_MessageData_ofName(x_208);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("", 0, 0);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
lean_ctor_set_tag(x_174, 7);
lean_ctor_set(x_174, 1, x_212);
lean_ctor_set(x_174, 0, x_210);
x_213 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_189, x_174, x_168, x_169, x_170, x_205);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
x_82 = x_160;
x_83 = x_186;
x_84 = x_162;
x_85 = x_184;
x_86 = x_183;
x_87 = x_180;
x_88 = x_166;
x_89 = x_167;
x_90 = x_168;
x_91 = x_169;
x_92 = x_170;
x_93 = x_214;
goto block_143;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_184);
lean_dec(x_183);
lean_free_object(x_174);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_80);
lean_dec(x_65);
x_215 = !lean_is_exclusive(x_185);
if (x_215 == 0)
{
return x_185;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_185, 0);
x_217 = lean_ctor_get(x_185, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_185);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_80);
lean_dec(x_65);
lean_dec(x_61);
x_219 = lean_ctor_get(x_176, 0);
lean_inc(x_219);
lean_dec(x_176);
x_220 = lean_mk_string_unchecked("step", 4, 4);
x_221 = l_Lean_Name_mkStr3(x_157, x_158, x_220);
lean_inc(x_221);
x_222 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_221, x_169, x_177);
x_223 = lean_ctor_get(x_222, 0);
lean_inc(x_223);
x_224 = lean_unbox(x_223);
lean_dec(x_223);
if (x_224 == 0)
{
lean_object* x_225; 
lean_dec(x_221);
lean_free_object(x_174);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
x_225 = lean_ctor_get(x_222, 1);
lean_inc(x_225);
lean_dec(x_222);
x_9 = x_184;
x_10 = x_219;
x_11 = x_183;
x_12 = x_225;
goto block_16;
}
else
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_222);
if (x_226 == 0)
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
x_227 = lean_ctor_get(x_222, 1);
x_228 = lean_ctor_get(x_222, 0);
lean_dec(x_228);
x_229 = lean_mk_string_unchecked("cached: ", 8, 8);
x_230 = l_Lean_stringToMessageData(x_229);
lean_dec(x_229);
lean_inc(x_219);
x_231 = l_Lean_MessageData_ofName(x_219);
lean_ctor_set_tag(x_222, 7);
lean_ctor_set(x_222, 1, x_231);
lean_ctor_set(x_222, 0, x_230);
x_232 = lean_mk_string_unchecked("", 0, 0);
x_233 = l_Lean_stringToMessageData(x_232);
lean_dec(x_232);
lean_ctor_set_tag(x_174, 7);
lean_ctor_set(x_174, 1, x_233);
lean_ctor_set(x_174, 0, x_222);
x_234 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_221, x_174, x_168, x_169, x_170, x_227);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
x_235 = lean_ctor_get(x_234, 1);
lean_inc(x_235);
lean_dec(x_234);
x_9 = x_184;
x_10 = x_219;
x_11 = x_183;
x_12 = x_235;
goto block_16;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_236 = lean_ctor_get(x_222, 1);
lean_inc(x_236);
lean_dec(x_222);
x_237 = lean_mk_string_unchecked("cached: ", 8, 8);
x_238 = l_Lean_stringToMessageData(x_237);
lean_dec(x_237);
lean_inc(x_219);
x_239 = l_Lean_MessageData_ofName(x_219);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_238);
lean_ctor_set(x_240, 1, x_239);
x_241 = lean_mk_string_unchecked("", 0, 0);
x_242 = l_Lean_stringToMessageData(x_241);
lean_dec(x_241);
lean_ctor_set_tag(x_174, 7);
lean_ctor_set(x_174, 1, x_242);
lean_ctor_set(x_174, 0, x_240);
x_243 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_221, x_174, x_168, x_169, x_170, x_236);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
x_244 = lean_ctor_get(x_243, 1);
lean_inc(x_244);
lean_dec(x_243);
x_9 = x_184;
x_10 = x_219;
x_11 = x_183;
x_12 = x_244;
goto block_16;
}
}
}
}
else
{
lean_object* x_245; lean_object* x_246; size_t x_247; lean_object* x_248; size_t x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_245 = lean_ctor_get(x_174, 0);
x_246 = lean_ctor_get(x_174, 1);
lean_inc(x_246);
lean_inc(x_245);
lean_dec(x_174);
x_247 = lean_array_size(x_159);
x_248 = lean_box(0);
x_249 = lean_usize_of_nat(x_160);
lean_inc(x_159);
x_250 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_247, x_249, x_159);
x_251 = l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(x_77, x_62);
lean_dec(x_77);
lean_inc(x_164);
x_252 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(x_164, x_248);
x_253 = l_Array_append(lean_box(0), x_250, x_251);
lean_dec(x_251);
if (lean_obj_tag(x_245) == 0)
{
lean_object* x_254; 
lean_inc(x_170);
lean_inc(x_169);
lean_inc(x_168);
lean_inc(x_167);
x_254 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_154, x_61, x_161, x_159, x_163, x_164, x_165, x_166, x_167, x_168, x_169, x_170, x_246);
if (lean_obj_tag(x_254) == 0)
{
lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; 
x_255 = lean_ctor_get(x_254, 0);
lean_inc(x_255);
x_256 = lean_ctor_get(x_254, 1);
lean_inc(x_256);
lean_dec(x_254);
x_257 = lean_mk_string_unchecked("step", 4, 4);
x_258 = l_Lean_Name_mkStr3(x_157, x_158, x_257);
lean_inc(x_258);
x_259 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_258, x_169, x_256);
x_260 = lean_ctor_get(x_259, 0);
lean_inc(x_260);
x_261 = lean_unbox(x_260);
lean_dec(x_260);
if (x_261 == 0)
{
lean_object* x_262; 
lean_dec(x_258);
x_262 = lean_ctor_get(x_259, 1);
lean_inc(x_262);
lean_dec(x_259);
x_82 = x_160;
x_83 = x_255;
x_84 = x_162;
x_85 = x_253;
x_86 = x_252;
x_87 = x_249;
x_88 = x_166;
x_89 = x_167;
x_90 = x_168;
x_91 = x_169;
x_92 = x_170;
x_93 = x_262;
goto block_143;
}
else
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_263 = lean_ctor_get(x_259, 1);
lean_inc(x_263);
if (lean_is_exclusive(x_259)) {
 lean_ctor_release(x_259, 0);
 lean_ctor_release(x_259, 1);
 x_264 = x_259;
} else {
 lean_dec_ref(x_259);
 x_264 = lean_box(0);
}
x_265 = lean_mk_string_unchecked("new: ", 5, 5);
x_266 = l_Lean_stringToMessageData(x_265);
lean_dec(x_265);
x_267 = lean_ctor_get(x_255, 0);
lean_inc(x_267);
x_268 = l_Lean_MessageData_ofName(x_267);
if (lean_is_scalar(x_264)) {
 x_269 = lean_alloc_ctor(7, 2, 0);
} else {
 x_269 = x_264;
 lean_ctor_set_tag(x_269, 7);
}
lean_ctor_set(x_269, 0, x_266);
lean_ctor_set(x_269, 1, x_268);
x_270 = lean_mk_string_unchecked("", 0, 0);
x_271 = l_Lean_stringToMessageData(x_270);
lean_dec(x_270);
x_272 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_272, 0, x_269);
lean_ctor_set(x_272, 1, x_271);
x_273 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_258, x_272, x_168, x_169, x_170, x_263);
x_274 = lean_ctor_get(x_273, 1);
lean_inc(x_274);
lean_dec(x_273);
x_82 = x_160;
x_83 = x_255;
x_84 = x_162;
x_85 = x_253;
x_86 = x_252;
x_87 = x_249;
x_88 = x_166;
x_89 = x_167;
x_90 = x_168;
x_91 = x_169;
x_92 = x_170;
x_93 = x_274;
goto block_143;
}
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
lean_dec(x_253);
lean_dec(x_252);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_162);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_80);
lean_dec(x_65);
x_275 = lean_ctor_get(x_254, 0);
lean_inc(x_275);
x_276 = lean_ctor_get(x_254, 1);
lean_inc(x_276);
if (lean_is_exclusive(x_254)) {
 lean_ctor_release(x_254, 0);
 lean_ctor_release(x_254, 1);
 x_277 = x_254;
} else {
 lean_dec_ref(x_254);
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
lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; uint8_t x_284; 
lean_dec(x_167);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_154);
lean_dec(x_80);
lean_dec(x_65);
lean_dec(x_61);
x_279 = lean_ctor_get(x_245, 0);
lean_inc(x_279);
lean_dec(x_245);
x_280 = lean_mk_string_unchecked("step", 4, 4);
x_281 = l_Lean_Name_mkStr3(x_157, x_158, x_280);
lean_inc(x_281);
x_282 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_281, x_169, x_246);
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_unbox(x_283);
lean_dec(x_283);
if (x_284 == 0)
{
lean_object* x_285; 
lean_dec(x_281);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
x_285 = lean_ctor_get(x_282, 1);
lean_inc(x_285);
lean_dec(x_282);
x_9 = x_253;
x_10 = x_279;
x_11 = x_252;
x_12 = x_285;
goto block_16;
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_286 = lean_ctor_get(x_282, 1);
lean_inc(x_286);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_287 = x_282;
} else {
 lean_dec_ref(x_282);
 x_287 = lean_box(0);
}
x_288 = lean_mk_string_unchecked("cached: ", 8, 8);
x_289 = l_Lean_stringToMessageData(x_288);
lean_dec(x_288);
lean_inc(x_279);
x_290 = l_Lean_MessageData_ofName(x_279);
if (lean_is_scalar(x_287)) {
 x_291 = lean_alloc_ctor(7, 2, 0);
} else {
 x_291 = x_287;
 lean_ctor_set_tag(x_291, 7);
}
lean_ctor_set(x_291, 0, x_289);
lean_ctor_set(x_291, 1, x_290);
x_292 = lean_mk_string_unchecked("", 0, 0);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_291);
lean_ctor_set(x_294, 1, x_293);
x_295 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_281, x_294, x_168, x_169, x_170, x_286);
lean_dec(x_170);
lean_dec(x_169);
lean_dec(x_168);
x_296 = lean_ctor_get(x_295, 1);
lean_inc(x_296);
lean_dec(x_295);
x_9 = x_253;
x_10 = x_279;
x_11 = x_252;
x_12 = x_296;
goto block_16;
}
}
}
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
x_297 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize", 29, 29);
x_298 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize.specializeApp\?", 44, 44);
x_299 = lean_unsigned_to_nat(286u);
x_300 = lean_unsigned_to_nat(4u);
x_301 = lean_mk_string_unchecked("assertion violation: !key.hasFVar\n    ", 38, 38);
x_302 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_297, x_298, x_299, x_300, x_301);
lean_dec(x_301);
lean_dec(x_298);
lean_dec(x_297);
x_303 = l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6(x_302, x_165, x_166, x_167, x_168, x_169, x_170, x_171);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
lean_dec(x_164);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_161);
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
x_304 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize", 29, 29);
x_305 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize.specializeApp\?", 44, 44);
x_306 = lean_unsigned_to_nat(285u);
x_307 = lean_unsigned_to_nat(4u);
x_308 = lean_mk_string_unchecked("assertion violation: !key.hasLooseBVars\n    ", 44, 44);
x_309 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_304, x_305, x_306, x_307, x_308);
lean_dec(x_308);
lean_dec(x_305);
lean_dec(x_304);
x_310 = l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6(x_309, x_165, x_166, x_167, x_168, x_169, x_170, x_171);
return x_310;
}
}
block_382:
{
lean_object* x_321; 
lean_inc(x_319);
lean_inc(x_318);
lean_inc(x_317);
lean_inc(x_316);
lean_inc(x_314);
lean_inc(x_62);
lean_inc(x_77);
x_321 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg(x_77, x_62, x_314, x_316, x_317, x_318, x_319, x_320);
if (lean_obj_tag(x_321) == 0)
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; uint8_t x_335; 
x_322 = lean_ctor_get(x_321, 0);
lean_inc(x_322);
x_323 = lean_ctor_get(x_322, 1);
lean_inc(x_323);
x_324 = lean_ctor_get(x_321, 1);
lean_inc(x_324);
lean_dec(x_321);
x_325 = lean_ctor_get(x_322, 0);
lean_inc(x_325);
lean_dec(x_322);
x_326 = lean_ctor_get(x_323, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_323, 1);
lean_inc(x_327);
lean_dec(x_323);
x_328 = lean_unsigned_to_nat(0u);
x_329 = lean_array_get_size(x_325);
x_330 = l_Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1(x_325, x_328, x_329);
lean_dec(x_329);
lean_inc(x_61);
x_331 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_331, 0, x_60);
lean_ctor_set(x_331, 1, x_61);
lean_ctor_set(x_331, 2, x_330);
lean_inc(x_327);
x_332 = l_Lean_Compiler_LCNF_Specialize_mkKey___redArg(x_326, x_327, x_331, x_324);
x_333 = lean_ctor_get(x_332, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_332, 1);
lean_inc(x_334);
lean_dec(x_332);
x_335 = !lean_is_exclusive(x_333);
if (x_335 == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; uint8_t x_340; 
x_336 = lean_ctor_get(x_333, 0);
x_337 = lean_ctor_get(x_333, 1);
lean_inc(x_313);
x_338 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_313, x_318, x_334);
x_339 = lean_ctor_get(x_338, 0);
lean_inc(x_339);
x_340 = lean_unbox(x_339);
lean_dec(x_339);
if (x_340 == 0)
{
lean_object* x_341; 
lean_free_object(x_333);
lean_dec(x_313);
x_341 = lean_ctor_get(x_338, 1);
lean_inc(x_341);
lean_dec(x_338);
x_159 = x_326;
x_160 = x_328;
x_161 = x_325;
x_162 = x_336;
x_163 = x_327;
x_164 = x_337;
x_165 = x_314;
x_166 = x_315;
x_167 = x_316;
x_168 = x_317;
x_169 = x_318;
x_170 = x_319;
x_171 = x_341;
goto block_311;
}
else
{
uint8_t x_342; 
x_342 = !lean_is_exclusive(x_338);
if (x_342 == 0)
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; 
x_343 = lean_ctor_get(x_338, 1);
x_344 = lean_ctor_get(x_338, 0);
lean_dec(x_344);
x_345 = lean_mk_string_unchecked("key: ", 5, 5);
x_346 = l_Lean_stringToMessageData(x_345);
lean_dec(x_345);
lean_inc(x_336);
x_347 = l_Lean_MessageData_ofExpr(x_336);
lean_ctor_set_tag(x_338, 7);
lean_ctor_set(x_338, 1, x_347);
lean_ctor_set(x_338, 0, x_346);
x_348 = lean_mk_string_unchecked("", 0, 0);
x_349 = l_Lean_stringToMessageData(x_348);
lean_dec(x_348);
lean_ctor_set_tag(x_333, 7);
lean_ctor_set(x_333, 1, x_349);
lean_ctor_set(x_333, 0, x_338);
x_350 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_313, x_333, x_317, x_318, x_319, x_343);
x_351 = lean_ctor_get(x_350, 1);
lean_inc(x_351);
lean_dec(x_350);
x_159 = x_326;
x_160 = x_328;
x_161 = x_325;
x_162 = x_336;
x_163 = x_327;
x_164 = x_337;
x_165 = x_314;
x_166 = x_315;
x_167 = x_316;
x_168 = x_317;
x_169 = x_318;
x_170 = x_319;
x_171 = x_351;
goto block_311;
}
else
{
lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_352 = lean_ctor_get(x_338, 1);
lean_inc(x_352);
lean_dec(x_338);
x_353 = lean_mk_string_unchecked("key: ", 5, 5);
x_354 = l_Lean_stringToMessageData(x_353);
lean_dec(x_353);
lean_inc(x_336);
x_355 = l_Lean_MessageData_ofExpr(x_336);
x_356 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_mk_string_unchecked("", 0, 0);
x_358 = l_Lean_stringToMessageData(x_357);
lean_dec(x_357);
lean_ctor_set_tag(x_333, 7);
lean_ctor_set(x_333, 1, x_358);
lean_ctor_set(x_333, 0, x_356);
x_359 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_313, x_333, x_317, x_318, x_319, x_352);
x_360 = lean_ctor_get(x_359, 1);
lean_inc(x_360);
lean_dec(x_359);
x_159 = x_326;
x_160 = x_328;
x_161 = x_325;
x_162 = x_336;
x_163 = x_327;
x_164 = x_337;
x_165 = x_314;
x_166 = x_315;
x_167 = x_316;
x_168 = x_317;
x_169 = x_318;
x_170 = x_319;
x_171 = x_360;
goto block_311;
}
}
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_365; 
x_361 = lean_ctor_get(x_333, 0);
x_362 = lean_ctor_get(x_333, 1);
lean_inc(x_362);
lean_inc(x_361);
lean_dec(x_333);
lean_inc(x_313);
x_363 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_313, x_318, x_334);
x_364 = lean_ctor_get(x_363, 0);
lean_inc(x_364);
x_365 = lean_unbox(x_364);
lean_dec(x_364);
if (x_365 == 0)
{
lean_object* x_366; 
lean_dec(x_313);
x_366 = lean_ctor_get(x_363, 1);
lean_inc(x_366);
lean_dec(x_363);
x_159 = x_326;
x_160 = x_328;
x_161 = x_325;
x_162 = x_361;
x_163 = x_327;
x_164 = x_362;
x_165 = x_314;
x_166 = x_315;
x_167 = x_316;
x_168 = x_317;
x_169 = x_318;
x_170 = x_319;
x_171 = x_366;
goto block_311;
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_367 = lean_ctor_get(x_363, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_363)) {
 lean_ctor_release(x_363, 0);
 lean_ctor_release(x_363, 1);
 x_368 = x_363;
} else {
 lean_dec_ref(x_363);
 x_368 = lean_box(0);
}
x_369 = lean_mk_string_unchecked("key: ", 5, 5);
x_370 = l_Lean_stringToMessageData(x_369);
lean_dec(x_369);
lean_inc(x_361);
x_371 = l_Lean_MessageData_ofExpr(x_361);
if (lean_is_scalar(x_368)) {
 x_372 = lean_alloc_ctor(7, 2, 0);
} else {
 x_372 = x_368;
 lean_ctor_set_tag(x_372, 7);
}
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_mk_string_unchecked("", 0, 0);
x_374 = l_Lean_stringToMessageData(x_373);
lean_dec(x_373);
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_372);
lean_ctor_set(x_375, 1, x_374);
x_376 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_313, x_375, x_317, x_318, x_319, x_367);
x_377 = lean_ctor_get(x_376, 1);
lean_inc(x_377);
lean_dec(x_376);
x_159 = x_326;
x_160 = x_328;
x_161 = x_325;
x_162 = x_361;
x_163 = x_327;
x_164 = x_362;
x_165 = x_314;
x_166 = x_315;
x_167 = x_316;
x_168 = x_317;
x_169 = x_318;
x_170 = x_319;
x_171 = x_377;
goto block_311;
}
}
}
else
{
uint8_t x_378; 
lean_dec(x_319);
lean_dec(x_318);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_315);
lean_dec(x_314);
lean_dec(x_313);
lean_dec(x_158);
lean_dec(x_157);
lean_dec(x_154);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_378 = !lean_is_exclusive(x_321);
if (x_378 == 0)
{
return x_321;
}
else
{
lean_object* x_379; lean_object* x_380; lean_object* x_381; 
x_379 = lean_ctor_get(x_321, 0);
x_380 = lean_ctor_get(x_321, 1);
lean_inc(x_380);
lean_inc(x_379);
lean_dec(x_321);
x_381 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_381, 0, x_379);
lean_ctor_set(x_381, 1, x_380);
return x_381;
}
}
}
}
else
{
uint8_t x_422; 
lean_dec(x_155);
lean_dec(x_154);
lean_dec(x_80);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_422 = !lean_is_exclusive(x_146);
if (x_422 == 0)
{
lean_object* x_423; lean_object* x_424; 
x_423 = lean_ctor_get(x_146, 0);
lean_dec(x_423);
x_424 = lean_box(0);
lean_ctor_set(x_146, 0, x_424);
return x_146;
}
else
{
lean_object* x_425; lean_object* x_426; lean_object* x_427; 
x_425 = lean_ctor_get(x_146, 1);
lean_inc(x_425);
lean_dec(x_146);
x_426 = lean_box(0);
x_427 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_427, 0, x_426);
lean_ctor_set(x_427, 1, x_425);
return x_427;
}
}
}
}
block_143:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_83, 0);
lean_inc(x_94);
x_95 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg(x_84, x_94, x_92, x_93);
x_96 = lean_ctor_get(x_95, 1);
lean_inc(x_96);
lean_dec(x_95);
lean_inc(x_83);
x_97 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_83, x_92, x_96);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_99 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_83, x_89, x_90, x_91, x_92, x_98);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; uint8_t x_106; uint8_t x_107; uint8_t x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
lean_inc(x_100);
x_102 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_100, x_92, x_101);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
lean_dec(x_102);
x_104 = lean_alloc_ctor(0, 0, 4);
x_105 = lean_unbox(x_65);
lean_ctor_set_uint8(x_104, 0, x_105);
x_106 = lean_unbox(x_65);
lean_ctor_set_uint8(x_104, 1, x_106);
x_107 = lean_unbox(x_65);
lean_dec(x_65);
lean_ctor_set_uint8(x_104, 2, x_107);
x_108 = lean_unbox(x_80);
lean_ctor_set_uint8(x_104, 3, x_108);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_109 = l_Lean_Compiler_LCNF_Decl_simp(x_100, x_104, x_89, x_90, x_91, x_92, x_103);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; uint8_t x_113; uint8_t x_114; uint8_t x_115; uint8_t x_116; lean_object* x_117; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_alloc_ctor(0, 0, 4);
x_113 = lean_unbox(x_80);
lean_ctor_set_uint8(x_112, 0, x_113);
x_114 = lean_unbox(x_80);
lean_ctor_set_uint8(x_112, 1, x_114);
x_115 = lean_unbox(x_80);
lean_ctor_set_uint8(x_112, 2, x_115);
x_116 = lean_unbox(x_80);
lean_dec(x_80);
lean_ctor_set_uint8(x_112, 3, x_116);
lean_inc(x_92);
lean_inc(x_91);
lean_inc(x_90);
lean_inc(x_89);
x_117 = l_Lean_Compiler_LCNF_Decl_simp(x_110, x_112, x_89, x_90, x_91, x_92, x_111);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; uint8_t x_127; 
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_118, 3);
lean_inc(x_120);
x_121 = l_Lean_Compiler_LCNF_Specialize_paramsToVarSet(x_120);
x_122 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_visitCode), 8, 0);
x_123 = lean_ctor_get(x_118, 4);
lean_inc(x_123);
x_124 = lean_box(0);
x_125 = lean_ctor_get(x_118, 0);
lean_inc(x_125);
x_126 = lean_array_get_size(x_120);
x_127 = lean_nat_dec_lt(x_82, x_126);
if (x_127 == 0)
{
lean_dec(x_126);
x_17 = x_88;
x_18 = x_123;
x_19 = x_120;
x_20 = x_121;
x_21 = x_86;
x_22 = x_122;
x_23 = x_91;
x_24 = x_125;
x_25 = x_92;
x_26 = x_90;
x_27 = x_85;
x_28 = x_89;
x_29 = x_119;
x_30 = x_118;
x_31 = x_124;
goto block_59;
}
else
{
uint8_t x_128; 
x_128 = lean_nat_dec_le(x_126, x_126);
if (x_128 == 0)
{
lean_dec(x_126);
x_17 = x_88;
x_18 = x_123;
x_19 = x_120;
x_20 = x_121;
x_21 = x_86;
x_22 = x_122;
x_23 = x_91;
x_24 = x_125;
x_25 = x_92;
x_26 = x_90;
x_27 = x_85;
x_28 = x_89;
x_29 = x_119;
x_30 = x_118;
x_31 = x_124;
goto block_59;
}
else
{
size_t x_129; lean_object* x_130; 
x_129 = lean_usize_of_nat(x_126);
lean_dec(x_126);
x_130 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_120, x_87, x_129, x_124);
x_17 = x_88;
x_18 = x_123;
x_19 = x_120;
x_20 = x_121;
x_21 = x_86;
x_22 = x_122;
x_23 = x_91;
x_24 = x_125;
x_25 = x_92;
x_26 = x_90;
x_27 = x_85;
x_28 = x_89;
x_29 = x_119;
x_30 = x_118;
x_31 = x_130;
goto block_59;
}
}
}
else
{
uint8_t x_131; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
x_131 = !lean_is_exclusive(x_117);
if (x_131 == 0)
{
return x_117;
}
else
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_117, 0);
x_133 = lean_ctor_get(x_117, 1);
lean_inc(x_133);
lean_inc(x_132);
lean_dec(x_117);
x_134 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
return x_134;
}
}
}
else
{
uint8_t x_135; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_80);
x_135 = !lean_is_exclusive(x_109);
if (x_135 == 0)
{
return x_109;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_109, 0);
x_137 = lean_ctor_get(x_109, 1);
lean_inc(x_137);
lean_inc(x_136);
lean_dec(x_109);
x_138 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_138, 0, x_136);
lean_ctor_set(x_138, 1, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
lean_dec(x_89);
lean_dec(x_88);
lean_dec(x_86);
lean_dec(x_85);
lean_dec(x_80);
lean_dec(x_65);
x_139 = !lean_is_exclusive(x_99);
if (x_139 == 0)
{
return x_99;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_140 = lean_ctor_get(x_99, 0);
x_141 = lean_ctor_get(x_99, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_99);
x_142 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_142, 0, x_140);
lean_ctor_set(x_142, 1, x_141);
return x_142;
}
}
}
}
else
{
lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; lean_object* x_433; lean_object* x_434; size_t x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_492; 
x_428 = lean_ctor_get(x_78, 0);
x_429 = lean_ctor_get(x_78, 1);
lean_inc(x_429);
lean_inc(x_428);
lean_dec(x_78);
x_492 = lean_unbox(x_428);
if (x_492 == 0)
{
lean_object* x_493; lean_object* x_494; 
lean_dec(x_428);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_493 = lean_box(0);
x_494 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_429);
return x_494;
}
else
{
lean_object* x_495; lean_object* x_496; 
lean_inc(x_60);
x_495 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_60, x_4, x_7, x_429);
x_496 = lean_ctor_get(x_495, 0);
lean_inc(x_496);
if (lean_obj_tag(x_496) == 0)
{
lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; 
lean_dec(x_428);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_497 = lean_ctor_get(x_495, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_498 = x_495;
} else {
 lean_dec_ref(x_495);
 x_498 = lean_box(0);
}
x_499 = lean_box(0);
if (lean_is_scalar(x_498)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_498;
}
lean_ctor_set(x_500, 0, x_499);
lean_ctor_set(x_500, 1, x_497);
return x_500;
}
else
{
lean_object* x_501; lean_object* x_502; 
x_501 = lean_ctor_get(x_496, 0);
lean_inc(x_501);
lean_dec(x_496);
x_502 = lean_ctor_get(x_501, 4);
lean_inc(x_502);
if (lean_obj_tag(x_502) == 0)
{
lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; lean_object* x_518; lean_object* x_590; lean_object* x_591; lean_object* x_592; lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_636; lean_object* x_637; uint8_t x_638; 
lean_dec(x_502);
x_503 = lean_ctor_get(x_495, 1);
lean_inc(x_503);
lean_dec(x_495);
x_504 = lean_mk_string_unchecked("Compiler", 8, 8);
x_505 = lean_mk_string_unchecked("specialize", 10, 10);
x_590 = lean_mk_string_unchecked("candidate", 9, 9);
lean_inc(x_505);
lean_inc(x_504);
x_591 = l_Lean_Name_mkStr3(x_504, x_505, x_590);
lean_inc(x_591);
x_636 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_591, x_6, x_503);
x_637 = lean_ctor_get(x_636, 0);
lean_inc(x_637);
x_638 = lean_unbox(x_637);
lean_dec(x_637);
if (x_638 == 0)
{
lean_object* x_639; 
lean_dec(x_1);
x_639 = lean_ctor_get(x_636, 1);
lean_inc(x_639);
lean_dec(x_636);
x_592 = x_2;
x_593 = x_3;
x_594 = x_4;
x_595 = x_5;
x_596 = x_6;
x_597 = x_7;
x_598 = x_639;
goto block_635;
}
else
{
lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_640 = lean_ctor_get(x_636, 1);
lean_inc(x_640);
if (lean_is_exclusive(x_636)) {
 lean_ctor_release(x_636, 0);
 lean_ctor_release(x_636, 1);
 x_641 = x_636;
} else {
 lean_dec_ref(x_636);
 x_641 = lean_box(0);
}
x_642 = lean_mk_string_unchecked("", 0, 0);
x_643 = l_Lean_stringToMessageData(x_642);
lean_dec(x_642);
x_644 = l_Lean_Compiler_LCNF_LetValue_toExpr(x_1);
x_645 = l_Lean_MessageData_ofExpr(x_644);
lean_inc(x_643);
if (lean_is_scalar(x_641)) {
 x_646 = lean_alloc_ctor(7, 2, 0);
} else {
 x_646 = x_641;
 lean_ctor_set_tag(x_646, 7);
}
lean_ctor_set(x_646, 0, x_643);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_mk_string_unchecked(", ", 2, 2);
x_648 = l_Lean_stringToMessageData(x_647);
lean_dec(x_647);
x_649 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_649, 0, x_646);
lean_ctor_set(x_649, 1, x_648);
lean_inc(x_77);
x_650 = lean_array_to_list(x_77);
x_651 = lean_box(0);
x_652 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_saveSpecParamInfo_spec__13(x_650, x_651);
x_653 = l_Lean_MessageData_ofList(x_652);
x_654 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_654, 0, x_649);
lean_ctor_set(x_654, 1, x_653);
x_655 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_655, 0, x_654);
lean_ctor_set(x_655, 1, x_643);
lean_inc(x_591);
x_656 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_591, x_655, x_5, x_6, x_7, x_640);
x_657 = lean_ctor_get(x_656, 1);
lean_inc(x_657);
lean_dec(x_656);
x_592 = x_2;
x_593 = x_3;
x_594 = x_4;
x_595 = x_5;
x_596 = x_6;
x_597 = x_7;
x_598 = x_657;
goto block_635;
}
block_589:
{
uint8_t x_519; 
x_519 = l_Lean_Expr_hasLooseBVars(x_509);
if (x_519 == 0)
{
uint8_t x_520; 
x_520 = l_Lean_Expr_hasFVar(x_509);
if (x_520 == 0)
{
lean_object* x_521; lean_object* x_522; lean_object* x_523; lean_object* x_524; size_t x_525; lean_object* x_526; size_t x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; 
x_521 = l_Lean_Compiler_LCNF_Specialize_findSpecCache_x3f___redArg(x_509, x_517, x_518);
x_522 = lean_ctor_get(x_521, 0);
lean_inc(x_522);
x_523 = lean_ctor_get(x_521, 1);
lean_inc(x_523);
if (lean_is_exclusive(x_521)) {
 lean_ctor_release(x_521, 0);
 lean_ctor_release(x_521, 1);
 x_524 = x_521;
} else {
 lean_dec_ref(x_521);
 x_524 = lean_box(0);
}
x_525 = lean_array_size(x_506);
x_526 = lean_box(0);
x_527 = lean_usize_of_nat(x_507);
lean_inc(x_506);
x_528 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_525, x_527, x_506);
x_529 = l_Lean_Compiler_LCNF_Specialize_getRemainingArgs(x_77, x_62);
lean_dec(x_77);
lean_inc(x_511);
x_530 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Elab_addConstInfo___at___Lean_Elab_realizeGlobalConstNoOverloadWithInfo_spec__0_spec__0_spec__1(x_511, x_526);
x_531 = l_Array_append(lean_box(0), x_528, x_529);
lean_dec(x_529);
if (lean_obj_tag(x_522) == 0)
{
lean_object* x_532; 
lean_inc(x_517);
lean_inc(x_516);
lean_inc(x_515);
lean_inc(x_514);
x_532 = l_Lean_Compiler_LCNF_Specialize_mkSpecDecl(x_501, x_61, x_508, x_506, x_510, x_511, x_512, x_513, x_514, x_515, x_516, x_517, x_523);
if (lean_obj_tag(x_532) == 0)
{
lean_object* x_533; lean_object* x_534; lean_object* x_535; lean_object* x_536; lean_object* x_537; lean_object* x_538; uint8_t x_539; 
x_533 = lean_ctor_get(x_532, 0);
lean_inc(x_533);
x_534 = lean_ctor_get(x_532, 1);
lean_inc(x_534);
lean_dec(x_532);
x_535 = lean_mk_string_unchecked("step", 4, 4);
x_536 = l_Lean_Name_mkStr3(x_504, x_505, x_535);
lean_inc(x_536);
x_537 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_536, x_516, x_534);
x_538 = lean_ctor_get(x_537, 0);
lean_inc(x_538);
x_539 = lean_unbox(x_538);
lean_dec(x_538);
if (x_539 == 0)
{
lean_object* x_540; 
lean_dec(x_536);
lean_dec(x_524);
x_540 = lean_ctor_get(x_537, 1);
lean_inc(x_540);
lean_dec(x_537);
x_430 = x_507;
x_431 = x_533;
x_432 = x_509;
x_433 = x_531;
x_434 = x_530;
x_435 = x_527;
x_436 = x_513;
x_437 = x_514;
x_438 = x_515;
x_439 = x_516;
x_440 = x_517;
x_441 = x_540;
goto block_491;
}
else
{
lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; lean_object* x_550; lean_object* x_551; lean_object* x_552; 
x_541 = lean_ctor_get(x_537, 1);
lean_inc(x_541);
if (lean_is_exclusive(x_537)) {
 lean_ctor_release(x_537, 0);
 lean_ctor_release(x_537, 1);
 x_542 = x_537;
} else {
 lean_dec_ref(x_537);
 x_542 = lean_box(0);
}
x_543 = lean_mk_string_unchecked("new: ", 5, 5);
x_544 = l_Lean_stringToMessageData(x_543);
lean_dec(x_543);
x_545 = lean_ctor_get(x_533, 0);
lean_inc(x_545);
x_546 = l_Lean_MessageData_ofName(x_545);
if (lean_is_scalar(x_542)) {
 x_547 = lean_alloc_ctor(7, 2, 0);
} else {
 x_547 = x_542;
 lean_ctor_set_tag(x_547, 7);
}
lean_ctor_set(x_547, 0, x_544);
lean_ctor_set(x_547, 1, x_546);
x_548 = lean_mk_string_unchecked("", 0, 0);
x_549 = l_Lean_stringToMessageData(x_548);
lean_dec(x_548);
if (lean_is_scalar(x_524)) {
 x_550 = lean_alloc_ctor(7, 2, 0);
} else {
 x_550 = x_524;
 lean_ctor_set_tag(x_550, 7);
}
lean_ctor_set(x_550, 0, x_547);
lean_ctor_set(x_550, 1, x_549);
x_551 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_536, x_550, x_515, x_516, x_517, x_541);
x_552 = lean_ctor_get(x_551, 1);
lean_inc(x_552);
lean_dec(x_551);
x_430 = x_507;
x_431 = x_533;
x_432 = x_509;
x_433 = x_531;
x_434 = x_530;
x_435 = x_527;
x_436 = x_513;
x_437 = x_514;
x_438 = x_515;
x_439 = x_516;
x_440 = x_517;
x_441 = x_552;
goto block_491;
}
}
else
{
lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; 
lean_dec(x_531);
lean_dec(x_530);
lean_dec(x_524);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_509);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_428);
lean_dec(x_65);
x_553 = lean_ctor_get(x_532, 0);
lean_inc(x_553);
x_554 = lean_ctor_get(x_532, 1);
lean_inc(x_554);
if (lean_is_exclusive(x_532)) {
 lean_ctor_release(x_532, 0);
 lean_ctor_release(x_532, 1);
 x_555 = x_532;
} else {
 lean_dec_ref(x_532);
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
else
{
lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; uint8_t x_562; 
lean_dec(x_514);
lean_dec(x_513);
lean_dec(x_512);
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_506);
lean_dec(x_501);
lean_dec(x_428);
lean_dec(x_65);
lean_dec(x_61);
x_557 = lean_ctor_get(x_522, 0);
lean_inc(x_557);
lean_dec(x_522);
x_558 = lean_mk_string_unchecked("step", 4, 4);
x_559 = l_Lean_Name_mkStr3(x_504, x_505, x_558);
lean_inc(x_559);
x_560 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_559, x_516, x_523);
x_561 = lean_ctor_get(x_560, 0);
lean_inc(x_561);
x_562 = lean_unbox(x_561);
lean_dec(x_561);
if (x_562 == 0)
{
lean_object* x_563; 
lean_dec(x_559);
lean_dec(x_524);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
x_563 = lean_ctor_get(x_560, 1);
lean_inc(x_563);
lean_dec(x_560);
x_9 = x_531;
x_10 = x_557;
x_11 = x_530;
x_12 = x_563;
goto block_16;
}
else
{
lean_object* x_564; lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; 
x_564 = lean_ctor_get(x_560, 1);
lean_inc(x_564);
if (lean_is_exclusive(x_560)) {
 lean_ctor_release(x_560, 0);
 lean_ctor_release(x_560, 1);
 x_565 = x_560;
} else {
 lean_dec_ref(x_560);
 x_565 = lean_box(0);
}
x_566 = lean_mk_string_unchecked("cached: ", 8, 8);
x_567 = l_Lean_stringToMessageData(x_566);
lean_dec(x_566);
lean_inc(x_557);
x_568 = l_Lean_MessageData_ofName(x_557);
if (lean_is_scalar(x_565)) {
 x_569 = lean_alloc_ctor(7, 2, 0);
} else {
 x_569 = x_565;
 lean_ctor_set_tag(x_569, 7);
}
lean_ctor_set(x_569, 0, x_567);
lean_ctor_set(x_569, 1, x_568);
x_570 = lean_mk_string_unchecked("", 0, 0);
x_571 = l_Lean_stringToMessageData(x_570);
lean_dec(x_570);
if (lean_is_scalar(x_524)) {
 x_572 = lean_alloc_ctor(7, 2, 0);
} else {
 x_572 = x_524;
 lean_ctor_set_tag(x_572, 7);
}
lean_ctor_set(x_572, 0, x_569);
lean_ctor_set(x_572, 1, x_571);
x_573 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_559, x_572, x_515, x_516, x_517, x_564);
lean_dec(x_517);
lean_dec(x_516);
lean_dec(x_515);
x_574 = lean_ctor_get(x_573, 1);
lean_inc(x_574);
lean_dec(x_573);
x_9 = x_531;
x_10 = x_557;
x_11 = x_530;
x_12 = x_574;
goto block_16;
}
}
}
else
{
lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; 
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_501);
lean_dec(x_428);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
x_575 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize", 29, 29);
x_576 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize.specializeApp\?", 44, 44);
x_577 = lean_unsigned_to_nat(286u);
x_578 = lean_unsigned_to_nat(4u);
x_579 = lean_mk_string_unchecked("assertion violation: !key.hasFVar\n    ", 38, 38);
x_580 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_575, x_576, x_577, x_578, x_579);
lean_dec(x_579);
lean_dec(x_576);
lean_dec(x_575);
x_581 = l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6(x_580, x_512, x_513, x_514, x_515, x_516, x_517, x_518);
return x_581;
}
}
else
{
lean_object* x_582; lean_object* x_583; lean_object* x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; 
lean_dec(x_511);
lean_dec(x_510);
lean_dec(x_509);
lean_dec(x_508);
lean_dec(x_506);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_501);
lean_dec(x_428);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
x_582 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize", 29, 29);
x_583 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Specialize.specializeApp\?", 44, 44);
x_584 = lean_unsigned_to_nat(285u);
x_585 = lean_unsigned_to_nat(4u);
x_586 = lean_mk_string_unchecked("assertion violation: !key.hasLooseBVars\n    ", 44, 44);
x_587 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_582, x_583, x_584, x_585, x_586);
lean_dec(x_586);
lean_dec(x_583);
lean_dec(x_582);
x_588 = l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6(x_587, x_512, x_513, x_514, x_515, x_516, x_517, x_518);
return x_588;
}
}
block_635:
{
lean_object* x_599; 
lean_inc(x_597);
lean_inc(x_596);
lean_inc(x_595);
lean_inc(x_594);
lean_inc(x_592);
lean_inc(x_62);
lean_inc(x_77);
x_599 = l_Lean_Compiler_LCNF_Specialize_Collector_collect___redArg(x_77, x_62, x_592, x_594, x_595, x_596, x_597, x_598);
if (lean_obj_tag(x_599) == 0)
{
lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; lean_object* x_606; lean_object* x_607; lean_object* x_608; lean_object* x_609; lean_object* x_610; lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; uint8_t x_618; 
x_600 = lean_ctor_get(x_599, 0);
lean_inc(x_600);
x_601 = lean_ctor_get(x_600, 1);
lean_inc(x_601);
x_602 = lean_ctor_get(x_599, 1);
lean_inc(x_602);
lean_dec(x_599);
x_603 = lean_ctor_get(x_600, 0);
lean_inc(x_603);
lean_dec(x_600);
x_604 = lean_ctor_get(x_601, 0);
lean_inc(x_604);
x_605 = lean_ctor_get(x_601, 1);
lean_inc(x_605);
lean_dec(x_601);
x_606 = lean_unsigned_to_nat(0u);
x_607 = lean_array_get_size(x_603);
x_608 = l_Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1(x_603, x_606, x_607);
lean_dec(x_607);
lean_inc(x_61);
x_609 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_609, 0, x_60);
lean_ctor_set(x_609, 1, x_61);
lean_ctor_set(x_609, 2, x_608);
lean_inc(x_605);
x_610 = l_Lean_Compiler_LCNF_Specialize_mkKey___redArg(x_604, x_605, x_609, x_602);
x_611 = lean_ctor_get(x_610, 0);
lean_inc(x_611);
x_612 = lean_ctor_get(x_610, 1);
lean_inc(x_612);
lean_dec(x_610);
x_613 = lean_ctor_get(x_611, 0);
lean_inc(x_613);
x_614 = lean_ctor_get(x_611, 1);
lean_inc(x_614);
if (lean_is_exclusive(x_611)) {
 lean_ctor_release(x_611, 0);
 lean_ctor_release(x_611, 1);
 x_615 = x_611;
} else {
 lean_dec_ref(x_611);
 x_615 = lean_box(0);
}
lean_inc(x_591);
x_616 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_591, x_596, x_612);
x_617 = lean_ctor_get(x_616, 0);
lean_inc(x_617);
x_618 = lean_unbox(x_617);
lean_dec(x_617);
if (x_618 == 0)
{
lean_object* x_619; 
lean_dec(x_615);
lean_dec(x_591);
x_619 = lean_ctor_get(x_616, 1);
lean_inc(x_619);
lean_dec(x_616);
x_506 = x_604;
x_507 = x_606;
x_508 = x_603;
x_509 = x_613;
x_510 = x_605;
x_511 = x_614;
x_512 = x_592;
x_513 = x_593;
x_514 = x_594;
x_515 = x_595;
x_516 = x_596;
x_517 = x_597;
x_518 = x_619;
goto block_589;
}
else
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; 
x_620 = lean_ctor_get(x_616, 1);
lean_inc(x_620);
if (lean_is_exclusive(x_616)) {
 lean_ctor_release(x_616, 0);
 lean_ctor_release(x_616, 1);
 x_621 = x_616;
} else {
 lean_dec_ref(x_616);
 x_621 = lean_box(0);
}
x_622 = lean_mk_string_unchecked("key: ", 5, 5);
x_623 = l_Lean_stringToMessageData(x_622);
lean_dec(x_622);
lean_inc(x_613);
x_624 = l_Lean_MessageData_ofExpr(x_613);
if (lean_is_scalar(x_621)) {
 x_625 = lean_alloc_ctor(7, 2, 0);
} else {
 x_625 = x_621;
 lean_ctor_set_tag(x_625, 7);
}
lean_ctor_set(x_625, 0, x_623);
lean_ctor_set(x_625, 1, x_624);
x_626 = lean_mk_string_unchecked("", 0, 0);
x_627 = l_Lean_stringToMessageData(x_626);
lean_dec(x_626);
if (lean_is_scalar(x_615)) {
 x_628 = lean_alloc_ctor(7, 2, 0);
} else {
 x_628 = x_615;
 lean_ctor_set_tag(x_628, 7);
}
lean_ctor_set(x_628, 0, x_625);
lean_ctor_set(x_628, 1, x_627);
x_629 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_591, x_628, x_595, x_596, x_597, x_620);
x_630 = lean_ctor_get(x_629, 1);
lean_inc(x_630);
lean_dec(x_629);
x_506 = x_604;
x_507 = x_606;
x_508 = x_603;
x_509 = x_613;
x_510 = x_605;
x_511 = x_614;
x_512 = x_592;
x_513 = x_593;
x_514 = x_594;
x_515 = x_595;
x_516 = x_596;
x_517 = x_597;
x_518 = x_630;
goto block_589;
}
}
else
{
lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; 
lean_dec(x_597);
lean_dec(x_596);
lean_dec(x_595);
lean_dec(x_594);
lean_dec(x_593);
lean_dec(x_592);
lean_dec(x_591);
lean_dec(x_505);
lean_dec(x_504);
lean_dec(x_501);
lean_dec(x_428);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
x_631 = lean_ctor_get(x_599, 0);
lean_inc(x_631);
x_632 = lean_ctor_get(x_599, 1);
lean_inc(x_632);
if (lean_is_exclusive(x_599)) {
 lean_ctor_release(x_599, 0);
 lean_ctor_release(x_599, 1);
 x_633 = x_599;
} else {
 lean_dec_ref(x_599);
 x_633 = lean_box(0);
}
if (lean_is_scalar(x_633)) {
 x_634 = lean_alloc_ctor(1, 2, 0);
} else {
 x_634 = x_633;
}
lean_ctor_set(x_634, 0, x_631);
lean_ctor_set(x_634, 1, x_632);
return x_634;
}
}
}
else
{
lean_object* x_658; lean_object* x_659; lean_object* x_660; lean_object* x_661; 
lean_dec(x_502);
lean_dec(x_501);
lean_dec(x_428);
lean_dec(x_77);
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_658 = lean_ctor_get(x_495, 1);
lean_inc(x_658);
if (lean_is_exclusive(x_495)) {
 lean_ctor_release(x_495, 0);
 lean_ctor_release(x_495, 1);
 x_659 = x_495;
} else {
 lean_dec_ref(x_495);
 x_659 = lean_box(0);
}
x_660 = lean_box(0);
if (lean_is_scalar(x_659)) {
 x_661 = lean_alloc_ctor(0, 2, 0);
} else {
 x_661 = x_659;
}
lean_ctor_set(x_661, 0, x_660);
lean_ctor_set(x_661, 1, x_658);
return x_661;
}
}
}
block_491:
{
lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_442 = lean_ctor_get(x_431, 0);
lean_inc(x_442);
x_443 = l_Lean_Compiler_LCNF_Specialize_cacheSpec___redArg(x_432, x_442, x_440, x_441);
x_444 = lean_ctor_get(x_443, 1);
lean_inc(x_444);
lean_dec(x_443);
lean_inc(x_431);
x_445 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_431, x_440, x_444);
x_446 = lean_ctor_get(x_445, 1);
lean_inc(x_446);
lean_dec(x_445);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
x_447 = l_Lean_Compiler_LCNF_Decl_etaExpand(x_431, x_437, x_438, x_439, x_440, x_446);
if (lean_obj_tag(x_447) == 0)
{
lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; uint8_t x_453; uint8_t x_454; uint8_t x_455; uint8_t x_456; lean_object* x_457; 
x_448 = lean_ctor_get(x_447, 0);
lean_inc(x_448);
x_449 = lean_ctor_get(x_447, 1);
lean_inc(x_449);
lean_dec(x_447);
lean_inc(x_448);
x_450 = l_Lean_Compiler_LCNF_Decl_saveBase___redArg(x_448, x_440, x_449);
x_451 = lean_ctor_get(x_450, 1);
lean_inc(x_451);
lean_dec(x_450);
x_452 = lean_alloc_ctor(0, 0, 4);
x_453 = lean_unbox(x_65);
lean_ctor_set_uint8(x_452, 0, x_453);
x_454 = lean_unbox(x_65);
lean_ctor_set_uint8(x_452, 1, x_454);
x_455 = lean_unbox(x_65);
lean_dec(x_65);
lean_ctor_set_uint8(x_452, 2, x_455);
x_456 = lean_unbox(x_428);
lean_ctor_set_uint8(x_452, 3, x_456);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
x_457 = l_Lean_Compiler_LCNF_Decl_simp(x_448, x_452, x_437, x_438, x_439, x_440, x_451);
if (lean_obj_tag(x_457) == 0)
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; uint8_t x_461; uint8_t x_462; uint8_t x_463; uint8_t x_464; lean_object* x_465; 
x_458 = lean_ctor_get(x_457, 0);
lean_inc(x_458);
x_459 = lean_ctor_get(x_457, 1);
lean_inc(x_459);
lean_dec(x_457);
x_460 = lean_alloc_ctor(0, 0, 4);
x_461 = lean_unbox(x_428);
lean_ctor_set_uint8(x_460, 0, x_461);
x_462 = lean_unbox(x_428);
lean_ctor_set_uint8(x_460, 1, x_462);
x_463 = lean_unbox(x_428);
lean_ctor_set_uint8(x_460, 2, x_463);
x_464 = lean_unbox(x_428);
lean_dec(x_428);
lean_ctor_set_uint8(x_460, 3, x_464);
lean_inc(x_440);
lean_inc(x_439);
lean_inc(x_438);
lean_inc(x_437);
x_465 = l_Lean_Compiler_LCNF_Decl_simp(x_458, x_460, x_437, x_438, x_439, x_440, x_459);
if (lean_obj_tag(x_465) == 0)
{
lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; uint8_t x_475; 
x_466 = lean_ctor_get(x_465, 0);
lean_inc(x_466);
x_467 = lean_ctor_get(x_465, 1);
lean_inc(x_467);
lean_dec(x_465);
x_468 = lean_ctor_get(x_466, 3);
lean_inc(x_468);
x_469 = l_Lean_Compiler_LCNF_Specialize_paramsToVarSet(x_468);
x_470 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_visitCode), 8, 0);
x_471 = lean_ctor_get(x_466, 4);
lean_inc(x_471);
x_472 = lean_box(0);
x_473 = lean_ctor_get(x_466, 0);
lean_inc(x_473);
x_474 = lean_array_get_size(x_468);
x_475 = lean_nat_dec_lt(x_430, x_474);
if (x_475 == 0)
{
lean_dec(x_474);
x_17 = x_436;
x_18 = x_471;
x_19 = x_468;
x_20 = x_469;
x_21 = x_434;
x_22 = x_470;
x_23 = x_439;
x_24 = x_473;
x_25 = x_440;
x_26 = x_438;
x_27 = x_433;
x_28 = x_437;
x_29 = x_467;
x_30 = x_466;
x_31 = x_472;
goto block_59;
}
else
{
uint8_t x_476; 
x_476 = lean_nat_dec_le(x_474, x_474);
if (x_476 == 0)
{
lean_dec(x_474);
x_17 = x_436;
x_18 = x_471;
x_19 = x_468;
x_20 = x_469;
x_21 = x_434;
x_22 = x_470;
x_23 = x_439;
x_24 = x_473;
x_25 = x_440;
x_26 = x_438;
x_27 = x_433;
x_28 = x_437;
x_29 = x_467;
x_30 = x_466;
x_31 = x_472;
goto block_59;
}
else
{
size_t x_477; lean_object* x_478; 
x_477 = lean_usize_of_nat(x_474);
lean_dec(x_474);
x_478 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_468, x_435, x_477, x_472);
x_17 = x_436;
x_18 = x_471;
x_19 = x_468;
x_20 = x_469;
x_21 = x_434;
x_22 = x_470;
x_23 = x_439;
x_24 = x_473;
x_25 = x_440;
x_26 = x_438;
x_27 = x_433;
x_28 = x_437;
x_29 = x_467;
x_30 = x_466;
x_31 = x_478;
goto block_59;
}
}
}
else
{
lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; 
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_433);
x_479 = lean_ctor_get(x_465, 0);
lean_inc(x_479);
x_480 = lean_ctor_get(x_465, 1);
lean_inc(x_480);
if (lean_is_exclusive(x_465)) {
 lean_ctor_release(x_465, 0);
 lean_ctor_release(x_465, 1);
 x_481 = x_465;
} else {
 lean_dec_ref(x_465);
 x_481 = lean_box(0);
}
if (lean_is_scalar(x_481)) {
 x_482 = lean_alloc_ctor(1, 2, 0);
} else {
 x_482 = x_481;
}
lean_ctor_set(x_482, 0, x_479);
lean_ctor_set(x_482, 1, x_480);
return x_482;
}
}
else
{
lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; 
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_428);
x_483 = lean_ctor_get(x_457, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_457, 1);
lean_inc(x_484);
if (lean_is_exclusive(x_457)) {
 lean_ctor_release(x_457, 0);
 lean_ctor_release(x_457, 1);
 x_485 = x_457;
} else {
 lean_dec_ref(x_457);
 x_485 = lean_box(0);
}
if (lean_is_scalar(x_485)) {
 x_486 = lean_alloc_ctor(1, 2, 0);
} else {
 x_486 = x_485;
}
lean_ctor_set(x_486, 0, x_483);
lean_ctor_set(x_486, 1, x_484);
return x_486;
}
}
else
{
lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; 
lean_dec(x_440);
lean_dec(x_439);
lean_dec(x_438);
lean_dec(x_437);
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_433);
lean_dec(x_428);
lean_dec(x_65);
x_487 = lean_ctor_get(x_447, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_447, 1);
lean_inc(x_488);
if (lean_is_exclusive(x_447)) {
 lean_ctor_release(x_447, 0);
 lean_ctor_release(x_447, 1);
 x_489 = x_447;
} else {
 lean_dec_ref(x_447);
 x_489 = lean_box(0);
}
if (lean_is_scalar(x_489)) {
 x_490 = lean_alloc_ctor(1, 2, 0);
} else {
 x_490 = x_489;
}
lean_ctor_set(x_490, 0, x_487);
lean_ctor_set(x_490, 1, x_488);
return x_490;
}
}
}
}
}
else
{
uint8_t x_662; 
lean_dec(x_65);
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_662 = !lean_is_exclusive(x_64);
if (x_662 == 0)
{
lean_object* x_663; lean_object* x_664; 
x_663 = lean_ctor_get(x_64, 0);
lean_dec(x_663);
x_664 = lean_box(0);
lean_ctor_set(x_64, 0, x_664);
return x_64;
}
else
{
lean_object* x_665; lean_object* x_666; lean_object* x_667; 
x_665 = lean_ctor_get(x_64, 1);
lean_inc(x_665);
lean_dec(x_64);
x_666 = lean_box(0);
x_667 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_667, 0, x_666);
lean_ctor_set(x_667, 1, x_665);
return x_667;
}
}
}
else
{
lean_object* x_668; lean_object* x_669; 
lean_dec(x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_668 = lean_box(0);
x_669 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_669, 0, x_668);
lean_ctor_set(x_669, 1, x_8);
return x_669;
}
}
else
{
lean_object* x_670; lean_object* x_671; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_670 = lean_box(0);
x_671 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_671, 0, x_670);
lean_ctor_set(x_671, 1, x_8);
return x_671;
}
block_16:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_11);
lean_ctor_set(x_13, 2, x_9);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
block_59:
{
lean_object* x_32; lean_object* x_33; 
lean_inc(x_24);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_20);
lean_ctor_set(x_32, 2, x_24);
lean_inc(x_17);
x_33 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__3(x_22, x_18, x_32, x_17, x_28, x_26, x_23, x_25, x_29);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; uint8_t x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_st_ref_take(x_17, x_35);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
x_39 = lean_ctor_get(x_30, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_30, 2);
lean_inc(x_40);
x_41 = lean_ctor_get_uint8(x_30, sizeof(void*)*6);
x_42 = lean_ctor_get_uint8(x_30, sizeof(void*)*6 + 1);
x_43 = lean_ctor_get(x_30, 5);
lean_inc(x_43);
lean_dec(x_30);
lean_inc(x_24);
x_44 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_44, 0, x_24);
lean_ctor_set(x_44, 1, x_39);
lean_ctor_set(x_44, 2, x_40);
lean_ctor_set(x_44, 3, x_19);
lean_ctor_set(x_44, 4, x_34);
lean_ctor_set(x_44, 5, x_43);
lean_ctor_set_uint8(x_44, sizeof(void*)*6, x_41);
lean_ctor_set_uint8(x_44, sizeof(void*)*6 + 1, x_42);
x_45 = lean_array_push(x_37, x_44);
x_46 = lean_st_ref_set(x_17, x_45, x_38);
lean_dec(x_17);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_46, 0);
lean_dec(x_48);
x_49 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_49, 0, x_24);
lean_ctor_set(x_49, 1, x_21);
lean_ctor_set(x_49, 2, x_27);
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_46, 0, x_50);
return x_46;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_46, 1);
lean_inc(x_51);
lean_dec(x_46);
x_52 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_52, 0, x_24);
lean_ctor_set(x_52, 1, x_21);
lean_ctor_set(x_52, 2, x_27);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8_t x_55; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_24);
lean_dec(x_21);
lean_dec(x_19);
lean_dec(x_17);
x_55 = !lean_is_exclusive(x_33);
if (x_55 == 0)
{
return x_33;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_33, 0);
x_57 = lean_ctor_get(x_33, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_33);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_5);
x_7 = lean_array_uget(x_2, x_3);
lean_inc(x_1);
x_8 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0_spec__1(x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_dec(x_1);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_5 = x_9;
goto _start;
}
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 2);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_apply_1(x_1, x_3);
return x_4;
}
case 3:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_ctor_get(x_2, 2);
lean_inc(x_5);
lean_dec(x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get_size(x_5);
x_8 = lean_box(0);
x_9 = lean_nat_dec_lt(x_6, x_7);
if (x_9 == 0)
{
lean_object* x_10; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_8);
return x_10;
}
else
{
uint8_t x_11; 
x_11 = lean_nat_dec_le(x_7, x_7);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_12, 0, x_8);
return x_12;
}
else
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_usize_of_nat(x_6);
x_14 = lean_usize_of_nat(x_7);
lean_dec(x_7);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_5, x_13, x_14, x_8);
lean_dec(x_5);
return x_15;
}
}
}
case 4:
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_dec(x_2);
lean_inc(x_1);
x_18 = lean_apply_1(x_1, x_16);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_17);
lean_dec(x_1);
return x_18;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_17);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_17);
lean_dec(x_1);
lean_ctor_set(x_18, 0, x_23);
return x_18;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_18);
x_26 = lean_usize_of_nat(x_21);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_17, x_26, x_27, x_23);
lean_dec(x_17);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
lean_dec(x_18);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_17);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_1);
x_33 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_33, 0, x_31);
return x_33;
}
else
{
uint8_t x_34; 
x_34 = lean_nat_dec_le(x_30, x_30);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_30);
lean_dec(x_17);
lean_dec(x_1);
x_35 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_35, 0, x_31);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_usize_of_nat(x_29);
x_37 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_38 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_17, x_36, x_37, x_31);
lean_dec(x_17);
return x_38;
}
}
}
}
}
default: 
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
return x_40;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0_spec__0_spec__0___lam__0), 2, 1);
lean_closure_set(x_3, 0, x_1);
x_4 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0(x_3, x_2);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
return x_6;
}
else
{
lean_object* x_7; uint8_t x_8; 
lean_dec(x_4);
x_7 = lean_box(1);
x_8 = lean_unbox(x_7);
return x_8;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_shouldSpecialize_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(x_5, 0, x_4);
x_6 = l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0(x_5, x_1);
x_7 = lean_box(x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0___redArg(x_1, x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_fget(x_2, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_13, 2);
lean_inc(x_28);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_27);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_27);
x_29 = x_42;
goto block_41;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_27);
x_29 = x_42;
goto block_41;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = lean_usize_of_nat(x_43);
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_27, x_47, x_48, x_42);
lean_dec(x_27);
x_29 = x_49;
goto block_41;
}
}
block_41:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_28, x_32, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_13);
x_36 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_34);
x_14 = x_36;
x_15 = x_35;
goto block_26;
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_13, 0);
lean_inc(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_13);
x_54 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_52);
x_14 = x_54;
x_15 = x_53;
goto block_26;
}
else
{
uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
block_26:
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = lean_array_fset(x_2, x_1, x_14);
lean_dec(x_1);
x_1 = x_20;
x_2 = x_21;
x_9 = x_15;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_1, x_23);
lean_dec(x_1);
x_1 = x_24;
x_9 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_get_size(x_2);
x_11 = lean_nat_dec_lt(x_1, x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_2);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_fget(x_2, x_1);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_13, 2);
lean_inc(x_28);
x_42 = lean_ctor_get(x_3, 0);
lean_inc(x_42);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_array_get_size(x_27);
x_45 = lean_nat_dec_lt(x_43, x_44);
if (x_45 == 0)
{
lean_dec(x_44);
lean_dec(x_27);
x_29 = x_42;
goto block_41;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_44, x_44);
if (x_46 == 0)
{
lean_dec(x_44);
lean_dec(x_27);
x_29 = x_42;
goto block_41;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; 
x_47 = lean_usize_of_nat(x_43);
x_48 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_27, x_47, x_48, x_42);
lean_dec(x_27);
x_29 = x_49;
goto block_41;
}
}
block_41:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_ctor_get(x_3, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_3, 2);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_30);
lean_ctor_set(x_32, 2, x_31);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_33 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_28, x_32, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
lean_inc(x_13);
x_36 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_34);
x_14 = x_36;
x_15 = x_35;
goto block_26;
}
else
{
uint8_t x_37; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_37 = !lean_is_exclusive(x_33);
if (x_37 == 0)
{
return x_33;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_33, 0);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_33);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_ctor_get(x_13, 0);
lean_inc(x_50);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_51 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_50, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
lean_inc(x_13);
x_54 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_13, x_52);
x_14 = x_54;
x_15 = x_53;
goto block_26;
}
else
{
uint8_t x_55; 
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_55 = !lean_is_exclusive(x_51);
if (x_55 == 0)
{
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_51, 0);
x_57 = lean_ctor_get(x_51, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_51);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
block_26:
{
size_t x_16; size_t x_17; uint8_t x_18; 
x_16 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_17 = lean_ptr_addr(x_14);
x_18 = lean_usize_dec_eq(x_16, x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_nat_add(x_1, x_19);
x_21 = lean_array_fset(x_2, x_1, x_14);
x_22 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5_spec__5(x_20, x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_14);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_1, x_23);
x_25 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at_____private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5_spec__5(x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15);
return x_25;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_141; lean_object* x_142; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
x_141 = lean_ctor_get(x_95, 3);
lean_inc(x_141);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_142 = l_Lean_Compiler_LCNF_Specialize_specializeApp_x3f(x_141, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; 
x_144 = lean_ctor_get(x_142, 1);
lean_inc(x_144);
lean_dec(x_142);
lean_inc(x_95);
x_108 = x_95;
x_109 = x_2;
x_110 = x_3;
x_111 = x_4;
x_112 = x_5;
x_113 = x_6;
x_114 = x_7;
x_115 = x_144;
goto block_140;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_ctor_get(x_143, 0);
lean_inc(x_146);
lean_dec(x_143);
lean_inc(x_95);
x_147 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_95, x_146, x_4, x_5, x_6, x_7, x_145);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
x_108 = x_148;
x_109 = x_2;
x_110 = x_3;
x_111 = x_4;
x_112 = x_5;
x_113 = x_6;
x_114 = x_7;
x_115 = x_149;
goto block_140;
}
}
else
{
uint8_t x_150; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_150 = !lean_is_exclusive(x_142);
if (x_150 == 0)
{
return x_142;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_142, 0);
x_152 = lean_ctor_get(x_142, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_142);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
block_107:
{
if (lean_obj_tag(x_98) == 0)
{
lean_object* x_99; lean_object* x_100; size_t x_101; size_t x_102; uint8_t x_103; 
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_ptr_addr(x_96);
lean_dec(x_96);
x_102 = lean_ptr_addr(x_99);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_dec(x_95);
x_87 = x_97;
x_88 = x_99;
x_89 = x_100;
x_90 = x_103;
goto block_94;
}
else
{
size_t x_104; size_t x_105; uint8_t x_106; 
x_104 = lean_ptr_addr(x_95);
lean_dec(x_95);
x_105 = lean_ptr_addr(x_97);
x_106 = lean_usize_dec_eq(x_104, x_105);
x_87 = x_97;
x_88 = x_99;
x_89 = x_100;
x_90 = x_106;
goto block_94;
}
}
else
{
lean_dec(x_97);
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_1);
return x_98;
}
}
block_140:
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_116 = lean_ctor_get(x_108, 3);
lean_inc(x_116);
lean_inc(x_109);
x_117 = l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0___redArg(x_116, x_109, x_115);
x_118 = lean_ctor_get(x_117, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = !lean_is_exclusive(x_109);
if (x_120 == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_121 = lean_ctor_get(x_109, 0);
x_122 = lean_ctor_get(x_109, 1);
x_123 = lean_ctor_get(x_108, 0);
lean_inc(x_123);
lean_inc(x_123);
x_124 = l_Lean_FVarIdSet_insert(x_121, x_123);
x_125 = lean_unbox(x_118);
lean_dec(x_118);
if (x_125 == 0)
{
lean_object* x_126; 
lean_dec(x_123);
lean_ctor_set(x_109, 0, x_124);
lean_inc(x_96);
x_126 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_96, x_109, x_110, x_111, x_112, x_113, x_114, x_119);
x_97 = x_108;
x_98 = x_126;
goto block_107;
}
else
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Lean_FVarIdSet_insert(x_122, x_123);
lean_ctor_set(x_109, 1, x_127);
lean_ctor_set(x_109, 0, x_124);
lean_inc(x_96);
x_128 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_96, x_109, x_110, x_111, x_112, x_113, x_114, x_119);
x_97 = x_108;
x_98 = x_128;
goto block_107;
}
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_129 = lean_ctor_get(x_109, 0);
x_130 = lean_ctor_get(x_109, 1);
x_131 = lean_ctor_get(x_109, 2);
lean_inc(x_131);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_109);
x_132 = lean_ctor_get(x_108, 0);
lean_inc(x_132);
lean_inc(x_132);
x_133 = l_Lean_FVarIdSet_insert(x_129, x_132);
x_134 = lean_unbox(x_118);
lean_dec(x_118);
if (x_134 == 0)
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_132);
x_135 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_130);
lean_ctor_set(x_135, 2, x_131);
lean_inc(x_96);
x_136 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_96, x_135, x_110, x_111, x_112, x_113, x_114, x_119);
x_97 = x_108;
x_98 = x_136;
goto block_107;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_137 = l_Lean_FVarIdSet_insert(x_130, x_132);
x_138 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_138, 0, x_133);
lean_ctor_set(x_138, 1, x_137);
lean_ctor_set(x_138, 2, x_131);
lean_inc(x_96);
x_139 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_96, x_138, x_110, x_111, x_112, x_113, x_114, x_119);
x_97 = x_108;
x_98 = x_139;
goto block_107;
}
}
}
}
case 1:
{
lean_object* x_154; lean_object* x_155; 
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_1, 1);
lean_inc(x_155);
x_25 = x_154;
x_26 = x_155;
x_27 = x_2;
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
goto block_86;
}
case 2:
{
lean_object* x_156; lean_object* x_157; 
x_156 = lean_ctor_get(x_1, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_1, 1);
lean_inc(x_157);
x_25 = x_156;
x_26 = x_157;
x_27 = x_2;
x_28 = x_3;
x_29 = x_4;
x_30 = x_5;
x_31 = x_6;
x_32 = x_7;
x_33 = x_8;
goto block_86;
}
case 4:
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
x_158 = lean_ctor_get(x_1, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_158, 3);
lean_inc(x_159);
x_160 = lean_unsigned_to_nat(0u);
lean_inc(x_159);
x_161 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5(x_160, x_159, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_161) == 0)
{
uint8_t x_162; 
x_162 = !lean_is_exclusive(x_161);
if (x_162 == 0)
{
lean_object* x_163; size_t x_164; size_t x_165; uint8_t x_166; 
x_163 = lean_ctor_get(x_161, 0);
x_164 = lean_ptr_addr(x_159);
lean_dec(x_159);
x_165 = lean_ptr_addr(x_163);
x_166 = lean_usize_dec_eq(x_164, x_165);
if (x_166 == 0)
{
uint8_t x_167; 
x_167 = !lean_is_exclusive(x_1);
if (x_167 == 0)
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_168 = lean_ctor_get(x_1, 0);
lean_dec(x_168);
x_169 = lean_ctor_get(x_158, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_158, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_158, 2);
lean_inc(x_171);
lean_dec(x_158);
x_172 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_172, 0, x_169);
lean_ctor_set(x_172, 1, x_170);
lean_ctor_set(x_172, 2, x_171);
lean_ctor_set(x_172, 3, x_163);
lean_ctor_set(x_1, 0, x_172);
lean_ctor_set(x_161, 0, x_1);
return x_161;
}
else
{
lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_1);
x_173 = lean_ctor_get(x_158, 0);
lean_inc(x_173);
x_174 = lean_ctor_get(x_158, 1);
lean_inc(x_174);
x_175 = lean_ctor_get(x_158, 2);
lean_inc(x_175);
lean_dec(x_158);
x_176 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_176, 0, x_173);
lean_ctor_set(x_176, 1, x_174);
lean_ctor_set(x_176, 2, x_175);
lean_ctor_set(x_176, 3, x_163);
x_177 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_161, 0, x_177);
return x_161;
}
}
else
{
lean_dec(x_163);
lean_dec(x_158);
lean_ctor_set(x_161, 0, x_1);
return x_161;
}
}
else
{
lean_object* x_178; lean_object* x_179; size_t x_180; size_t x_181; uint8_t x_182; 
x_178 = lean_ctor_get(x_161, 0);
x_179 = lean_ctor_get(x_161, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_161);
x_180 = lean_ptr_addr(x_159);
lean_dec(x_159);
x_181 = lean_ptr_addr(x_178);
x_182 = lean_usize_dec_eq(x_180, x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_183 = x_1;
} else {
 lean_dec_ref(x_1);
 x_183 = lean_box(0);
}
x_184 = lean_ctor_get(x_158, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_158, 1);
lean_inc(x_185);
x_186 = lean_ctor_get(x_158, 2);
lean_inc(x_186);
lean_dec(x_158);
x_187 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_187, 0, x_184);
lean_ctor_set(x_187, 1, x_185);
lean_ctor_set(x_187, 2, x_186);
lean_ctor_set(x_187, 3, x_178);
if (lean_is_scalar(x_183)) {
 x_188 = lean_alloc_ctor(4, 1, 0);
} else {
 x_188 = x_183;
}
lean_ctor_set(x_188, 0, x_187);
x_189 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_189, 0, x_188);
lean_ctor_set(x_189, 1, x_179);
return x_189;
}
else
{
lean_object* x_190; 
lean_dec(x_178);
lean_dec(x_158);
x_190 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_190, 0, x_1);
lean_ctor_set(x_190, 1, x_179);
return x_190;
}
}
}
else
{
uint8_t x_191; 
lean_dec(x_159);
lean_dec(x_158);
lean_dec(x_1);
x_191 = !lean_is_exclusive(x_161);
if (x_191 == 0)
{
return x_161;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_161, 0);
x_193 = lean_ctor_get(x_161, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_161);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
}
default: 
{
lean_object* x_195; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_195 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_195, 0, x_1);
lean_ctor_set(x_195, 1, x_8);
return x_195;
}
}
block_16:
{
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_1);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_9);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
else
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_10);
return x_15;
}
}
block_24:
{
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_17);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_19);
lean_dec(x_17);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_1);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
block_86:
{
lean_object* x_34; 
lean_inc(x_32);
lean_inc(x_31);
lean_inc(x_30);
lean_inc(x_29);
lean_inc(x_28);
lean_inc(x_27);
x_34 = l_Lean_Compiler_LCNF_Specialize_visitFunDecl(x_25, x_27, x_28, x_29, x_30, x_31, x_32, x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_35, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_27, 0);
lean_inc(x_38);
x_39 = l_Lean_FVarIdSet_insert(x_38, x_37);
x_40 = lean_ctor_get(x_27, 1);
lean_inc(x_40);
x_41 = lean_ctor_get(x_27, 2);
lean_inc(x_41);
lean_dec(x_27);
x_42 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_40);
lean_ctor_set(x_42, 2, x_41);
x_43 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_26, x_42, x_28, x_29, x_30, x_31, x_32, x_36);
if (lean_obj_tag(x_43) == 0)
{
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; size_t x_48; size_t x_49; uint8_t x_50; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = lean_ctor_get(x_1, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_1, 1);
lean_inc(x_47);
x_48 = lean_ptr_addr(x_47);
lean_dec(x_47);
x_49 = lean_ptr_addr(x_44);
x_50 = lean_usize_dec_eq(x_48, x_49);
if (x_50 == 0)
{
lean_dec(x_46);
x_9 = x_44;
x_10 = x_45;
x_11 = x_35;
x_12 = x_50;
goto block_16;
}
else
{
size_t x_51; size_t x_52; uint8_t x_53; 
x_51 = lean_ptr_addr(x_46);
lean_dec(x_46);
x_52 = lean_ptr_addr(x_35);
x_53 = lean_usize_dec_eq(x_51, x_52);
x_9 = x_44;
x_10 = x_45;
x_11 = x_35;
x_12 = x_53;
goto block_16;
}
}
case 2:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; size_t x_58; size_t x_59; uint8_t x_60; 
x_54 = lean_ctor_get(x_43, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_43, 1);
lean_inc(x_55);
lean_dec(x_43);
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_1, 1);
lean_inc(x_57);
x_58 = lean_ptr_addr(x_57);
lean_dec(x_57);
x_59 = lean_ptr_addr(x_54);
x_60 = lean_usize_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_dec(x_56);
x_17 = x_54;
x_18 = x_55;
x_19 = x_35;
x_20 = x_60;
goto block_24;
}
else
{
size_t x_61; size_t x_62; uint8_t x_63; 
x_61 = lean_ptr_addr(x_56);
lean_dec(x_56);
x_62 = lean_ptr_addr(x_35);
x_63 = lean_usize_dec_eq(x_61, x_62);
x_17 = x_54;
x_18 = x_55;
x_19 = x_35;
x_20 = x_63;
goto block_24;
}
}
default: 
{
uint8_t x_64; 
lean_dec(x_35);
lean_dec(x_1);
x_64 = !lean_is_exclusive(x_43);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_43, 0);
lean_dec(x_65);
x_66 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_67 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_68 = lean_unsigned_to_nat(305u);
x_69 = lean_unsigned_to_nat(9u);
x_70 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_71 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_66, x_67, x_68, x_69, x_70);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_66);
x_72 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_71);
lean_ctor_set(x_43, 0, x_72);
return x_43;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_73 = lean_ctor_get(x_43, 1);
lean_inc(x_73);
lean_dec(x_43);
x_74 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_75 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_76 = lean_unsigned_to_nat(305u);
x_77 = lean_unsigned_to_nat(9u);
x_78 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_79 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_74, x_75, x_76, x_77, x_78);
lean_dec(x_78);
lean_dec(x_75);
lean_dec(x_74);
x_80 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_73);
return x_81;
}
}
}
}
else
{
lean_dec(x_35);
lean_dec(x_1);
return x_43;
}
}
else
{
uint8_t x_82; 
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_1);
x_82 = !lean_is_exclusive(x_34);
if (x_82 == 0)
{
return x_34;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_34, 0);
x_84 = lean_ctor_get(x_34, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_34);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
block_94:
{
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
lean_dec(x_1);
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_87);
lean_ctor_set(x_91, 1, x_88);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_89);
return x_92;
}
else
{
lean_object* x_93; 
lean_dec(x_88);
lean_dec(x_87);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_1);
lean_ctor_set(x_93, 1, x_89);
return x_93;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_visitFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 4);
lean_inc(x_10);
x_25 = lean_ctor_get(x_2, 0);
lean_inc(x_25);
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_9);
x_28 = lean_nat_dec_lt(x_26, x_27);
if (x_28 == 0)
{
lean_dec(x_27);
x_11 = x_25;
goto block_24;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_le(x_27, x_27);
if (x_29 == 0)
{
lean_dec(x_27);
x_11 = x_25;
goto block_24;
}
else
{
size_t x_30; size_t x_31; lean_object* x_32; 
x_30 = lean_usize_of_nat(x_26);
x_31 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_32 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_9, x_30, x_31, x_25);
x_11 = x_32;
goto block_24;
}
}
block_24:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
x_13 = lean_ctor_get(x_2, 2);
lean_inc(x_13);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_12);
lean_ctor_set(x_14, 2, x_13);
lean_inc(x_5);
x_15 = l_Lean_Compiler_LCNF_Specialize_visitCode(x_10, x_14, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_1, 3);
lean_inc(x_18);
x_19 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_18, x_9, x_16, x_5, x_17);
lean_dec(x_5);
return x_19;
}
else
{
uint8_t x_20; 
lean_dec(x_9);
lean_dec(x_5);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_getSpecParamInfo_x3f___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_filterMapM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__1(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_panic___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__6___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_allFVarM___at___Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Compiler_LCNF_allFVar___at___Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Specialize_isGround___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Specialize_visitCode_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Specialize_main(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_Decl_isTemplateLike___redArg(x_1, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
lean_dec(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_ctor_get(x_1, 3);
lean_inc(x_13);
x_14 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Specialize_visitCode), 8, 0);
x_15 = lean_ctor_get(x_1, 4);
lean_inc(x_15);
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
x_46 = lean_unsigned_to_nat(0u);
x_47 = lean_array_get_size(x_13);
x_48 = lean_nat_dec_lt(x_46, x_47);
if (x_48 == 0)
{
lean_dec(x_47);
x_16 = x_45;
goto block_44;
}
else
{
uint8_t x_49; 
x_49 = lean_nat_dec_le(x_47, x_47);
if (x_49 == 0)
{
lean_dec(x_47);
x_16 = x_45;
goto block_44;
}
else
{
size_t x_50; size_t x_51; lean_object* x_52; 
x_50 = lean_usize_of_nat(x_46);
x_51 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_52 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Specialize_paramsToVarSet_spec__0(x_13, x_50, x_51, x_45);
x_16 = x_52;
goto block_44;
}
}
block_44:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
lean_dec(x_2);
x_19 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set(x_19, 2, x_18);
x_20 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Specialize_specializeApp_x3f_spec__3(x_14, x_15, x_19, x_3, x_4, x_5, x_6, x_7, x_12);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; lean_object* x_29; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_26 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_28 = lean_ctor_get(x_1, 5);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_29, 0, x_23);
lean_ctor_set(x_29, 1, x_24);
lean_ctor_set(x_29, 2, x_25);
lean_ctor_set(x_29, 3, x_13);
lean_ctor_set(x_29, 4, x_22);
lean_ctor_set(x_29, 5, x_28);
lean_ctor_set_uint8(x_29, sizeof(void*)*6, x_26);
lean_ctor_set_uint8(x_29, sizeof(void*)*6 + 1, x_27);
lean_ctor_set(x_20, 0, x_29);
return x_20;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; uint8_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_30 = lean_ctor_get(x_20, 0);
x_31 = lean_ctor_get(x_20, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_20);
x_32 = lean_ctor_get(x_1, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_1, 1);
lean_inc(x_33);
x_34 = lean_ctor_get(x_1, 2);
lean_inc(x_34);
x_35 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_36 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_37 = lean_ctor_get(x_1, 5);
lean_inc(x_37);
lean_dec(x_1);
x_38 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_38, 0, x_32);
lean_ctor_set(x_38, 1, x_33);
lean_ctor_set(x_38, 2, x_34);
lean_ctor_set(x_38, 3, x_13);
lean_ctor_set(x_38, 4, x_30);
lean_ctor_set(x_38, 5, x_37);
lean_ctor_set_uint8(x_38, sizeof(void*)*6, x_35);
lean_ctor_set_uint8(x_38, sizeof(void*)*6 + 1, x_36);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_31);
return x_39;
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_20);
if (x_40 == 0)
{
return x_20;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_20, 0);
x_42 = lean_ctor_get(x_20, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_20);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
else
{
uint8_t x_53; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_53 = !lean_is_exclusive(x_9);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_9, 0);
lean_dec(x_54);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_9, 1);
lean_inc(x_55);
lean_dec(x_9);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_specialize(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_mk_empty_array_with_capacity(x_7);
x_9 = lean_st_mk_ref(x_8, x_6);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = l_Lean_Compiler_LCNF_Specialize_paramsToVarSet(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
x_16 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_13);
lean_ctor_set(x_16, 2, x_15);
lean_inc(x_10);
x_17 = l_Lean_Compiler_LCNF_Specialize_main(x_1, x_16, x_10, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_st_ref_get(x_10, x_19);
lean_dec(x_10);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_array_push(x_22, x_18);
lean_ctor_set(x_20, 0, x_23);
return x_20;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_20, 0);
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_20);
x_26 = lean_array_push(x_24, x_18);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
lean_dec(x_10);
x_28 = !lean_is_exclusive(x_17);
if (x_28 == 0)
{
return x_17;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_17, 0);
x_30 = lean_ctor_get(x_17, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_17);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_specialize_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; uint8_t x_17; 
x_17 = lean_usize_dec_eq(x_2, x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_array_uget(x_1, x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_19 = l_Lean_Compiler_LCNF_Decl_specialize(x_18, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
lean_dec(x_19);
x_22 = l_Array_append(lean_box(0), x_4, x_20);
lean_dec(x_20);
x_10 = x_22;
x_11 = x_21;
goto block_16;
}
else
{
lean_dec(x_4);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_19, 1);
lean_inc(x_24);
lean_dec(x_19);
x_10 = x_23;
x_11 = x_24;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_19;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_9);
return x_25;
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_8 = l_Lean_Compiler_LCNF_saveSpecParamInfo(x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_8) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_10 = lean_ctor_get(x_8, 1);
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
x_12 = lean_mk_empty_array_with_capacity(x_1);
x_13 = lean_array_get_size(x_2);
x_14 = lean_nat_dec_lt(x_1, x_13);
if (x_14 == 0)
{
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_13, x_13);
if (x_15 == 0)
{
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_ctor_set(x_8, 0, x_12);
return x_8;
}
else
{
size_t x_16; size_t x_17; lean_object* x_18; 
lean_free_object(x_8);
x_16 = lean_usize_of_nat(x_1);
x_17 = lean_usize_of_nat(x_13);
lean_dec(x_13);
x_18 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_specialize_spec__0(x_2, x_16, x_17, x_12, x_3, x_4, x_5, x_6, x_10);
lean_dec(x_2);
return x_18;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
lean_dec(x_8);
x_20 = lean_mk_empty_array_with_capacity(x_1);
x_21 = lean_array_get_size(x_2);
x_22 = lean_nat_dec_lt(x_1, x_21);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_19);
return x_23;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_21, x_21);
if (x_24 == 0)
{
lean_object* x_25; 
lean_dec(x_21);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_20);
lean_ctor_set(x_25, 1, x_19);
return x_25;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
x_26 = lean_usize_of_nat(x_1);
x_27 = lean_usize_of_nat(x_21);
lean_dec(x_21);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_specialize_spec__0(x_2, x_26, x_27, x_20, x_3, x_4, x_5, x_6, x_19);
lean_dec(x_2);
return x_28;
}
}
}
}
else
{
uint8_t x_29; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_29 = !lean_is_exclusive(x_8);
if (x_29 == 0)
{
return x_8;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_8, 0);
x_31 = lean_ctor_get(x_8, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_8);
x_32 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_31);
return x_32;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_specialize() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_specialize___lam__0___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("specialize", 10, 10);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = lean_alloc_ctor(0, 3, 2);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
lean_ctor_set(x_6, 2, x_2);
x_7 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3, x_7);
x_8 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, sizeof(void*)*3 + 1, x_8);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_specialize_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_specialize_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_specialize___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_specialize___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4406_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("specialize", 10, 10);
lean_inc(x_3);
lean_inc(x_2);
x_4 = l_Lean_Name_mkStr2(x_2, x_3);
x_5 = lean_box(1);
x_6 = lean_box(0);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_7);
x_8 = l_Lean_Name_str___override(x_6, x_7);
lean_inc(x_2);
x_9 = l_Lean_Name_str___override(x_8, x_2);
x_10 = lean_mk_string_unchecked("LCNF", 4, 4);
lean_inc(x_10);
x_11 = l_Lean_Name_str___override(x_9, x_10);
x_12 = lean_mk_string_unchecked("initFn", 6, 6);
x_13 = l_Lean_Name_str___override(x_11, x_12);
x_14 = lean_mk_string_unchecked("_@", 2, 2);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_7);
lean_inc(x_2);
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("Specialize", 10, 10);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(4406u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
lean_inc(x_24);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; 
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_28 = lean_mk_string_unchecked("candidate", 9, 9);
lean_inc(x_3);
lean_inc(x_2);
x_29 = l_Lean_Name_mkStr3(x_2, x_3, x_28);
x_30 = lean_box(0);
x_31 = lean_unbox(x_30);
lean_inc(x_24);
x_32 = l_Lean_registerTraceClass(x_29, x_31, x_24, x_27);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_mk_string_unchecked("step", 4, 4);
x_35 = l_Lean_Name_mkStr3(x_2, x_3, x_34);
x_36 = lean_unbox(x_30);
x_37 = l_Lean_registerTraceClass(x_35, x_36, x_24, x_33);
return x_37;
}
else
{
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
}
else
{
lean_dec(x_24);
lean_dec(x_3);
lean_dec(x_2);
return x_26;
}
}
}
lean_object* initialize_Lean_Compiler_Specialize(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_SpecInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ToExpr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Level(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_MonadScope(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Closure(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Specialize(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_Specialize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_SpecInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ToExpr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Level(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_MonadScope(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Closure(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry = _init_l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instInhabitedCacheEntry);
if (builtin) {res = l_Lean_Compiler_LCNF_Specialize_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_49_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Compiler_LCNF_Specialize_specCacheExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_specCacheExt);
lean_dec_ref(res);
}l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM = _init_l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM();
lean_mark_persistent(l_Lean_Compiler_LCNF_Specialize_instMonadScopeSpecializeM);
l_Lean_Compiler_LCNF_specialize = _init_l_Lean_Compiler_LCNF_specialize();
lean_mark_persistent(l_Lean_Compiler_LCNF_specialize);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_Specialize___hyg_4406_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
