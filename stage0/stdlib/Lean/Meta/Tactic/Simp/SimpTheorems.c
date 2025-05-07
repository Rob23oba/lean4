// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.SimpTheorems
// Imports: Lean.ScopedEnvExtension Lean.Util.Recognizers Lean.Meta.DiscrTree Lean.Meta.AppBuilder Lean.Meta.Eqns Lean.Meta.Tactic.AuxLemma Lean.DocString Lean.PrettyPrinter
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
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___boxed(lean_object*, lean_object*);
uint8_t l_ptrEqList___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__2(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_whnf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Config_toConfigWithKey(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpEntry;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isProp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5516_;
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Meta_mkEqSymm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableOrigin___lam__0(lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isExprDefEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLemma___boxed(lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin___lam__0___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isAppOfArity(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
lean_object* l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2026_(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__5(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addGlobalInstance_spec__0___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5574_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableLtOrigin___boxed(lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableLtOrigin(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
uint8_t l_Lean_Meta_hasSmartUnfoldingDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorem;
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem;
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin;
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_logWarning___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(lean_object*, lean_object*, size_t, size_t);
lean_object* l_Lean_Meta_mkAuxLemma(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOrigin___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isErased___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLetDeclToUnfold___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkPropExt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1___boxed(lean_object*);
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getEqnsFor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkAppM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_constName_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1(lean_object*);
lean_object* l_Lean_Expr_instantiateLevelParamsArray(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_isReducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems_spec__0(lean_object*, lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpGlobalConfig;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instLTOrigin;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* l_Lean_traceBlock___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedSimpTheorems;
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConstOf(lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkForallFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_instInhabitedMetaM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT uint8_t l_Lean_Meta_instToFormatSimpTheorem___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_Meta_forallMetaTelescopeReducing(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Expr_getAppFn(lean_object*);
lean_object* l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_instInhabitedEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_converse(lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_findAsync_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0(lean_object*, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_Meta_Origin_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedOrigin;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqFalse(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_simpExtensionMapRef;
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___redArg(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_appendTR(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem;
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Meta_DiscrTree_reduceDT(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkLambdaFVars(lean_object*, lean_object*, uint8_t, uint8_t, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isConst(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isFVar(lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___lam__0___boxed(lean_object*, lean_object*);
lean_object* lean_expr_instantiate1(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
uint8_t l_Lean_Name_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object*, lean_object*);
lean_object* l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isRecursiveDefinition___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Meta_whnfR(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_instReprOrigin;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_instInhabitedOrigin() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; uint8_t x_4; uint8_t x_5; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_3, 0, x_1);
x_4 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1, x_4);
x_5 = lean_unbox(x_2);
lean_ctor_set_uint8(x_3, sizeof(void*)*1 + 1, x_5);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_27; lean_object* x_41; uint8_t x_42; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_15 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
lean_dec(x_1);
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
block_26:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_16);
if (x_15 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_mk_string_unchecked("false", 5, 5);
x_23 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_3 = x_21;
x_4 = x_17;
x_5 = x_23;
goto block_12;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_mk_string_unchecked("true", 4, 4);
x_25 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_25, 0, x_24);
x_3 = x_21;
x_4 = x_17;
x_5 = x_25;
goto block_12;
}
}
block_40:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_28 = lean_mk_string_unchecked("Lean.Meta.Origin.decl", 21, 21);
x_29 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_29, 0, x_28);
x_30 = lean_box(1);
x_31 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(1024u);
x_33 = l_Lean_Name_reprPrec(x_13, x_32);
x_34 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
if (x_14 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_mk_string_unchecked("false", 5, 5);
x_37 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_16 = x_30;
x_17 = x_27;
x_18 = x_35;
x_19 = x_37;
goto block_26;
}
else
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_mk_string_unchecked("true", 4, 4);
x_39 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_39, 0, x_38);
x_16 = x_30;
x_17 = x_27;
x_18 = x_35;
x_19 = x_39;
goto block_26;
}
}
}
case 1:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_63; uint8_t x_64; 
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_48 = x_1;
} else {
 lean_dec_ref(x_1);
 x_48 = lean_box(0);
}
x_63 = lean_unsigned_to_nat(1024u);
x_64 = lean_nat_dec_le(x_63, x_2);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_to_int(x_65);
x_49 = x_66;
goto block_62;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_unsigned_to_nat(1u);
x_68 = lean_nat_to_int(x_67);
x_49 = x_68;
goto block_62;
}
block_62:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_50 = lean_mk_string_unchecked("Lean.Meta.Origin.fvar", 21, 21);
if (lean_is_scalar(x_48)) {
 x_51 = lean_alloc_ctor(3, 1, 0);
} else {
 x_51 = x_48;
 lean_ctor_set_tag(x_51, 3);
}
lean_ctor_set(x_51, 0, x_50);
x_52 = lean_box(1);
x_53 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_unsigned_to_nat(1024u);
x_55 = l_Lean_Name_reprPrec(x_47, x_54);
x_56 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_56, 0, x_53);
lean_ctor_set(x_56, 1, x_55);
x_57 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_57, 0, x_49);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_box(0);
x_59 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_59, 0, x_57);
x_60 = lean_unbox(x_58);
lean_ctor_set_uint8(x_59, sizeof(void*)*1, x_60);
x_61 = l_Repr_addAppParen(x_59, x_2);
return x_61;
}
}
case 2:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_89; uint8_t x_90; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_1, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_71 = x_1;
} else {
 lean_dec_ref(x_1);
 x_71 = lean_box(0);
}
x_89 = lean_unsigned_to_nat(1024u);
x_90 = lean_nat_dec_le(x_89, x_2);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; 
x_91 = lean_unsigned_to_nat(2u);
x_92 = lean_nat_to_int(x_91);
x_72 = x_92;
goto block_88;
}
else
{
lean_object* x_93; lean_object* x_94; 
x_93 = lean_unsigned_to_nat(1u);
x_94 = lean_nat_to_int(x_93);
x_72 = x_94;
goto block_88;
}
block_88:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_73 = lean_mk_string_unchecked("Lean.Meta.Origin.stx", 20, 20);
x_74 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_74, 0, x_73);
x_75 = lean_box(1);
if (lean_is_scalar(x_71)) {
 x_76 = lean_alloc_ctor(5, 2, 0);
} else {
 x_76 = x_71;
 lean_ctor_set_tag(x_76, 5);
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_unsigned_to_nat(1024u);
x_78 = l_Lean_Name_reprPrec(x_69, x_77);
x_79 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_80, 1, x_75);
x_81 = l___private_Init_Meta_0__Lean_Syntax_reprSyntax____x40_Init_Meta___hyg_2026_(x_70, x_77);
x_82 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_82, 0, x_80);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_83, 0, x_72);
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
default: 
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_111; uint8_t x_112; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_96 = x_1;
} else {
 lean_dec_ref(x_1);
 x_96 = lean_box(0);
}
x_111 = lean_unsigned_to_nat(1024u);
x_112 = lean_nat_dec_le(x_111, x_2);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = lean_unsigned_to_nat(2u);
x_114 = lean_nat_to_int(x_113);
x_97 = x_114;
goto block_110;
}
else
{
lean_object* x_115; lean_object* x_116; 
x_115 = lean_unsigned_to_nat(1u);
x_116 = lean_nat_to_int(x_115);
x_97 = x_116;
goto block_110;
}
block_110:
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; uint8_t x_108; lean_object* x_109; 
x_98 = lean_mk_string_unchecked("Lean.Meta.Origin.other", 22, 22);
if (lean_is_scalar(x_96)) {
 x_99 = lean_alloc_ctor(3, 1, 0);
} else {
 x_99 = x_96;
}
lean_ctor_set(x_99, 0, x_98);
x_100 = lean_box(1);
x_101 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = lean_unsigned_to_nat(1024u);
x_103 = l_Lean_Name_reprPrec(x_95, x_102);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_101);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_105, 0, x_97);
lean_ctor_set(x_105, 1, x_104);
x_106 = lean_box(0);
x_107 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_107, 0, x_105);
x_108 = lean_unbox(x_106);
lean_ctor_set_uint8(x_107, sizeof(void*)*1, x_108);
x_109 = l_Repr_addAppParen(x_107, x_2);
return x_109;
}
}
}
block_12:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; 
x_6 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_6, 0, x_3);
lean_ctor_set(x_6, 1, x_5);
x_7 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_9, 0, x_7);
x_10 = lean_unbox(x_8);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = l_Repr_addAppParen(x_9, x_2);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_instReprOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_reprOrigin____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_82____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_key___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Origin_key(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_converse(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; uint8_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*1);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_5 = x_1;
} else {
 lean_dec_ref(x_1);
 x_5 = lean_box(0);
}
if (x_4 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_6 = x_11;
goto block_9;
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
x_6 = x_13;
goto block_9;
}
block_9:
{
lean_object* x_7; lean_object* x_8; 
if (lean_is_scalar(x_5)) {
 x_7 = lean_alloc_ctor(0, 1, 2);
} else {
 x_7 = x_5;
}
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set_uint8(x_7, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_7, sizeof(void*)*1 + 1, x_6);
x_8 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
else
{
lean_object* x_14; 
lean_dec(x_1);
x_14 = lean_box(0);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqOrigin___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_11 = lean_name_eq(x_7, x_9);
if (x_11 == 0)
{
return x_11;
}
else
{
if (x_8 == 0)
{
if (x_10 == 0)
{
return x_11;
}
else
{
return x_8;
}
}
else
{
return x_10;
}
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
else
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_1, 0);
x_3 = x_16;
goto block_6;
}
}
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
}
}
static lean_object* _init_l_Lean_Meta_instBEqOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqOrigin___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqOrigin___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint64_t l_Lean_Meta_instHashableOrigin___lam__0(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
if (x_2 == 0)
{
lean_object* x_3; uint64_t x_4; lean_object* x_5; uint64_t x_6; uint64_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = l_Lean_Name_hash___override(x_3);
x_5 = lean_unsigned_to_nat(13u);
x_6 = lean_uint64_of_nat(x_5);
x_7 = lean_uint64_mix_hash(x_4, x_6);
return x_7;
}
else
{
lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = l_Lean_Name_hash___override(x_8);
x_10 = lean_unsigned_to_nat(11u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_mix_hash(x_9, x_11);
return x_12;
}
}
else
{
lean_object* x_13; uint64_t x_14; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = l_Lean_Name_hash___override(x_13);
return x_14;
}
}
}
static lean_object* _init_l_Lean_Meta_instHashableOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instHashableOrigin___lam__0___boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instHashableOrigin___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Origin_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; uint8_t x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_ctor_get_uint8(x_1, sizeof(void*)*1 + 1);
x_9 = lean_ctor_get(x_2, 0);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
x_11 = l_Lean_Name_lt(x_7, x_9);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = lean_name_eq(x_7, x_9);
if (x_12 == 0)
{
if (x_12 == 0)
{
return x_12;
}
else
{
return x_10;
}
}
else
{
if (x_8 == 0)
{
if (x_12 == 0)
{
return x_12;
}
else
{
return x_10;
}
}
else
{
if (x_11 == 0)
{
return x_11;
}
else
{
return x_10;
}
}
}
}
else
{
return x_11;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_box(1);
x_16 = lean_unbox(x_15);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_1, 0);
x_3 = x_17;
goto block_6;
}
}
block_6:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_lt(x_3, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Origin_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Origin_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instLTOrigin() {
_start:
{
lean_object* x_1; 
x_1 = lean_box(0);
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instDecidableLtOrigin(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Meta_Origin_lt(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instDecidableLtOrigin___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instDecidableLtOrigin(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorem() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; 
x_1 = l_Array_empty(lean_box(0));
x_2 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_11);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_6);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_unbox(x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_13);
x_14 = lean_unbox(x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_14);
x_15 = lean_unbox(x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 2, x_15);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 7)
{
if (lean_obj_tag(x_2) == 6)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 2);
x_7 = lean_ctor_get(x_2, 2);
lean_inc(x_7);
lean_dec(x_2);
x_1 = x_6;
x_2 = x_7;
goto _start;
}
else
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_5);
return x_10;
}
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_mk_string_unchecked("Eq", 2, 2);
lean_inc(x_11);
x_12 = l_Lean_Name_mkStr1(x_11);
x_13 = lean_unsigned_to_nat(3u);
x_14 = l_Lean_Expr_isAppOfArity(x_1, x_12, x_13);
lean_dec(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_box(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_5);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_mk_string_unchecked("refl", 4, 4);
lean_inc(x_11);
x_18 = l_Lean_Name_mkStr2(x_11, x_17);
x_19 = lean_unsigned_to_nat(2u);
x_20 = l_Lean_Expr_isAppOfArity(x_2, x_18, x_19);
lean_dec(x_18);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = lean_mk_string_unchecked("rfl", 3, 3);
x_22 = l_Lean_Name_mkStr1(x_21);
x_23 = l_Lean_Expr_isAppOfArity(x_2, x_22, x_19);
lean_dec(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_mk_string_unchecked("symm", 4, 4);
x_25 = l_Lean_Name_mkStr2(x_11, x_24);
x_26 = lean_unsigned_to_nat(4u);
x_27 = l_Lean_Expr_isAppOfArity(x_2, x_25, x_26);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = l_Lean_Expr_getAppFn(x_2);
lean_dec(x_2);
x_29 = l_Lean_Expr_isConst(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
lean_dec(x_28);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_box(x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_5);
return x_31;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = l_Lean_Expr_constName_x21(x_28);
lean_dec(x_28);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(x_32, x_3, x_4, x_5);
return x_33;
}
}
else
{
lean_object* x_34; 
x_34 = l_Lean_Expr_appArg_x21(x_2);
lean_dec(x_2);
x_2 = x_34;
goto _start;
}
}
else
{
lean_object* x_36; lean_object* x_37; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_36 = lean_box(x_14);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_5);
return x_37;
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec(x_11);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_38 = lean_box(x_14);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_5);
return x_39;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
lean_inc(x_1);
x_11 = l_Lean_Environment_findAsync_x3f(x_10, x_1, x_2);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
lean_free_object(x_6);
x_12 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = l_Lean_Expr_const___override(x_1, x_14);
x_16 = l_Lean_MessageData_ofExpr(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_mk_string_unchecked("'", 1, 1);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_20, x_3, x_4, x_9);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_1);
x_22 = lean_ctor_get(x_11, 0);
lean_inc(x_22);
lean_dec(x_11);
lean_ctor_set(x_6, 0, x_22);
return x_6;
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = lean_ctor_get(x_6, 0);
x_24 = lean_ctor_get(x_6, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_6);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_1);
x_26 = l_Lean_Environment_findAsync_x3f(x_25, x_1, x_2);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_27 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_28 = l_Lean_stringToMessageData(x_27);
lean_dec(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_1, x_29);
x_31 = l_Lean_MessageData_ofExpr(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_31);
x_33 = lean_mk_string_unchecked("'", 1, 1);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_32);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_throwError___at___Lean_throwKernelException___at___Lean_ofExceptKernelException___at___Lean_addDecl_addAsAxiom_spec__0_spec__0_spec__0___redArg(x_35, x_3, x_4, x_24);
return x_36;
}
else
{
lean_object* x_37; lean_object* x_38; 
lean_dec(x_1);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
lean_dec(x_26);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_24);
return x_38;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(x_1, x_6, x_2, x_3, x_4);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
x_10 = lean_box(x_9);
if (lean_obj_tag(x_10) == 1)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_ctor_get(x_8, 2);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_mk_string_unchecked("isRflTheorem theorem body", 25, 25);
lean_inc(x_3);
lean_inc(x_2);
x_14 = l_Lean_traceBlock___redArg(x_13, x_12, x_2, x_3, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 2)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_18, 2);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(x_19, x_20, x_2, x_3, x_16);
lean_dec(x_19);
return x_21;
}
else
{
uint8_t x_22; 
lean_dec(x_15);
lean_dec(x_3);
lean_dec(x_2);
x_22 = !lean_is_exclusive(x_14);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_14, 0);
lean_dec(x_23);
lean_ctor_set(x_14, 0, x_5);
return x_14;
}
else
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_14, 1);
lean_inc(x_24);
lean_dec(x_14);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_5);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
uint8_t x_26; 
lean_dec(x_3);
lean_dec(x_2);
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
else
{
uint8_t x_30; 
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_3);
lean_dec(x_2);
x_30 = !lean_is_exclusive(x_7);
if (x_30 == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_7, 0);
lean_dec(x_31);
lean_ctor_set(x_7, 0, x_5);
return x_7;
}
else
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_5);
lean_ctor_set(x_33, 1, x_32);
return x_33;
}
}
}
else
{
uint8_t x_34; 
lean_dec(x_3);
lean_dec(x_2);
x_34 = !lean_is_exclusive(x_7);
if (x_34 == 0)
{
return x_7;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_7, 0);
x_36 = lean_ctor_get(x_7, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_7);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_getAsyncConstInfo___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore_spec__0(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_6 = lean_st_ref_take(x_1, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_7, 0);
lean_inc(x_9);
x_10 = l_Lean_Environment_setExporting(x_9, x_2);
lean_dec(x_9);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_7, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 3);
lean_inc(x_13);
x_14 = lean_ctor_get(x_7, 5);
lean_inc(x_14);
x_15 = lean_ctor_get(x_7, 6);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 7);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_17, 0, x_10);
lean_ctor_set(x_17, 1, x_11);
lean_ctor_set(x_17, 2, x_12);
lean_ctor_set(x_17, 3, x_13);
lean_ctor_set(x_17, 4, x_3);
lean_ctor_set(x_17, 5, x_14);
lean_ctor_set(x_17, 6, x_15);
lean_ctor_set(x_17, 7, x_16);
x_18 = lean_st_ref_set(x_1, x_17, x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_18, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_18, 0, x_21);
return x_18;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__0(x_6, x_2, x_3, x_7);
lean_dec(x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_3, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__0(x_12, x_2, x_3, x_13);
lean_dec(x_12);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_st_ref_take(x_3, x_15);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_36; 
x_18 = lean_ctor_get(x_16, 0);
x_19 = lean_ctor_get(x_16, 1);
x_20 = lean_box(0);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_unbox(x_20);
x_23 = l_Lean_Environment_setExporting(x_21, x_22);
lean_dec(x_21);
x_24 = lean_ctor_get(x_18, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_18, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_18, 3);
lean_inc(x_26);
x_27 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_inc(x_28);
lean_ctor_set(x_16, 1, x_28);
lean_ctor_set(x_16, 0, x_28);
x_29 = lean_ctor_get(x_18, 5);
lean_inc(x_29);
x_30 = lean_ctor_get(x_18, 6);
lean_inc(x_30);
x_31 = lean_ctor_get(x_18, 7);
lean_inc(x_31);
lean_dec(x_18);
lean_inc(x_16);
x_32 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_32, 0, x_23);
lean_ctor_set(x_32, 1, x_24);
lean_ctor_set(x_32, 2, x_25);
lean_ctor_set(x_32, 3, x_26);
lean_ctor_set(x_32, 4, x_16);
lean_ctor_set(x_32, 5, x_29);
lean_ctor_set(x_32, 6, x_30);
lean_ctor_set(x_32, 7, x_31);
x_33 = lean_st_ref_set(x_3, x_32, x_19);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_dec(x_9);
lean_inc(x_3);
x_36 = lean_apply_3(x_1, x_2, x_3, x_34);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_37);
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
x_40 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1(x_3, x_35, x_16, x_39, x_38);
lean_dec(x_39);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; 
x_42 = lean_ctor_get(x_40, 0);
lean_dec(x_42);
lean_ctor_set(x_40, 0, x_37);
return x_40;
}
else
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_45 = lean_ctor_get(x_36, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_36, 1);
lean_inc(x_46);
lean_dec(x_36);
x_47 = lean_box(0);
x_48 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1(x_3, x_35, x_16, x_47, x_46);
lean_dec(x_3);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set_tag(x_48, 1);
lean_ctor_set(x_48, 0, x_45);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint8_t x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; lean_object* x_72; 
x_53 = lean_ctor_get(x_16, 0);
x_54 = lean_ctor_get(x_16, 1);
lean_inc(x_54);
lean_inc(x_53);
lean_dec(x_16);
x_55 = lean_box(0);
x_56 = lean_ctor_get(x_53, 0);
lean_inc(x_56);
x_57 = lean_unbox(x_55);
x_58 = l_Lean_Environment_setExporting(x_56, x_57);
lean_dec(x_56);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
x_60 = lean_ctor_get(x_53, 2);
lean_inc(x_60);
x_61 = lean_ctor_get(x_53, 3);
lean_inc(x_61);
x_62 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_62);
lean_inc(x_63);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_63);
x_65 = lean_ctor_get(x_53, 5);
lean_inc(x_65);
x_66 = lean_ctor_get(x_53, 6);
lean_inc(x_66);
x_67 = lean_ctor_get(x_53, 7);
lean_inc(x_67);
lean_dec(x_53);
lean_inc(x_64);
x_68 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_68, 0, x_58);
lean_ctor_set(x_68, 1, x_59);
lean_ctor_set(x_68, 2, x_60);
lean_ctor_set(x_68, 3, x_61);
lean_ctor_set(x_68, 4, x_64);
lean_ctor_set(x_68, 5, x_65);
lean_ctor_set(x_68, 6, x_66);
lean_ctor_set(x_68, 7, x_67);
x_69 = lean_st_ref_set(x_3, x_68, x_54);
x_70 = lean_ctor_get(x_69, 1);
lean_inc(x_70);
lean_dec(x_69);
x_71 = lean_ctor_get_uint8(x_9, sizeof(void*)*8);
lean_dec(x_9);
lean_inc(x_3);
x_72 = lean_apply_3(x_1, x_2, x_3, x_70);
if (lean_obj_tag(x_72) == 0)
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
lean_dec(x_72);
lean_inc(x_73);
x_75 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_75, 0, x_73);
x_76 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1(x_3, x_71, x_64, x_75, x_74);
lean_dec(x_75);
lean_dec(x_3);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_78 = x_76;
} else {
 lean_dec_ref(x_76);
 x_78 = lean_box(0);
}
if (lean_is_scalar(x_78)) {
 x_79 = lean_alloc_ctor(0, 2, 0);
} else {
 x_79 = x_78;
}
lean_ctor_set(x_79, 0, x_73);
lean_ctor_set(x_79, 1, x_77);
return x_79;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_80 = lean_ctor_get(x_72, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_72, 1);
lean_inc(x_81);
lean_dec(x_72);
x_82 = lean_box(0);
x_83 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1(x_3, x_71, x_64, x_82, x_81);
lean_dec(x_3);
x_84 = lean_ctor_get(x_83, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_83)) {
 lean_ctor_release(x_83, 0);
 lean_ctor_release(x_83, 1);
 x_85 = x_83;
} else {
 lean_dec_ref(x_83);
 x_85 = lean_box(0);
}
if (lean_is_scalar(x_85)) {
 x_86 = lean_alloc_ctor(1, 2, 0);
} else {
 x_86 = x_85;
 lean_ctor_set_tag(x_86, 1);
}
lean_ctor_set(x_86, 0, x_80);
lean_ctor_set(x_86, 1, x_84);
return x_86;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore), 4, 1);
lean_closure_set(x_5, 0, x_1);
x_6 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = l_Lean_withoutExporting___at___Lean_Meta_isRflTheorem_spec__0___redArg___lam__1(x_1, x_6, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_8 = lean_st_ref_take(x_1, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
x_12 = l_Lean_Environment_setExporting(x_11, x_2);
lean_dec(x_11);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_9, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_9, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_9, 5);
lean_inc(x_16);
x_17 = lean_ctor_get(x_9, 6);
lean_inc(x_17);
x_18 = lean_ctor_get(x_9, 7);
lean_inc(x_18);
lean_dec(x_9);
x_19 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_13);
lean_ctor_set(x_19, 2, x_14);
lean_ctor_set(x_19, 3, x_15);
lean_ctor_set(x_19, 4, x_3);
lean_ctor_set(x_19, 5, x_16);
lean_ctor_set(x_19, 6, x_17);
lean_ctor_set(x_19, 7, x_18);
x_20 = lean_st_ref_set(x_1, x_19, x_10);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_st_ref_take(x_4, x_21);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 3);
lean_inc(x_27);
x_28 = lean_ctor_get(x_23, 4);
lean_inc(x_28);
lean_dec(x_23);
x_29 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_29, 0, x_25);
lean_ctor_set(x_29, 1, x_5);
lean_ctor_set(x_29, 2, x_26);
lean_ctor_set(x_29, 3, x_27);
lean_ctor_set(x_29, 4, x_28);
x_30 = lean_st_ref_set(x_4, x_29, x_24);
x_31 = !lean_is_exclusive(x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_30, 0);
lean_dec(x_32);
x_33 = lean_box(0);
lean_ctor_set(x_30, 0, x_33);
return x_30;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_30, 1);
lean_inc(x_34);
lean_dec(x_30);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_34);
return x_36;
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_7 = lean_st_ref_get(x_5, x_6);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_st_ref_get(x_5, x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_st_ref_take(x_5, x_11);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
x_16 = lean_box(0);
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
x_18 = lean_unbox(x_16);
x_19 = l_Lean_Environment_setExporting(x_17, x_18);
lean_dec(x_17);
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
x_21 = lean_ctor_get(x_14, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_14, 3);
lean_inc(x_22);
x_23 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
lean_inc(x_24);
lean_ctor_set(x_12, 1, x_24);
lean_ctor_set(x_12, 0, x_24);
x_25 = lean_ctor_get(x_14, 5);
lean_inc(x_25);
x_26 = lean_ctor_get(x_14, 6);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 7);
lean_inc(x_27);
lean_dec(x_14);
lean_inc(x_12);
x_28 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_28, 0, x_19);
lean_ctor_set(x_28, 1, x_20);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_22);
lean_ctor_set(x_28, 4, x_12);
lean_ctor_set(x_28, 5, x_25);
lean_ctor_set(x_28, 6, x_26);
lean_ctor_set(x_28, 7, x_27);
x_29 = lean_st_ref_set(x_5, x_28, x_15);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
x_31 = lean_st_ref_take(x_3, x_30);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_31, 1);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_8, 0);
lean_inc(x_34);
lean_dec(x_8);
x_35 = lean_ctor_get(x_32, 0);
lean_inc(x_35);
lean_inc(x_23);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_23);
lean_inc(x_23);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_23);
lean_inc(x_23);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_23);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_23);
lean_inc(x_39);
lean_inc(x_36);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_36);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_38);
lean_ctor_set(x_40, 3, x_36);
lean_ctor_set(x_40, 4, x_39);
lean_ctor_set(x_40, 5, x_39);
x_41 = lean_ctor_get(x_32, 2);
lean_inc(x_41);
x_42 = lean_ctor_get(x_32, 3);
lean_inc(x_42);
x_43 = lean_ctor_get(x_32, 4);
lean_inc(x_43);
lean_dec(x_32);
lean_inc(x_40);
x_44 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_44, 0, x_35);
lean_ctor_set(x_44, 1, x_40);
lean_ctor_set(x_44, 2, x_41);
lean_ctor_set(x_44, 3, x_42);
lean_ctor_set(x_44, 4, x_43);
x_45 = lean_st_ref_set(x_3, x_44, x_33);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get_uint8(x_34, sizeof(void*)*8);
lean_dec(x_34);
lean_inc(x_5);
lean_inc(x_3);
x_48 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_46);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_49);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_49);
x_52 = l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0(x_5, x_47, x_12, x_3, x_40, x_51, x_50);
lean_dec(x_51);
lean_dec(x_3);
lean_dec(x_5);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; 
x_54 = lean_ctor_get(x_52, 0);
lean_dec(x_54);
lean_ctor_set(x_52, 0, x_49);
return x_52;
}
else
{
lean_object* x_55; lean_object* x_56; 
x_55 = lean_ctor_get(x_52, 1);
lean_inc(x_55);
lean_dec(x_52);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_55);
return x_56;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_48, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_48, 1);
lean_inc(x_58);
lean_dec(x_48);
x_59 = lean_box(0);
x_60 = l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0(x_5, x_47, x_12, x_3, x_40, x_59, x_58);
lean_dec(x_3);
lean_dec(x_5);
x_61 = !lean_is_exclusive(x_60);
if (x_61 == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_60, 0);
lean_dec(x_62);
lean_ctor_set_tag(x_60, 1);
lean_ctor_set(x_60, 0, x_57);
return x_60;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_60, 1);
lean_inc(x_63);
lean_dec(x_60);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_57);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; uint8_t x_99; lean_object* x_100; 
x_65 = lean_ctor_get(x_12, 0);
x_66 = lean_ctor_get(x_12, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_12);
x_67 = lean_box(0);
x_68 = lean_ctor_get(x_65, 0);
lean_inc(x_68);
x_69 = lean_unbox(x_67);
x_70 = l_Lean_Environment_setExporting(x_68, x_69);
lean_dec(x_68);
x_71 = lean_ctor_get(x_65, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_65, 2);
lean_inc(x_72);
x_73 = lean_ctor_get(x_65, 3);
lean_inc(x_73);
x_74 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_74);
x_75 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_75, 0, x_74);
lean_inc(x_75);
x_76 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_76, 0, x_75);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_ctor_get(x_65, 5);
lean_inc(x_77);
x_78 = lean_ctor_get(x_65, 6);
lean_inc(x_78);
x_79 = lean_ctor_get(x_65, 7);
lean_inc(x_79);
lean_dec(x_65);
lean_inc(x_76);
x_80 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_80, 0, x_70);
lean_ctor_set(x_80, 1, x_71);
lean_ctor_set(x_80, 2, x_72);
lean_ctor_set(x_80, 3, x_73);
lean_ctor_set(x_80, 4, x_76);
lean_ctor_set(x_80, 5, x_77);
lean_ctor_set(x_80, 6, x_78);
lean_ctor_set(x_80, 7, x_79);
x_81 = lean_st_ref_set(x_5, x_80, x_66);
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = lean_st_ref_take(x_3, x_82);
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
x_86 = lean_ctor_get(x_8, 0);
lean_inc(x_86);
lean_dec(x_8);
x_87 = lean_ctor_get(x_84, 0);
lean_inc(x_87);
lean_inc(x_74);
x_88 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_88, 0, x_74);
lean_inc(x_74);
x_89 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_89, 0, x_74);
lean_inc(x_74);
x_90 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_90, 0, x_74);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_74);
lean_inc(x_91);
lean_inc(x_88);
x_92 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_92, 0, x_88);
lean_ctor_set(x_92, 1, x_89);
lean_ctor_set(x_92, 2, x_90);
lean_ctor_set(x_92, 3, x_88);
lean_ctor_set(x_92, 4, x_91);
lean_ctor_set(x_92, 5, x_91);
x_93 = lean_ctor_get(x_84, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_84, 3);
lean_inc(x_94);
x_95 = lean_ctor_get(x_84, 4);
lean_inc(x_95);
lean_dec(x_84);
lean_inc(x_92);
x_96 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_96, 0, x_87);
lean_ctor_set(x_96, 1, x_92);
lean_ctor_set(x_96, 2, x_93);
lean_ctor_set(x_96, 3, x_94);
lean_ctor_set(x_96, 4, x_95);
x_97 = lean_st_ref_set(x_3, x_96, x_85);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_99 = lean_ctor_get_uint8(x_86, sizeof(void*)*8);
lean_dec(x_86);
lean_inc(x_5);
lean_inc(x_3);
x_100 = lean_apply_5(x_1, x_2, x_3, x_4, x_5, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
lean_inc(x_101);
x_103 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_103, 0, x_101);
x_104 = l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0(x_5, x_99, x_76, x_3, x_92, x_103, x_102);
lean_dec(x_103);
lean_dec(x_3);
lean_dec(x_5);
x_105 = lean_ctor_get(x_104, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_104)) {
 lean_ctor_release(x_104, 0);
 lean_ctor_release(x_104, 1);
 x_106 = x_104;
} else {
 lean_dec_ref(x_104);
 x_106 = lean_box(0);
}
if (lean_is_scalar(x_106)) {
 x_107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_107 = x_106;
}
lean_ctor_set(x_107, 0, x_101);
lean_ctor_set(x_107, 1, x_105);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_108 = lean_ctor_get(x_100, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_100, 1);
lean_inc(x_109);
lean_dec(x_100);
x_110 = lean_box(0);
x_111 = l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0(x_5, x_99, x_76, x_3, x_92, x_110, x_109);
lean_dec(x_3);
lean_dec(x_5);
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
 x_114 = lean_alloc_ctor(1, 2, 0);
} else {
 x_114 = x_113;
 lean_ctor_set_tag(x_114, 1);
}
lean_ctor_set(x_114, 0, x_108);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_3);
lean_dec(x_2);
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflTheoremCore(x_7, x_4, x_5, x_6);
return x_8;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_9 = lean_infer_type(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isRflProofCore(x_10, x_1, x_4, x_5, x_11);
lean_dec(x_10);
return x_12;
}
else
{
uint8_t x_13; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_9);
if (x_13 == 0)
{
return x_9;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_9, 0);
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_9);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isRflProof(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_isRflProof___lam__0), 6, 1);
lean_closure_set(x_7, 0, x_1);
x_8 = l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l_Lean_withoutExporting___at___Lean_Meta_isRflProof_spec__0___redArg___lam__0(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instToFormatSimpTheorem___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_22; uint8_t x_26; 
x_26 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
if (x_26 == 0)
{
lean_object* x_27; 
x_27 = lean_mk_string_unchecked("", 0, 0);
x_22 = x_27;
goto block_25;
}
else
{
lean_object* x_28; 
x_28 = lean_mk_string_unchecked(":perm", 5, 5);
x_22 = x_28;
goto block_25;
}
block_21:
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Name_toString(x_4, x_6, x_1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_mk_string_unchecked(":", 1, 1);
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l___private_Init_Data_Repr_0__Nat_reprFast(x_11);
x_13 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_13, 0, x_12);
x_14 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_14, 0, x_10);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_18, 0, x_8);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_19, 0, x_3);
x_20 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
block_25:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_2, 4);
lean_inc(x_23);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_3 = x_22;
x_4 = x_24;
goto block_21;
}
}
}
static lean_object* _init_l_Lean_Meta_instToFormatSimpTheorem() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instToFormatSimpTheorem___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instToFormatSimpTheorem___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instToFormatSimpTheorem___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_instToFormatSimpTheorem___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_2, sizeof(void*)*1);
x_7 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
lean_dec(x_2);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_MessageData_ofConstName(x_5, x_9);
if (x_6 == 0)
{
if (x_7 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_mk_string_unchecked("↓ ", 4, 2);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_mk_string_unchecked("", 0, 0);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_2(x_4, lean_box(0), x_16);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_mk_string_unchecked("↓ ← ", 8, 4);
x_19 = l_Lean_stringToMessageData(x_18);
lean_dec(x_18);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_10);
x_21 = lean_mk_string_unchecked("", 0, 0);
x_22 = l_Lean_stringToMessageData(x_21);
lean_dec(x_21);
x_23 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_23, 0, x_20);
lean_ctor_set(x_23, 1, x_22);
x_24 = lean_apply_2(x_4, lean_box(0), x_23);
return x_24;
}
}
else
{
if (x_7 == 0)
{
lean_object* x_25; 
x_25 = lean_apply_2(x_4, lean_box(0), x_10);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_26 = lean_mk_string_unchecked("← ", 4, 2);
x_27 = l_Lean_stringToMessageData(x_26);
lean_dec(x_26);
x_28 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_10);
x_29 = lean_mk_string_unchecked("", 0, 0);
x_30 = l_Lean_stringToMessageData(x_29);
lean_dec(x_29);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_apply_2(x_4, lean_box(0), x_31);
return x_32;
}
}
}
case 1:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_1, 0);
lean_inc(x_33);
lean_dec(x_1);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
lean_dec(x_2);
x_36 = l_Lean_Expr_fvar___override(x_35);
x_37 = l_Lean_MessageData_ofExpr(x_36);
x_38 = lean_apply_2(x_34, lean_box(0), x_37);
return x_38;
}
case 2:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_1, 0);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_ctor_get(x_39, 1);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_MessageData_ofSyntax(x_41);
x_43 = lean_apply_2(x_40, lean_box(0), x_42);
return x_43;
}
default: 
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_ctor_get(x_44, 1);
lean_inc(x_45);
lean_dec(x_44);
x_46 = lean_ctor_get(x_2, 0);
lean_inc(x_46);
lean_dec(x_2);
x_47 = l_Lean_MessageData_ofName(x_46);
x_48 = lean_apply_2(x_45, lean_box(0), x_47);
return x_48;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppOrigin___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppOrigin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppOrigin(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_5 = lean_mk_string_unchecked(":", 1, 1);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l___private_Init_Data_Repr_0__Nat_reprFast(x_7);
x_9 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_9, 0, x_8);
x_10 = l_Lean_MessageData_ofFormat(x_9);
x_11 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_11, 0, x_6);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_mk_string_unchecked("", 0, 0);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_2);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_apply_2(x_3, lean_box(0), x_18);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*5 + 1);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 1);
lean_inc(x_6);
lean_dec(x_5);
if (x_3 == 0)
{
lean_object* x_13; 
x_13 = lean_mk_string_unchecked("", 0, 0);
x_7 = x_13;
goto block_12;
}
else
{
lean_object* x_14; 
x_14 = lean_mk_string_unchecked(":perm", 5, 5);
x_7 = x_14;
goto block_12;
}
block_12:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_inc(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_ppSimpTheorem___redArg___lam__0), 4, 3);
lean_closure_set(x_8, 0, x_2);
lean_closure_set(x_8, 1, x_7);
lean_closure_set(x_8, 2, x_6);
x_9 = lean_ctor_get(x_2, 4);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Meta_ppOrigin___redArg(x_1, x_9);
x_11 = lean_apply_4(x_4, lean_box(0), lean_box(0), x_10, x_8);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppSimpTheorem___redArg(x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_ppSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_ppSimpTheorem(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_instBEqSimpTheorem___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 2);
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_expr_eqv(x_3, x_4);
return x_5;
}
}
static lean_object* _init_l_Lean_Meta_instBEqSimpTheorem() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqSimpTheorem___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_instBEqSimpTheorem___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_instBEqSimpTheorem___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpTheorems() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___lam__0___boxed), 2, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___lam__0___boxed), 1, 0);
x_3 = l_Lean_Name_instBEq;
x_4 = l_Lean_instHashableName;
x_5 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_8 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_3, x_4);
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_5);
lean_inc(x_7);
lean_inc(x_6);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_6);
lean_ctor_set(x_10, 1, x_6);
lean_ctor_set(x_10, 2, x_7);
lean_ctor_set(x_10, 3, x_8);
lean_ctor_set(x_10, 4, x_7);
lean_ctor_set(x_10, 5, x_9);
return x_10;
}
}
static lean_object* _init_l_Lean_Meta_simpGlobalConfig() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_11; uint8_t x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; lean_object* x_25; 
x_1 = lean_box(0);
x_2 = lean_box(1);
x_3 = lean_box(2);
x_4 = lean_box(0);
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(0, 0, 18);
x_7 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 0, x_7);
x_8 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 1, x_8);
x_9 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 2, x_9);
x_10 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 3, x_10);
x_11 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 4, x_11);
x_12 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 5, x_12);
x_13 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 6, x_13);
x_14 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 7, x_14);
x_15 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 8, x_15);
x_16 = lean_unbox(x_3);
lean_ctor_set_uint8(x_6, 9, x_16);
x_17 = lean_unbox(x_4);
lean_ctor_set_uint8(x_6, 10, x_17);
x_18 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 11, x_18);
x_19 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 12, x_19);
x_20 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 13, x_20);
x_21 = lean_unbox(x_5);
lean_ctor_set_uint8(x_6, 14, x_21);
x_22 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 15, x_22);
x_23 = lean_unbox(x_1);
lean_ctor_set_uint8(x_6, 16, x_23);
x_24 = lean_unbox(x_2);
lean_ctor_set_uint8(x_6, 17, x_24);
x_25 = l_Lean_Meta_Config_toConfigWithKey(x_6);
return x_25;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint64_t x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_7 = l_Lean_Meta_simpGlobalConfig;
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get_uint64(x_7, sizeof(void*)*1);
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 8);
x_11 = lean_ctor_get(x_2, 1);
x_12 = lean_ctor_get(x_2, 2);
x_13 = lean_ctor_get(x_2, 3);
x_14 = lean_ctor_get(x_2, 4);
x_15 = lean_ctor_get(x_2, 5);
x_16 = lean_ctor_get(x_2, 6);
x_17 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 9);
x_18 = lean_ctor_get_uint8(x_2, sizeof(void*)*7 + 10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_19 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_19, 0, x_8);
lean_ctor_set(x_19, 1, x_11);
lean_ctor_set(x_19, 2, x_12);
lean_ctor_set(x_19, 3, x_13);
lean_ctor_set(x_19, 4, x_14);
lean_ctor_set(x_19, 5, x_15);
lean_ctor_set(x_19, 6, x_16);
lean_ctor_set_uint64(x_19, sizeof(void*)*7, x_9);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 8, x_10);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 9, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*7 + 10, x_18);
x_20 = lean_apply_5(x_1, x_19, x_3, x_4, x_5, x_6);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint64_t x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_8 = l_Lean_Meta_simpGlobalConfig;
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_11 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = lean_ctor_get(x_3, 3);
x_15 = lean_ctor_get(x_3, 4);
x_16 = lean_ctor_get(x_3, 5);
x_17 = lean_ctor_get(x_3, 6);
x_18 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_20 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_20, 0, x_9);
lean_ctor_set(x_20, 1, x_12);
lean_ctor_set(x_20, 2, x_13);
lean_ctor_set(x_20, 3, x_14);
lean_ctor_set(x_20, 4, x_15);
lean_ctor_set(x_20, 5, x_16);
lean_ctor_set(x_20, 6, x_17);
lean_ctor_set_uint64(x_20, sizeof(void*)*7, x_10);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 8, x_11);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 9, x_18);
lean_ctor_set_uint8(x_20, sizeof(void*)*7 + 10, x_19);
x_21 = lean_apply_5(x_2, x_20, x_4, x_5, x_6, x_7);
return x_21;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_withSimpGlobalConfig___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withSimpGlobalConfig___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_withSimpGlobalConfig(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint64_t x_4; lean_object* x_8; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___lam__0___boxed), 2, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_11; 
x_11 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_11 == 0)
{
lean_object* x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
x_13 = l_Lean_Name_hash___override(x_12);
lean_dec(x_12);
x_14 = lean_unsigned_to_nat(13u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_mix_hash(x_13, x_15);
x_4 = x_16;
goto block_7;
}
else
{
lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; 
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
x_18 = l_Lean_Name_hash___override(x_17);
lean_dec(x_17);
x_19 = lean_unsigned_to_nat(11u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_mix_hash(x_18, x_20);
x_4 = x_21;
goto block_7;
}
}
else
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_2, 0);
lean_inc(x_22);
x_8 = x_22;
goto block_10;
}
block_7:
{
size_t x_5; lean_object* x_6; 
x_5 = lean_uint64_to_usize(x_4);
x_6 = l_Lean_PersistentHashMap_eraseAux___at___Lean_PersistentHashMap_erase_spec__0___redArg(x_3, x_1, x_5, x_2);
return x_6;
}
block_10:
{
uint64_t x_9; 
x_9 = l_Lean_Name_hash___override(x_8);
lean_dec(x_8);
x_4 = x_9;
goto block_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint64_t x_6; lean_object* x_12; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_instBEqOrigin___lam__0___boxed), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_instHashableOrigin___lam__0___boxed), 1, 0);
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_15; 
x_15 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_15 == 0)
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; 
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = l_Lean_Name_hash___override(x_16);
lean_dec(x_16);
x_18 = lean_unsigned_to_nat(13u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_mix_hash(x_17, x_19);
x_6 = x_20;
goto block_11;
}
else
{
lean_object* x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
x_22 = l_Lean_Name_hash___override(x_21);
lean_dec(x_21);
x_23 = lean_unsigned_to_nat(11u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_mix_hash(x_22, x_24);
x_6 = x_25;
goto block_11;
}
}
else
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_2, 0);
lean_inc(x_26);
x_12 = x_26;
goto block_14;
}
block_11:
{
size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_uint64_to_usize(x_6);
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = l_Lean_PersistentHashMap_insertAux___at___Lean_PersistentHashMap_insert_spec__0___redArg(x_4, x_5, x_1, x_7, x_9, x_2, x_3);
return x_10;
}
block_14:
{
uint64_t x_13; 
x_13 = l_Lean_Name_hash___override(x_12);
lean_dec(x_12);
x_6 = x_13;
goto block_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
x_6 = lean_box(1);
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_unbox(x_6);
lean_ctor_set_uint8(x_8, sizeof(void*)*1, x_9);
lean_ctor_set_uint8(x_8, sizeof(void*)*1 + 1, x_5);
x_10 = l_Lean_Meta_SimpTheorems_eraseCore(x_4, x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_10;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_eraseCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
lean_inc(x_2);
x_6 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_5, x_2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_box(0);
lean_inc(x_2);
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_8, x_2, x_9);
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_1, 5);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
lean_inc(x_12);
x_13 = l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0(lean_box(0), x_7, x_12);
lean_inc(x_11);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_4);
lean_ctor_set(x_14, 2, x_6);
lean_ctor_set(x_14, 3, x_13);
lean_ctor_set(x_14, 4, x_10);
lean_ctor_set(x_14, 5, x_11);
x_15 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_box(0), x_11, x_12);
lean_dec(x_12);
if (lean_obj_tag(x_15) == 0)
{
return x_14;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_array_get_size(x_16);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
return x_14;
}
else
{
uint8_t x_20; 
x_20 = lean_nat_dec_le(x_18, x_18);
if (x_20 == 0)
{
lean_dec(x_18);
lean_dec(x_16);
return x_14;
}
else
{
size_t x_21; size_t x_22; lean_object* x_23; 
x_21 = lean_usize_of_nat(x_17);
x_22 = lean_usize_of_nat(x_18);
lean_dec(x_18);
x_23 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(x_16, x_21, x_22, x_14);
lean_dec(x_16);
return x_23;
}
}
}
}
else
{
lean_object* x_24; lean_object* x_25; 
lean_dec(x_2);
x_24 = lean_ctor_get(x_1, 5);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set(x_25, 1, x_4);
lean_ctor_set(x_25, 2, x_6);
lean_ctor_set(x_25, 3, x_7);
lean_ctor_set(x_25, 4, x_10);
lean_ctor_set(x_25, 5, x_24);
return x_25;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_eraseCore_spec__2(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_8; uint8_t x_9; uint8_t x_10; lean_object* x_12; lean_object* x_13; 
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_2, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_dec(x_2);
return x_9;
}
else
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_array_fget(x_1, x_2);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_22 = lean_ctor_get(x_16, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_16, sizeof(void*)*1 + 1);
lean_dec(x_16);
x_24 = lean_name_eq(x_20, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
x_10 = x_24;
goto block_11;
}
else
{
if (x_21 == 0)
{
if (x_23 == 0)
{
x_10 = x_24;
goto block_11;
}
else
{
goto block_7;
}
}
else
{
x_10 = x_23;
goto block_11;
}
}
}
else
{
lean_dec(x_16);
goto block_7;
}
}
else
{
if (lean_obj_tag(x_16) == 0)
{
lean_dec(x_16);
goto block_7;
}
else
{
lean_object* x_25; 
x_25 = lean_ctor_get(x_3, 0);
x_17 = x_25;
goto block_19;
}
}
block_19:
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
lean_dec(x_16);
x_12 = x_17;
x_13 = x_18;
goto block_15;
}
}
block_7:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_unsigned_to_nat(1u);
x_5 = lean_nat_add(x_2, x_4);
lean_dec(x_2);
x_2 = x_5;
goto _start;
}
block_11:
{
if (x_10 == 0)
{
goto block_7;
}
else
{
lean_dec(x_2);
return x_9;
}
}
block_15:
{
uint8_t x_14; 
x_14 = lean_name_eq(x_12, x_13);
lean_dec(x_13);
x_10 = x_14;
goto block_11;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
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
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_3) == 0)
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_20; uint8_t x_21; lean_object* x_22; uint8_t x_23; uint8_t x_24; 
x_20 = lean_ctor_get(x_3, 0);
x_21 = lean_ctor_get_uint8(x_3, sizeof(void*)*1 + 1);
x_22 = lean_ctor_get(x_15, 0);
lean_inc(x_22);
x_23 = lean_ctor_get_uint8(x_15, sizeof(void*)*1 + 1);
lean_dec(x_15);
x_24 = lean_name_eq(x_20, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
return x_24;
}
else
{
if (x_21 == 0)
{
if (x_23 == 0)
{
return x_24;
}
else
{
return x_21;
}
}
else
{
return x_23;
}
}
}
else
{
lean_object* x_25; uint8_t x_26; 
lean_dec(x_15);
x_25 = lean_box(0);
x_26 = lean_unbox(x_25);
return x_26;
}
}
else
{
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_15);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_3, 0);
x_16 = x_29;
goto block_19;
}
}
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
lean_object* x_30; size_t x_31; 
x_30 = lean_ctor_get(x_14, 0);
lean_inc(x_30);
lean_dec(x_14);
x_31 = lean_usize_shift_right(x_2, x_6);
x_1 = x_30;
x_2 = x_31;
goto _start;
}
default: 
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_box(0);
x_34 = lean_unbox(x_33);
return x_34;
}
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(x_35, x_36, x_3);
lean_dec(x_35);
return x_37;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; lean_object* x_7; 
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_10; 
x_10 = lean_ctor_get_uint8(x_2, sizeof(void*)*1 + 1);
if (x_10 == 0)
{
lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = l_Lean_Name_hash___override(x_11);
x_13 = lean_unsigned_to_nat(13u);
x_14 = lean_uint64_of_nat(x_13);
x_15 = lean_uint64_mix_hash(x_12, x_14);
x_3 = x_15;
goto block_6;
}
else
{
lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = l_Lean_Name_hash___override(x_16);
x_18 = lean_unsigned_to_nat(11u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_mix_hash(x_17, x_19);
x_3 = x_20;
goto block_6;
}
}
else
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_2, 0);
x_7 = x_21;
goto block_9;
}
block_6:
{
size_t x_4; uint8_t x_5; 
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(x_1, x_4, x_2);
return x_5;
}
block_9:
{
uint64_t x_8; 
x_8 = l_Lean_Name_hash___override(x_7);
x_3 = x_8;
goto block_6;
}
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_3, x_2);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_eraseCore(x_1, x_2);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___redArg(x_1, x_4, x_3);
lean_dec(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0_spec__0(x_1, x_2, x_5, x_4);
lean_dec(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 4);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Meta_Origin_converse(x_3);
if (lean_obj_tag(x_4) == 0)
{
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
lean_dec(x_4);
x_6 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_1, 4);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_box(0);
x_5 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_SimpTheorems_eraseCore_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
lean_dec(x_4);
if (x_5 == 0)
{
lean_object* x_6; 
lean_dec(x_3);
x_6 = lean_array_push(x_1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_ctor_get(x_2, 2);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 2);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_expr_eqv(x_8, x_9);
lean_dec(x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
lean_dec(x_3);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; 
x_14 = lean_array_fset(x_1, x_3, x_2);
lean_dec(x_3);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_nat_add(x_6, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_shiftr(x_9, x_10);
lean_dec(x_9);
x_12 = lean_array_fget(x_4, x_11);
x_13 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_12, x_5);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_5, x_12);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
lean_dec(x_6);
x_15 = lean_array_get_size(x_4);
x_16 = lean_nat_dec_lt(x_11, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_3);
return x_4;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_18 = lean_ctor_get(x_12, 1);
x_19 = lean_ctor_get(x_12, 0);
lean_dec(x_19);
x_20 = lean_box(0);
x_21 = lean_array_fset(x_4, x_11, x_20);
x_22 = lean_nat_add(x_1, x_10);
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(x_2, x_3, x_22, x_18);
lean_dec(x_22);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_12, 0, x_8);
x_24 = lean_array_fset(x_21, x_11, x_12);
lean_dec(x_11);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_dec(x_12);
x_26 = lean_box(0);
x_27 = lean_array_fset(x_4, x_11, x_26);
x_28 = lean_nat_add(x_1, x_10);
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(x_2, x_3, x_28, x_25);
lean_dec(x_28);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_8);
lean_ctor_set(x_30, 1, x_29);
x_31 = lean_array_fset(x_27, x_11, x_30);
lean_dec(x_11);
return x_31;
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_8);
x_7 = x_11;
goto _start;
}
}
else
{
uint8_t x_33; 
lean_dec(x_12);
x_33 = lean_nat_dec_eq(x_11, x_6);
if (x_33 == 0)
{
lean_dec(x_8);
lean_dec(x_6);
x_6 = x_11;
goto _start;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_11);
lean_dec(x_7);
x_35 = lean_nat_add(x_1, x_10);
x_36 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(x_2, x_3, x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_8);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_nat_add(x_6, x_10);
lean_dec(x_6);
lean_inc(x_4);
x_39 = lean_array_push(x_4, x_37);
x_40 = lean_array_get_size(x_4);
lean_dec(x_4);
x_41 = l_Array_insertIdx_loop(lean_box(0), x_38, x_39, x_40);
lean_dec(x_38);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_add(x_1, x_6);
x_8 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(x_2, x_3, x_7);
lean_dec(x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 1);
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_1, x_9);
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(x_2, x_3, x_10, x_7);
lean_dec(x_10);
lean_ctor_set(x_5, 1, x_11);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_1, x_13);
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(x_2, x_3, x_14, x_12);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_array_fget(x_2, x_1);
x_7 = lean_array_get_size(x_4);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_nat_dec_eq(x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_array_fget(x_4, x_8);
x_11 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1(x_5, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1(x_10, x_5);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_13 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_box(0);
x_15 = lean_array_fset(x_4, x_8, x_14);
x_16 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_10);
x_17 = lean_array_fset(x_15, x_8, x_16);
return x_17;
}
}
else
{
if (x_11 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
lean_dec(x_10);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_nat_sub(x_7, x_18);
x_20 = lean_array_fget(x_4, x_19);
x_21 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1(x_20, x_5);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1(x_5, x_20);
if (x_22 == 0)
{
uint8_t x_23; 
x_23 = lean_nat_dec_lt(x_19, x_7);
lean_dec(x_7);
if (x_23 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_box(0);
x_25 = lean_array_fset(x_4, x_19, x_24);
x_26 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_20);
x_27 = lean_array_fset(x_25, x_19, x_26);
lean_dec(x_19);
return x_27;
}
}
else
{
if (x_21 == 0)
{
lean_object* x_28; 
lean_dec(x_20);
lean_dec(x_7);
lean_dec(x_6);
x_28 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_19);
return x_28;
}
else
{
uint8_t x_29; 
x_29 = lean_nat_dec_lt(x_19, x_7);
lean_dec(x_7);
if (x_29 == 0)
{
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_6);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_30 = lean_box(0);
x_31 = lean_array_fset(x_4, x_19, x_30);
x_32 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_20);
x_33 = lean_array_fset(x_31, x_19, x_32);
lean_dec(x_19);
return x_33;
}
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_7);
x_34 = lean_box(0);
x_35 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_34);
x_36 = lean_array_push(x_4, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = lean_nat_dec_lt(x_8, x_7);
lean_dec(x_7);
if (x_37 == 0)
{
lean_dec(x_10);
lean_dec(x_6);
lean_dec(x_3);
return x_4;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_box(0);
x_39 = lean_array_fset(x_4, x_8, x_38);
x_40 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_10);
x_41 = lean_array_fset(x_39, x_8, x_40);
return x_41;
}
}
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
lean_dec(x_10);
x_42 = lean_box(0);
x_43 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_42);
x_44 = lean_array_push(x_4, x_43);
x_45 = l_Array_insertIdx_loop(lean_box(0), x_8, x_44, x_7);
return x_45;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_7);
x_46 = lean_box(0);
x_47 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_46);
x_48 = lean_array_push(x_4, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_array_get_size(x_1);
x_9 = lean_nat_dec_lt(x_3, x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__0(x_6, x_2);
lean_ctor_set(x_4, 0, x_10);
return x_4;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_array_fget(x_1, x_3);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
lean_inc(x_13);
lean_ctor_set(x_4, 1, x_13);
lean_ctor_set(x_4, 0, x_13);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_11);
lean_ctor_set(x_14, 1, x_4);
x_15 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_7, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_6);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
lean_inc(x_18);
lean_inc(x_17);
lean_dec(x_4);
x_19 = lean_array_get_size(x_1);
x_20 = lean_nat_dec_lt(x_3, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__0(x_17, x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_23 = lean_array_fget(x_1, x_3);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_mk_empty_array_with_capacity(x_24);
lean_inc(x_25);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_23);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_18, x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Array_isEmpty___redArg(x_2);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_5 = l_Lean_Meta_DiscrTree_instInhabitedKey;
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_get(x_5, x_2, x_6);
lean_inc(x_1);
x_8 = l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_box(0), x_1, x_7);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(x_2, x_3, x_9);
x_11 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(x_1, x_7, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_unsigned_to_nat(1u);
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(x_2, x_3, x_13, x_12);
x_15 = l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(x_1, x_7, x_14);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
lean_dec(x_1);
x_16 = lean_mk_string_unchecked("Lean.Meta.DiscrTree", 19, 19);
x_17 = lean_mk_string_unchecked("Lean.Meta.DiscrTree.insertCore", 30, 30);
x_18 = lean_unsigned_to_nat(482u);
x_19 = lean_unsigned_to_nat(23u);
x_20 = lean_mk_string_unchecked("invalid key sequence", 20, 20);
x_21 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_16, x_17, x_18, x_19, x_20);
lean_dec(x_20);
lean_dec(x_17);
lean_dec(x_16);
x_22 = l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__5(x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheoremEntry(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
lean_inc(x_2);
x_3 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseFwdIfBwd(x_1, x_2);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*5);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
lean_inc(x_2);
x_7 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0(x_5, x_6, x_2);
lean_dec(x_6);
x_8 = lean_ctor_get(x_3, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_9);
x_11 = lean_ctor_get(x_3, 3);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
x_13 = lean_ctor_get(x_3, 5);
lean_inc(x_13);
lean_dec(x_3);
x_14 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_8);
lean_ctor_set(x_14, 2, x_10);
lean_ctor_set(x_14, 3, x_11);
lean_ctor_set(x_14, 4, x_12);
lean_ctor_set(x_14, 5, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_15 = lean_ctor_get(x_3, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 0);
lean_inc(x_17);
lean_inc(x_2);
x_18 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0(x_16, x_17, x_2);
lean_dec(x_17);
x_19 = lean_ctor_get(x_3, 2);
lean_inc(x_19);
x_20 = l_Lean_Meta_addSimpTheoremEntry_updateLemmaNames(x_2, x_19);
x_21 = lean_ctor_get(x_3, 3);
lean_inc(x_21);
x_22 = lean_ctor_get(x_3, 4);
lean_inc(x_22);
x_23 = lean_ctor_get(x_3, 5);
lean_inc(x_23);
lean_dec(x_3);
x_24 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_24, 0, x_15);
lean_ctor_set(x_24, 1, x_18);
lean_ctor_set(x_24, 2, x_20);
lean_ctor_set(x_24, 3, x_21);
lean_ctor_set(x_24, 4, x_22);
lean_ctor_set(x_24, 5, x_23);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addSimpTheoremEntry_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_6, x_2, x_7);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set(x_11, 5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addLetDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 2);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_6, x_2, x_7);
x_9 = lean_ctor_get(x_1, 4);
lean_inc(x_9);
x_10 = lean_ctor_get(x_1, 5);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_4);
lean_ctor_set(x_11, 2, x_5);
lean_ctor_set(x_11, 3, x_8);
lean_ctor_set(x_11, 4, x_9);
lean_ctor_set(x_11, 5, x_10);
return x_11;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLetDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheorems_isLemma(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_ctor_get(x_1, 2);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_isLemma___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheorems_isLemma(x_1, x_2);
lean_dec(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_1, 1);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 2);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 5);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_9, x_2, x_3);
x_11 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_5);
lean_ctor_set(x_11, 2, x_6);
lean_ctor_set(x_11, 3, x_7);
lean_ctor_set(x_11, 4, x_8);
lean_ctor_set(x_11, 5, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_apply_2(x_1, lean_box(0), x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_20; 
x_9 = lean_mk_string_unchecked("'", 1, 1);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_20 = lean_ctor_get(x_7, 0);
lean_inc(x_20);
lean_dec(x_7);
x_11 = x_20;
goto block_19;
block_19:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = l_Lean_MessageData_ofName(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("' does not have [simp] attribute", 32, 32);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_logWarning___redArg(x_1, x_2, x_3, x_4, x_16);
x_18 = lean_apply_4(x_5, lean_box(0), lean_box(0), x_17, x_6);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = lean_apply_1(x_1, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_Origin_converse(x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_box(0);
x_10 = lean_apply_2(x_2, lean_box(0), x_9);
x_11 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_10, x_4);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_4);
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
lean_inc(x_5);
x_13 = l_Lean_Meta_SimpTheorems_isLemma(x_5, x_12);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_12);
lean_dec(x_5);
x_14 = lean_box(0);
x_15 = lean_apply_2(x_2, lean_box(0), x_14);
x_16 = lean_apply_4(x_3, lean_box(0), lean_box(0), x_15, x_6);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
lean_dec(x_6);
lean_dec(x_3);
x_17 = l_Lean_Meta_SimpTheorems_eraseCore(x_5, x_12);
x_18 = lean_apply_2(x_2, lean_box(0), x_17);
return x_18;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_21; 
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 1);
lean_inc(x_9);
lean_dec(x_8);
lean_inc(x_5);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__0___boxed), 3, 2);
lean_closure_set(x_10, 0, x_9);
lean_closure_set(x_10, 1, x_5);
lean_inc(x_6);
lean_inc(x_7);
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___boxed), 8, 7);
lean_closure_set(x_11, 0, x_1);
lean_closure_set(x_11, 1, x_2);
lean_closure_set(x_11, 2, x_3);
lean_closure_set(x_11, 3, x_4);
lean_closure_set(x_11, 4, x_7);
lean_closure_set(x_11, 5, x_10);
lean_closure_set(x_11, 6, x_6);
x_12 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__2), 2, 1);
lean_closure_set(x_12, 0, x_11);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_7);
lean_inc(x_9);
lean_inc(x_6);
x_13 = lean_alloc_closure((void*)(l_Lean_Meta_SimpTheorems_erase___redArg___lam__4___boxed), 7, 6);
lean_closure_set(x_13, 0, x_6);
lean_closure_set(x_13, 1, x_9);
lean_closure_set(x_13, 2, x_7);
lean_closure_set(x_13, 3, x_12);
lean_closure_set(x_13, 4, x_5);
lean_closure_set(x_13, 5, x_12);
lean_inc(x_5);
x_21 = l_Lean_Meta_SimpTheorems_isLemma(x_5, x_6);
if (x_21 == 0)
{
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_6, 0);
lean_inc(x_22);
lean_inc(x_5);
x_23 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_5, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = l_Lean_Name_instBEq;
x_25 = l_Lean_instHashableName;
x_26 = lean_ctor_get(x_5, 5);
lean_inc(x_26);
x_27 = l_Lean_PersistentHashMap_contains(lean_box(0), lean_box(0), x_24, x_25, x_26, x_22);
x_14 = x_27;
goto block_20;
}
else
{
lean_dec(x_22);
x_14 = x_23;
goto block_20;
}
}
else
{
x_14 = x_21;
goto block_20;
}
}
else
{
x_14 = x_21;
goto block_20;
}
block_20:
{
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_6);
lean_dec(x_5);
x_15 = lean_box(0);
x_16 = lean_apply_2(x_9, lean_box(0), x_15);
x_17 = lean_apply_4(x_7, lean_box(0), lean_box(0), x_16, x_13);
return x_17;
}
else
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_13);
lean_dec(x_7);
x_18 = l_Lean_Meta_SimpTheorems_eraseCore(x_5, x_6);
x_19 = lean_apply_2(x_9, lean_box(0), x_18);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_erase___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__0(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_erase___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_erase___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_apply_6(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_alloc_closure((void*)(l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___lam__0), 7, 1);
lean_closure_set(x_11, 0, x_4);
x_12 = l___private_Lean_Meta_Basic_0__Lean_Meta_withLetDeclImp(lean_box(0), x_1, x_2, x_3, x_11, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_12);
if (x_17 == 0)
{
return x_12;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_12, 0);
x_19 = lean_ctor_get(x_12, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_12);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; lean_object* x_10; 
x_8 = lean_expr_eqv(x_1, x_2);
x_9 = lean_box(x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = lean_expr_instantiate1(x_2, x_3);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_2);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_2, x_6, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1___boxed), 8, 2);
lean_closure_set(x_18, 0, x_3);
lean_closure_set(x_18, 1, x_7);
x_19 = l_Lean_Meta_withLocalDeclD___at___Lean_Meta_addPPExplicitToExposeDiff_visit_spec__3(lean_box(0), x_1, x_2, x_18, x_9, x_10, x_11, x_12, x_17);
return x_19;
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_bvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_fvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_mvar___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_sort___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_const___override(x_1, x_2);
x_15 = lean_apply_7(x_3, x_14, x_4, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, uint8_t x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Lean_Expr_app___override(x_1, x_2);
x_15 = lean_apply_7(x_3, x_14, x_4, x_9, x_10, x_11, x_12, x_13);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, uint8_t x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Expr_letE___override(x_1, x_2, x_3, x_4, x_5);
x_18 = lean_apply_7(x_6, x_17, x_7, x_12, x_13, x_14, x_15, x_16);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_expr_instantiate1(x_1, x_3);
x_10 = lean_expr_instantiate1(x_2, x_3);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_14; 
x_13 = l_Lean_Expr_lit___override(x_1);
x_14 = lean_apply_7(x_2, x_13, x_3, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; 
x_15 = l_Lean_Expr_proj___override(x_1, x_2, x_3);
x_16 = lean_apply_7(x_4, x_15, x_5, x_10, x_11, x_12, x_13, x_14);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0___boxed), 7, 0);
switch (lean_obj_tag(x_1)) {
case 0:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__3(x_9, x_8, x_2, x_10, x_11, x_12, x_13, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_14;
}
case 7:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_1, 0);
lean_inc(x_15);
lean_dec(x_1);
x_16 = lean_ctor_get(x_2, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_2, 2);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_20 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__3(x_15, x_8, x_2, x_16, x_17, x_18, x_19, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
return x_20;
}
case 10:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_dec(x_8);
x_21 = lean_ctor_get(x_1, 0);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_ctor_get(x_2, 1);
lean_inc(x_22);
lean_dec(x_2);
x_23 = l_Lean_Expr_bvar___override(x_21);
x_1 = x_23;
x_2 = x_22;
goto _start;
}
default: 
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
lean_dec(x_8);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_Expr_bvar___override(x_25);
x_27 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_26, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_26);
return x_27;
}
}
}
case 1:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
lean_dec(x_1);
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__4(x_28, x_8, x_2, x_29, x_30, x_31, x_32, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
return x_33;
}
case 7:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; lean_object* x_39; 
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
lean_dec(x_1);
x_35 = lean_ctor_get(x_2, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_2, 1);
lean_inc(x_36);
x_37 = lean_ctor_get(x_2, 2);
lean_inc(x_37);
x_38 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_39 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__4(x_34, x_8, x_2, x_35, x_36, x_37, x_38, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
return x_39;
}
case 10:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
x_40 = lean_ctor_get(x_1, 0);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_ctor_get(x_2, 1);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_Expr_fvar___override(x_40);
x_1 = x_42;
x_2 = x_41;
goto _start;
}
default: 
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
lean_dec(x_8);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_Expr_fvar___override(x_44);
x_46 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_45, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_45);
return x_46;
}
}
}
case 2:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
x_47 = lean_ctor_get(x_1, 0);
lean_inc(x_47);
lean_dec(x_1);
x_48 = l_Lean_Expr_mvar___override(x_47);
x_49 = l_Lean_Meta_isExprDefEq(x_48, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_49;
}
case 6:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_1, 0);
lean_inc(x_50);
lean_dec(x_1);
x_51 = lean_ctor_get(x_2, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_2, 2);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_55 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__5(x_50, x_8, x_2, x_51, x_52, x_53, x_54, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_53);
lean_dec(x_52);
lean_dec(x_51);
return x_55;
}
case 7:
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_1, 0);
lean_inc(x_56);
lean_dec(x_1);
x_57 = lean_ctor_get(x_2, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_2, 1);
lean_inc(x_58);
x_59 = lean_ctor_get(x_2, 2);
lean_inc(x_59);
x_60 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_61 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__5(x_56, x_8, x_2, x_57, x_58, x_59, x_60, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_59);
lean_dec(x_58);
lean_dec(x_57);
return x_61;
}
case 10:
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_8);
x_62 = lean_ctor_get(x_1, 0);
lean_inc(x_62);
lean_dec(x_1);
x_63 = lean_ctor_get(x_2, 1);
lean_inc(x_63);
lean_dec(x_2);
x_64 = l_Lean_Expr_mvar___override(x_62);
x_1 = x_64;
x_2 = x_63;
goto _start;
}
default: 
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
lean_dec(x_8);
x_66 = lean_ctor_get(x_1, 0);
lean_inc(x_66);
lean_dec(x_1);
x_67 = l_Lean_Expr_mvar___override(x_66);
x_68 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_67, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_67);
return x_68;
}
}
}
case 3:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; lean_object* x_74; 
x_69 = lean_ctor_get(x_1, 0);
lean_inc(x_69);
lean_dec(x_1);
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_2, 1);
lean_inc(x_71);
x_72 = lean_ctor_get(x_2, 2);
lean_inc(x_72);
x_73 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_74 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__6(x_69, x_8, x_2, x_70, x_71, x_72, x_73, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_72);
lean_dec(x_71);
lean_dec(x_70);
return x_74;
}
case 7:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_80; 
x_75 = lean_ctor_get(x_1, 0);
lean_inc(x_75);
lean_dec(x_1);
x_76 = lean_ctor_get(x_2, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_2, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_2, 2);
lean_inc(x_78);
x_79 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_80 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__6(x_75, x_8, x_2, x_76, x_77, x_78, x_79, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
return x_80;
}
case 10:
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_8);
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec(x_1);
x_82 = lean_ctor_get(x_2, 1);
lean_inc(x_82);
lean_dec(x_2);
x_83 = l_Lean_Expr_sort___override(x_81);
x_1 = x_83;
x_2 = x_82;
goto _start;
}
default: 
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_8);
x_85 = lean_ctor_get(x_1, 0);
lean_inc(x_85);
lean_dec(x_1);
x_86 = l_Lean_Expr_sort___override(x_85);
x_87 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_86, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_86);
return x_87;
}
}
}
case 4:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_1, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_1, 1);
lean_inc(x_89);
lean_dec(x_1);
x_90 = lean_ctor_get(x_2, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_2, 1);
lean_inc(x_91);
x_92 = lean_ctor_get(x_2, 2);
lean_inc(x_92);
x_93 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_94 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__7(x_88, x_89, x_8, x_2, x_90, x_91, x_92, x_93, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_90);
return x_94;
}
case 7:
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; lean_object* x_101; 
x_95 = lean_ctor_get(x_1, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_1, 1);
lean_inc(x_96);
lean_dec(x_1);
x_97 = lean_ctor_get(x_2, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_2, 1);
lean_inc(x_98);
x_99 = lean_ctor_get(x_2, 2);
lean_inc(x_99);
x_100 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_101 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__7(x_95, x_96, x_8, x_2, x_97, x_98, x_99, x_100, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
return x_101;
}
case 10:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
lean_dec(x_8);
x_102 = lean_ctor_get(x_1, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_1, 1);
lean_inc(x_103);
lean_dec(x_1);
x_104 = lean_ctor_get(x_2, 1);
lean_inc(x_104);
lean_dec(x_2);
x_105 = l_Lean_Expr_const___override(x_102, x_103);
x_1 = x_105;
x_2 = x_104;
goto _start;
}
default: 
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; 
lean_dec(x_8);
x_107 = lean_ctor_get(x_1, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_1, 1);
lean_inc(x_108);
lean_dec(x_1);
x_109 = l_Lean_Expr_const___override(x_107, x_108);
x_110 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_109, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_109);
return x_110;
}
}
}
case 5:
{
switch (lean_obj_tag(x_2)) {
case 5:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_8);
x_111 = lean_ctor_get(x_1, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_1, 1);
lean_inc(x_112);
lean_dec(x_1);
x_113 = lean_ctor_get(x_2, 0);
lean_inc(x_113);
x_114 = lean_ctor_get(x_2, 1);
lean_inc(x_114);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_115 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_111, x_113, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_unbox(x_116);
lean_dec(x_116);
if (x_117 == 0)
{
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_115;
}
else
{
lean_object* x_118; 
x_118 = lean_ctor_get(x_115, 1);
lean_inc(x_118);
lean_dec(x_115);
x_1 = x_112;
x_2 = x_114;
x_7 = x_118;
goto _start;
}
}
else
{
lean_dec(x_114);
lean_dec(x_112);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_115;
}
}
case 6:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; 
x_120 = lean_ctor_get(x_1, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 1);
lean_inc(x_121);
lean_dec(x_1);
x_122 = lean_ctor_get(x_2, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_2, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_2, 2);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_126 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__8(x_120, x_121, x_8, x_2, x_122, x_123, x_124, x_125, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_124);
lean_dec(x_123);
lean_dec(x_122);
return x_126;
}
case 7:
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; lean_object* x_133; 
x_127 = lean_ctor_get(x_1, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_1, 1);
lean_inc(x_128);
lean_dec(x_1);
x_129 = lean_ctor_get(x_2, 0);
lean_inc(x_129);
x_130 = lean_ctor_get(x_2, 1);
lean_inc(x_130);
x_131 = lean_ctor_get(x_2, 2);
lean_inc(x_131);
x_132 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_133 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__8(x_127, x_128, x_8, x_2, x_129, x_130, x_131, x_132, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_131);
lean_dec(x_130);
lean_dec(x_129);
return x_133;
}
case 10:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_8);
x_134 = lean_ctor_get(x_1, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_1, 1);
lean_inc(x_135);
lean_dec(x_1);
x_136 = lean_ctor_get(x_2, 1);
lean_inc(x_136);
lean_dec(x_2);
x_137 = l_Lean_Expr_app___override(x_134, x_135);
x_1 = x_137;
x_2 = x_136;
goto _start;
}
default: 
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
lean_dec(x_8);
x_139 = lean_ctor_get(x_1, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_1, 1);
lean_inc(x_140);
lean_dec(x_1);
x_141 = l_Lean_Expr_app___override(x_139, x_140);
x_142 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_141, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_141);
return x_142;
}
}
}
case 6:
{
lean_dec(x_8);
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; uint8_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; uint8_t x_150; lean_object* x_151; 
x_143 = lean_ctor_get(x_1, 0);
lean_inc(x_143);
x_144 = lean_ctor_get(x_1, 1);
lean_inc(x_144);
x_145 = lean_ctor_get(x_1, 2);
lean_inc(x_145);
x_146 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_147 = lean_ctor_get(x_2, 0);
lean_inc(x_147);
x_148 = lean_ctor_get(x_2, 1);
lean_inc(x_148);
x_149 = lean_ctor_get(x_2, 2);
lean_inc(x_149);
x_150 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_151 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__2(x_143, x_144, x_145, x_146, x_147, x_148, x_149, x_150, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_147);
return x_151;
}
case 10:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_1, 0);
lean_inc(x_152);
x_153 = lean_ctor_get(x_1, 1);
lean_inc(x_153);
x_154 = lean_ctor_get(x_1, 2);
lean_inc(x_154);
x_155 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_156 = lean_ctor_get(x_2, 1);
lean_inc(x_156);
lean_dec(x_2);
x_157 = l_Lean_Expr_lam___override(x_152, x_153, x_154, x_155);
x_1 = x_157;
x_2 = x_156;
goto _start;
}
default: 
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; uint8_t x_162; lean_object* x_163; lean_object* x_164; 
x_159 = lean_ctor_get(x_1, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_1, 1);
lean_inc(x_160);
x_161 = lean_ctor_get(x_1, 2);
lean_inc(x_161);
x_162 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_163 = l_Lean_Expr_lam___override(x_159, x_160, x_161, x_162);
x_164 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_163, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_163);
return x_164;
}
}
}
case 7:
{
lean_dec(x_8);
switch (lean_obj_tag(x_2)) {
case 7:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; uint8_t x_172; lean_object* x_173; 
x_165 = lean_ctor_get(x_1, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_1, 1);
lean_inc(x_166);
x_167 = lean_ctor_get(x_1, 2);
lean_inc(x_167);
x_168 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_169 = lean_ctor_get(x_2, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_2, 1);
lean_inc(x_170);
x_171 = lean_ctor_get(x_2, 2);
lean_inc(x_171);
x_172 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_173 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__2(x_165, x_166, x_167, x_168, x_169, x_170, x_171, x_172, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_169);
return x_173;
}
case 10:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
x_174 = lean_ctor_get(x_1, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_1, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_1, 2);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_178 = lean_ctor_get(x_2, 1);
lean_inc(x_178);
lean_dec(x_2);
x_179 = l_Lean_Expr_forallE___override(x_174, x_175, x_176, x_177);
x_1 = x_179;
x_2 = x_178;
goto _start;
}
default: 
{
lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
x_181 = lean_ctor_get(x_1, 0);
lean_inc(x_181);
x_182 = lean_ctor_get(x_1, 1);
lean_inc(x_182);
x_183 = lean_ctor_get(x_1, 2);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_1, sizeof(void*)*3 + 8);
lean_dec(x_1);
x_185 = l_Lean_Expr_forallE___override(x_181, x_182, x_183, x_184);
x_186 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_185, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_185);
return x_186;
}
}
}
case 8:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint8_t x_195; lean_object* x_196; 
x_187 = lean_ctor_get(x_1, 0);
lean_inc(x_187);
x_188 = lean_ctor_get(x_1, 1);
lean_inc(x_188);
x_189 = lean_ctor_get(x_1, 2);
lean_inc(x_189);
x_190 = lean_ctor_get(x_1, 3);
lean_inc(x_190);
x_191 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_192 = lean_ctor_get(x_2, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_2, 1);
lean_inc(x_193);
x_194 = lean_ctor_get(x_2, 2);
lean_inc(x_194);
x_195 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_196 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__9(x_187, x_188, x_189, x_190, x_191, x_8, x_2, x_192, x_193, x_194, x_195, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_194);
lean_dec(x_193);
lean_dec(x_192);
return x_196;
}
case 7:
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; uint8_t x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; 
x_197 = lean_ctor_get(x_1, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_1, 1);
lean_inc(x_198);
x_199 = lean_ctor_get(x_1, 2);
lean_inc(x_199);
x_200 = lean_ctor_get(x_1, 3);
lean_inc(x_200);
x_201 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_202 = lean_ctor_get(x_2, 0);
lean_inc(x_202);
x_203 = lean_ctor_get(x_2, 1);
lean_inc(x_203);
x_204 = lean_ctor_get(x_2, 2);
lean_inc(x_204);
x_205 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_206 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__9(x_197, x_198, x_199, x_200, x_201, x_8, x_2, x_202, x_203, x_204, x_205, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_204);
lean_dec(x_203);
lean_dec(x_202);
return x_206;
}
case 8:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
lean_dec(x_8);
x_207 = lean_ctor_get(x_1, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_1, 1);
lean_inc(x_208);
x_209 = lean_ctor_get(x_1, 2);
lean_inc(x_209);
x_210 = lean_ctor_get(x_1, 3);
lean_inc(x_210);
lean_dec(x_1);
x_211 = lean_ctor_get(x_2, 1);
lean_inc(x_211);
x_212 = lean_ctor_get(x_2, 2);
lean_inc(x_212);
x_213 = lean_ctor_get(x_2, 3);
lean_inc(x_213);
lean_dec(x_2);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_208);
x_214 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_208, x_211, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; uint8_t x_216; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_unbox(x_215);
lean_dec(x_215);
if (x_216 == 0)
{
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_214;
}
else
{
lean_object* x_217; lean_object* x_218; 
x_217 = lean_ctor_get(x_214, 1);
lean_inc(x_217);
lean_dec(x_214);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_209);
x_218 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_209, x_212, x_3, x_4, x_5, x_6, x_217);
if (lean_obj_tag(x_218) == 0)
{
lean_object* x_219; uint8_t x_220; 
x_219 = lean_ctor_get(x_218, 0);
lean_inc(x_219);
x_220 = lean_unbox(x_219);
lean_dec(x_219);
if (x_220 == 0)
{
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_218;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; uint8_t x_224; lean_object* x_225; 
x_221 = lean_ctor_get(x_218, 1);
lean_inc(x_221);
lean_dec(x_218);
x_222 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__10___boxed), 8, 2);
lean_closure_set(x_222, 0, x_210);
lean_closure_set(x_222, 1, x_213);
x_223 = lean_box(0);
x_224 = lean_unbox(x_223);
x_225 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(x_207, x_208, x_209, x_222, x_224, x_3, x_4, x_5, x_6, x_221);
return x_225;
}
}
else
{
lean_dec(x_213);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_218;
}
}
}
else
{
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_208);
lean_dec(x_207);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_214;
}
}
case 10:
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; uint8_t x_230; lean_object* x_231; lean_object* x_232; 
lean_dec(x_8);
x_226 = lean_ctor_get(x_1, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_1, 1);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 2);
lean_inc(x_228);
x_229 = lean_ctor_get(x_1, 3);
lean_inc(x_229);
x_230 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_231 = lean_ctor_get(x_2, 1);
lean_inc(x_231);
lean_dec(x_2);
x_232 = l_Lean_Expr_letE___override(x_226, x_227, x_228, x_229, x_230);
x_1 = x_232;
x_2 = x_231;
goto _start;
}
default: 
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; lean_object* x_239; lean_object* x_240; 
lean_dec(x_8);
x_234 = lean_ctor_get(x_1, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_1, 1);
lean_inc(x_235);
x_236 = lean_ctor_get(x_1, 2);
lean_inc(x_236);
x_237 = lean_ctor_get(x_1, 3);
lean_inc(x_237);
x_238 = lean_ctor_get_uint8(x_1, sizeof(void*)*4 + 8);
lean_dec(x_1);
x_239 = l_Lean_Expr_letE___override(x_234, x_235, x_236, x_237, x_238);
x_240 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_239, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_239);
return x_240;
}
}
}
case 9:
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; uint8_t x_245; lean_object* x_246; 
x_241 = lean_ctor_get(x_1, 0);
lean_inc(x_241);
lean_dec(x_1);
x_242 = lean_ctor_get(x_2, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_2, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_2, 2);
lean_inc(x_244);
x_245 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_246 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__11(x_241, x_8, x_2, x_242, x_243, x_244, x_245, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_244);
lean_dec(x_243);
lean_dec(x_242);
return x_246;
}
case 7:
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; uint8_t x_251; lean_object* x_252; 
x_247 = lean_ctor_get(x_1, 0);
lean_inc(x_247);
lean_dec(x_1);
x_248 = lean_ctor_get(x_2, 0);
lean_inc(x_248);
x_249 = lean_ctor_get(x_2, 1);
lean_inc(x_249);
x_250 = lean_ctor_get(x_2, 2);
lean_inc(x_250);
x_251 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_252 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__11(x_247, x_8, x_2, x_248, x_249, x_250, x_251, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_250);
lean_dec(x_249);
lean_dec(x_248);
return x_252;
}
case 10:
{
lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_dec(x_8);
x_253 = lean_ctor_get(x_1, 0);
lean_inc(x_253);
lean_dec(x_1);
x_254 = lean_ctor_get(x_2, 1);
lean_inc(x_254);
lean_dec(x_2);
x_255 = l_Lean_Expr_lit___override(x_253);
x_1 = x_255;
x_2 = x_254;
goto _start;
}
default: 
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_8);
x_257 = lean_ctor_get(x_1, 0);
lean_inc(x_257);
lean_dec(x_1);
x_258 = l_Lean_Expr_lit___override(x_257);
x_259 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_258, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_258);
return x_259;
}
}
}
case 10:
{
lean_object* x_260; 
lean_dec(x_8);
x_260 = lean_ctor_get(x_1, 1);
lean_inc(x_260);
lean_dec(x_1);
x_1 = x_260;
goto _start;
}
default: 
{
switch (lean_obj_tag(x_2)) {
case 6:
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; uint8_t x_268; lean_object* x_269; 
x_262 = lean_ctor_get(x_1, 0);
lean_inc(x_262);
x_263 = lean_ctor_get(x_1, 1);
lean_inc(x_263);
x_264 = lean_ctor_get(x_1, 2);
lean_inc(x_264);
lean_dec(x_1);
x_265 = lean_ctor_get(x_2, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_2, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_2, 2);
lean_inc(x_267);
x_268 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_269 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__12(x_262, x_263, x_264, x_8, x_2, x_265, x_266, x_267, x_268, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_267);
lean_dec(x_266);
lean_dec(x_265);
return x_269;
}
case 7:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; uint8_t x_276; lean_object* x_277; 
x_270 = lean_ctor_get(x_1, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_1, 1);
lean_inc(x_271);
x_272 = lean_ctor_get(x_1, 2);
lean_inc(x_272);
lean_dec(x_1);
x_273 = lean_ctor_get(x_2, 0);
lean_inc(x_273);
x_274 = lean_ctor_get(x_2, 1);
lean_inc(x_274);
x_275 = lean_ctor_get(x_2, 2);
lean_inc(x_275);
x_276 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
x_277 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__12(x_270, x_271, x_272, x_8, x_2, x_273, x_274, x_275, x_276, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_275);
lean_dec(x_274);
lean_dec(x_273);
return x_277;
}
case 10:
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
lean_dec(x_8);
x_278 = lean_ctor_get(x_1, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_1, 1);
lean_inc(x_279);
x_280 = lean_ctor_get(x_1, 2);
lean_inc(x_280);
lean_dec(x_1);
x_281 = lean_ctor_get(x_2, 1);
lean_inc(x_281);
lean_dec(x_2);
x_282 = l_Lean_Expr_proj___override(x_278, x_279, x_280);
x_1 = x_282;
x_2 = x_281;
goto _start;
}
case 11:
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; uint8_t x_288; 
lean_dec(x_8);
x_284 = lean_ctor_get(x_1, 1);
lean_inc(x_284);
x_285 = lean_ctor_get(x_1, 2);
lean_inc(x_285);
lean_dec(x_1);
x_286 = lean_ctor_get(x_2, 1);
lean_inc(x_286);
x_287 = lean_ctor_get(x_2, 2);
lean_inc(x_287);
lean_dec(x_2);
x_288 = lean_nat_dec_eq(x_284, x_286);
lean_dec(x_286);
lean_dec(x_284);
if (x_288 == 0)
{
lean_object* x_289; lean_object* x_290; 
lean_dec(x_287);
lean_dec(x_285);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_289 = lean_box(x_288);
x_290 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_290, 0, x_289);
lean_ctor_set(x_290, 1, x_7);
return x_290;
}
else
{
x_1 = x_285;
x_2 = x_287;
goto _start;
}
}
default: 
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
lean_dec(x_8);
x_292 = lean_ctor_get(x_1, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_1, 1);
lean_inc(x_293);
x_294 = lean_ctor_get(x_1, 2);
lean_inc(x_294);
lean_dec(x_1);
x_295 = l_Lean_Expr_proj___override(x_292, x_293, x_294);
x_296 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_295, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_295);
return x_296;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_5);
lean_dec(x_5);
x_12 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___redArg(x_1, x_2, x_3, x_4, x_11, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_6);
lean_dec(x_6);
x_13 = l_Lean_Meta_withLetDecl___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm_spec__0(x_1, x_2, x_3, x_4, x_5, x_12, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_8);
lean_dec(x_8);
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__2(x_1, x_2, x_3, x_14, x_5, x_6, x_7, x_15, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__3(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__5(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__6(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_8);
lean_dec(x_8);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_14, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
uint8_t x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = lean_unbox(x_11);
lean_dec(x_11);
x_19 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__9(x_1, x_2, x_3, x_4, x_17, x_6, x_7, x_8, x_9, x_10, x_18, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
return x_19;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__10(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_7);
lean_dec(x_7);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__11(x_1, x_2, x_3, x_4, x_5, x_6, x_13, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; lean_object* x_16; 
x_15 = lean_unbox(x_9);
lean_dec(x_9);
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm___lam__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_15, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint64_t x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; uint8_t x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; 
x_8 = lean_box(1);
x_9 = l_Lean_Meta_simpGlobalConfig;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint64(x_9, sizeof(void*)*1);
x_12 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 8);
x_13 = lean_ctor_get(x_3, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_3, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_3, 4);
lean_inc(x_16);
x_17 = lean_ctor_get(x_3, 5);
lean_inc(x_17);
x_18 = lean_ctor_get(x_3, 6);
lean_inc(x_18);
x_19 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 9);
x_20 = lean_ctor_get_uint8(x_3, sizeof(void*)*7 + 10);
x_21 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_21, 0, x_10);
lean_ctor_set(x_21, 1, x_13);
lean_ctor_set(x_21, 2, x_14);
lean_ctor_set(x_21, 3, x_15);
lean_ctor_set(x_21, 4, x_16);
lean_ctor_set(x_21, 5, x_17);
lean_ctor_set(x_21, 6, x_18);
lean_ctor_set_uint64(x_21, sizeof(void*)*7, x_11);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 8, x_12);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 9, x_19);
lean_ctor_set_uint8(x_21, sizeof(void*)*7 + 10, x_20);
x_22 = lean_unbox(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_23 = l_Lean_Meta_DiscrTree_reduceDT(x_1, x_22, x_21, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_46; 
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
x_46 = lean_expr_eqv(x_24, x_2);
if (x_46 == 0)
{
x_27 = x_46;
goto block_45;
}
else
{
uint8_t x_47; 
x_47 = l_Lean_Expr_isFVar(x_24);
x_27 = x_47;
goto block_45;
}
block_45:
{
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_dec(x_24);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_28 = lean_box(0);
if (lean_is_scalar(x_26)) {
 x_29 = lean_alloc_ctor(0, 2, 0);
} else {
 x_29 = x_26;
}
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_25);
return x_29;
}
else
{
lean_object* x_30; 
lean_dec(x_26);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_30 = l_Lean_Meta_mkEq(x_24, x_2, x_3, x_4, x_5, x_6, x_25);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_mk_string_unchecked("invalid `simp` theorem, equation is equivalent to", 49, 49);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = l_Lean_indentExpr(x_31);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_mk_string_unchecked("", 0, 0);
x_38 = l_Lean_stringToMessageData(x_37);
lean_dec(x_37);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_39, x_3, x_4, x_5, x_6, x_32);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_40;
}
else
{
uint8_t x_41; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
return x_30;
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_42 = lean_ctor_get(x_30, 0);
x_43 = lean_ctor_get(x_30, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
return x_44;
}
}
}
}
}
else
{
uint8_t x_48; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_48 = !lean_is_exclusive(x_23);
if (x_48 == 0)
{
return x_23;
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = lean_ctor_get(x_23, 0);
x_50 = lean_ctor_get(x_23, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_23);
x_51 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_51, 0, x_49);
lean_ctor_set(x_51, 1, x_50);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_mk_string_unchecked("Eq", 2, 2);
x_9 = l_Lean_Name_mkStr1(x_8);
x_10 = lean_unsigned_to_nat(3u);
x_11 = l_Lean_Expr_isAppOfArity(x_2, x_9, x_10);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_12 = lean_box(1);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = l_Lean_Expr_appFn_x21(x_2);
x_15 = l_Lean_Expr_appArg_x21(x_14);
lean_dec(x_14);
x_16 = l_Lean_Expr_appArg_x21(x_2);
x_17 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_15, x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
lean_dec(x_19);
x_20 = lean_box(0);
lean_ctor_set(x_17, 0, x_20);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 1);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_box(0);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_21);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_17);
if (x_24 == 0)
{
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_17, 0);
x_26 = lean_ctor_get(x_17, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_17);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0___boxed), 7, 0);
x_8 = lean_box(0);
x_9 = lean_unbox(x_8);
x_10 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_1, x_7, x_9, x_2, x_3, x_4, x_5, x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = l_List_reverse___redArg(x_4);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_3);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_3, 0);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; lean_object* x_23; 
x_15 = lean_ctor_get(x_3, 1);
x_16 = lean_ctor_get(x_13, 0);
x_17 = lean_ctor_get(x_13, 1);
x_18 = lean_box(0);
x_19 = lean_box(1);
x_20 = lean_unbox(x_18);
x_21 = lean_unbox(x_18);
x_22 = lean_unbox(x_19);
x_23 = l_Lean_Meta_mkLambdaFVars(x_1, x_16, x_20, x_2, x_21, x_22, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_unbox(x_18);
x_27 = lean_unbox(x_19);
x_28 = l_Lean_Meta_mkForallFVars(x_1, x_17, x_26, x_2, x_27, x_5, x_6, x_7, x_8, x_25);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
lean_ctor_set(x_13, 1, x_29);
lean_ctor_set(x_13, 0, x_24);
lean_ctor_set(x_3, 1, x_4);
{
lean_object* _tmp_2 = x_15;
lean_object* _tmp_3 = x_3;
lean_object* _tmp_8 = x_30;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
uint8_t x_32; 
lean_dec(x_24);
lean_free_object(x_13);
lean_free_object(x_3);
lean_dec(x_15);
lean_dec(x_4);
x_32 = !lean_is_exclusive(x_28);
if (x_32 == 0)
{
return x_28;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_28, 0);
x_34 = lean_ctor_get(x_28, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_28);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_free_object(x_13);
lean_dec(x_17);
lean_free_object(x_3);
lean_dec(x_15);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_23);
if (x_36 == 0)
{
return x_23;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_3, 1);
x_41 = lean_ctor_get(x_13, 0);
x_42 = lean_ctor_get(x_13, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_13);
x_43 = lean_box(0);
x_44 = lean_box(1);
x_45 = lean_unbox(x_43);
x_46 = lean_unbox(x_43);
x_47 = lean_unbox(x_44);
x_48 = l_Lean_Meta_mkLambdaFVars(x_1, x_41, x_45, x_2, x_46, x_47, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; uint8_t x_52; lean_object* x_53; 
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_unbox(x_43);
x_52 = lean_unbox(x_44);
x_53 = l_Lean_Meta_mkForallFVars(x_1, x_42, x_51, x_2, x_52, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_53) == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_54 = lean_ctor_get(x_53, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_53, 1);
lean_inc(x_55);
lean_dec(x_53);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_49);
lean_ctor_set(x_56, 1, x_54);
lean_ctor_set(x_3, 1, x_4);
lean_ctor_set(x_3, 0, x_56);
{
lean_object* _tmp_2 = x_40;
lean_object* _tmp_3 = x_3;
lean_object* _tmp_8 = x_55;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_9 = _tmp_8;
}
goto _start;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_49);
lean_free_object(x_3);
lean_dec(x_40);
lean_dec(x_4);
x_58 = lean_ctor_get(x_53, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_53, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_53)) {
 lean_ctor_release(x_53, 0);
 lean_ctor_release(x_53, 1);
 x_60 = x_53;
} else {
 lean_dec_ref(x_53);
 x_60 = lean_box(0);
}
if (lean_is_scalar(x_60)) {
 x_61 = lean_alloc_ctor(1, 2, 0);
} else {
 x_61 = x_60;
}
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
lean_dec(x_42);
lean_free_object(x_3);
lean_dec(x_40);
lean_dec(x_4);
x_62 = lean_ctor_get(x_48, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_48, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_48)) {
 lean_ctor_release(x_48, 0);
 lean_ctor_release(x_48, 1);
 x_64 = x_48;
} else {
 lean_dec_ref(x_48);
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
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; lean_object* x_76; 
x_66 = lean_ctor_get(x_3, 0);
x_67 = lean_ctor_get(x_3, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_3);
x_68 = lean_ctor_get(x_66, 0);
lean_inc(x_68);
x_69 = lean_ctor_get(x_66, 1);
lean_inc(x_69);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_70 = x_66;
} else {
 lean_dec_ref(x_66);
 x_70 = lean_box(0);
}
x_71 = lean_box(0);
x_72 = lean_box(1);
x_73 = lean_unbox(x_71);
x_74 = lean_unbox(x_71);
x_75 = lean_unbox(x_72);
x_76 = l_Lean_Meta_mkLambdaFVars(x_1, x_68, x_73, x_2, x_74, x_75, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; uint8_t x_79; uint8_t x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_unbox(x_71);
x_80 = lean_unbox(x_72);
x_81 = l_Lean_Meta_mkForallFVars(x_1, x_69, x_79, x_2, x_80, x_5, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
if (lean_is_scalar(x_70)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_70;
}
lean_ctor_set(x_84, 0, x_77);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_4);
x_3 = x_67;
x_4 = x_85;
x_9 = x_83;
goto _start;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_77);
lean_dec(x_70);
lean_dec(x_67);
lean_dec(x_4);
x_87 = lean_ctor_get(x_81, 0);
lean_inc(x_87);
x_88 = lean_ctor_get(x_81, 1);
lean_inc(x_88);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_89 = x_81;
} else {
 lean_dec_ref(x_81);
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
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_4);
x_91 = lean_ctor_get(x_76, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_76, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_76)) {
 lean_ctor_release(x_76, 0);
 lean_ctor_release(x_76, 1);
 x_93 = x_76;
} else {
 lean_dec_ref(x_76);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; 
x_12 = l_Lean_mkAppN(x_1, x_5);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_13 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_3, x_12, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
x_17 = l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(x_5, x_4, x_14, x_16, x_7, x_8, x_9, x_10, x_15);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_17;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(uint8_t x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_whnf(x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_47; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
if (lean_is_exclusive(x_10)) {
 lean_ctor_release(x_10, 0);
 lean_ctor_release(x_10, 1);
 x_13 = x_10;
} else {
 lean_dec_ref(x_10);
 x_13 = lean_box(0);
}
x_47 = l_Lean_Expr_isForall(x_11);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_mk_string_unchecked("Eq", 2, 2);
x_49 = l_Lean_Name_mkStr1(x_48);
x_50 = lean_unsigned_to_nat(3u);
x_51 = l_Lean_Expr_isAppOfArity(x_11, x_49, x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_13);
x_52 = lean_mk_string_unchecked("Iff", 3, 3);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = lean_unsigned_to_nat(2u);
x_55 = l_Lean_Expr_isAppOfArity(x_11, x_53, x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; uint8_t x_58; 
x_56 = lean_mk_string_unchecked("Ne", 2, 2);
x_57 = l_Lean_Name_mkStr1(x_56);
x_58 = l_Lean_Expr_isAppOfArity(x_11, x_57, x_50);
lean_dec(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_59 = lean_mk_string_unchecked("Not", 3, 3);
x_60 = l_Lean_Name_mkStr1(x_59);
x_61 = lean_unsigned_to_nat(1u);
x_62 = l_Lean_Expr_isAppOfArity(x_11, x_60, x_61);
lean_dec(x_60);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; uint8_t x_65; 
lean_dec(x_49);
x_63 = lean_mk_string_unchecked("And", 3, 3);
x_64 = l_Lean_Name_mkStr1(x_63);
x_65 = l_Lean_Expr_isAppOfArity(x_11, x_64, x_54);
if (x_65 == 0)
{
lean_dec(x_64);
if (x_1 == 0)
{
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
x_18 = x_12;
goto block_46;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; uint8_t x_69; 
lean_dec(x_11);
lean_dec(x_3);
x_66 = lean_mk_string_unchecked("invalid '←' modifier in rewrite rule to 'True'", 48, 46);
x_67 = l_Lean_stringToMessageData(x_66);
lean_dec(x_66);
x_68 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_67, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
return x_68;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = lean_ctor_get(x_68, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_68);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_73 = l_Lean_Expr_appFn_x21(x_11);
x_74 = l_Lean_Expr_appArg_x21(x_73);
lean_dec(x_73);
x_75 = lean_unsigned_to_nat(0u);
lean_inc(x_3);
lean_inc(x_64);
x_76 = l_Lean_Expr_proj___override(x_64, x_75, x_3);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_77 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_76, x_74, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_77) == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_77, 1);
lean_inc(x_79);
lean_dec(x_77);
x_80 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
x_81 = l_Lean_Expr_proj___override(x_64, x_61, x_3);
x_82 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_1, x_2, x_81, x_80, x_5, x_6, x_7, x_8, x_79);
if (lean_obj_tag(x_82) == 0)
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
x_85 = l_List_appendTR(lean_box(0), x_78, x_84);
lean_ctor_set(x_82, 0, x_85);
return x_82;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_82, 0);
x_87 = lean_ctor_get(x_82, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_82);
x_88 = l_List_appendTR(lean_box(0), x_78, x_86);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
else
{
lean_dec(x_78);
return x_82;
}
}
else
{
lean_dec(x_64);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
return x_77;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_90 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
x_124 = x_5;
x_125 = x_6;
x_126 = x_7;
x_127 = x_8;
x_128 = x_12;
goto block_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; uint8_t x_204; 
lean_dec(x_90);
lean_dec(x_49);
lean_dec(x_3);
x_201 = lean_mk_string_unchecked("invalid '←' modifier in rewrite rule to 'False'", 49, 47);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
x_203 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_202, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_204 = !lean_is_exclusive(x_203);
if (x_204 == 0)
{
return x_203;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_205 = lean_ctor_get(x_203, 0);
x_206 = lean_ctor_get(x_203, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_203);
x_207 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_207, 0, x_205);
lean_ctor_set(x_207, 1, x_206);
return x_207;
}
}
block_123:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_96 = lean_mk_string_unchecked("False", 5, 5);
x_97 = l_Lean_Name_mkStr1(x_96);
x_98 = lean_box(0);
x_99 = l_Lean_Expr_const___override(x_97, x_98);
lean_inc(x_94);
lean_inc(x_93);
lean_inc(x_92);
lean_inc(x_91);
x_100 = l_Lean_Meta_mkEq(x_90, x_99, x_91, x_92, x_93, x_94, x_95);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
lean_dec(x_100);
x_103 = l_Lean_Meta_mkEqFalse(x_3, x_91, x_92, x_93, x_94, x_102);
if (lean_obj_tag(x_103) == 0)
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_105 = lean_ctor_get(x_103, 0);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_101);
x_107 = lean_box(0);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
lean_ctor_set(x_103, 0, x_108);
return x_103;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_103, 0);
x_110 = lean_ctor_get(x_103, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_103);
x_111 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_101);
x_112 = lean_box(0);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_110);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_101);
x_115 = !lean_is_exclusive(x_103);
if (x_115 == 0)
{
return x_103;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_103, 0);
x_117 = lean_ctor_get(x_103, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_103);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
uint8_t x_119; 
lean_dec(x_94);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_91);
lean_dec(x_3);
x_119 = !lean_is_exclusive(x_100);
if (x_119 == 0)
{
return x_100;
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_100, 0);
x_121 = lean_ctor_get(x_100, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_100);
x_122 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_122, 0, x_120);
lean_ctor_set(x_122, 1, x_121);
return x_122;
}
}
}
block_200:
{
uint8_t x_129; 
x_129 = l_Lean_Expr_isAppOfArity(x_90, x_49, x_50);
lean_dec(x_49);
if (x_129 == 0)
{
x_91 = x_124;
x_92 = x_125;
x_93 = x_126;
x_94 = x_127;
x_95 = x_128;
goto block_123;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; uint8_t x_136; 
x_130 = l_Lean_Expr_appFn_x21(x_90);
x_131 = l_Lean_Expr_appArg_x21(x_130);
lean_dec(x_130);
x_132 = l_Lean_Expr_appArg_x21(x_90);
x_133 = lean_mk_string_unchecked("Bool", 4, 4);
x_134 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_133);
x_135 = l_Lean_Name_mkStr2(x_133, x_134);
x_136 = l_Lean_Expr_isConstOf(x_132, x_135);
if (x_136 == 0)
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_133);
x_138 = l_Lean_Name_mkStr2(x_133, x_137);
x_139 = l_Lean_Expr_isConstOf(x_132, x_138);
lean_dec(x_138);
lean_dec(x_132);
if (x_139 == 0)
{
lean_dec(x_135);
lean_dec(x_133);
lean_dec(x_131);
x_91 = x_124;
x_92 = x_125;
x_93 = x_126;
x_94 = x_127;
x_95 = x_128;
goto block_123;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_90);
x_140 = lean_mk_string_unchecked("of_not_eq_false", 15, 15);
x_141 = l_Lean_Name_mkStr2(x_133, x_140);
x_142 = lean_mk_empty_array_with_capacity(x_61);
x_143 = lean_array_push(x_142, x_3);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
x_144 = l_Lean_Meta_mkAppM(x_141, x_143, x_124, x_125, x_126, x_127, x_128);
if (lean_obj_tag(x_144) == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_144, 1);
lean_inc(x_146);
lean_dec(x_144);
x_147 = lean_box(0);
x_148 = l_Lean_Expr_const___override(x_135, x_147);
x_149 = l_Lean_Meta_mkEq(x_131, x_148, x_124, x_125, x_126, x_127, x_146);
if (lean_obj_tag(x_149) == 0)
{
uint8_t x_150; 
x_150 = !lean_is_exclusive(x_149);
if (x_150 == 0)
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_151 = lean_ctor_get(x_149, 0);
x_152 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_152, 0, x_145);
lean_ctor_set(x_152, 1, x_151);
x_153 = lean_box(0);
x_154 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_154, 0, x_152);
lean_ctor_set(x_154, 1, x_153);
lean_ctor_set(x_149, 0, x_154);
return x_149;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_155 = lean_ctor_get(x_149, 0);
x_156 = lean_ctor_get(x_149, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_149);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_145);
lean_ctor_set(x_157, 1, x_155);
x_158 = lean_box(0);
x_159 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_159, 0, x_157);
lean_ctor_set(x_159, 1, x_158);
x_160 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_160, 0, x_159);
lean_ctor_set(x_160, 1, x_156);
return x_160;
}
}
else
{
uint8_t x_161; 
lean_dec(x_145);
x_161 = !lean_is_exclusive(x_149);
if (x_161 == 0)
{
return x_149;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_149, 0);
x_163 = lean_ctor_get(x_149, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_149);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_135);
lean_dec(x_131);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
x_165 = !lean_is_exclusive(x_144);
if (x_165 == 0)
{
return x_144;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_144, 0);
x_167 = lean_ctor_get(x_144, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_144);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_135);
lean_dec(x_132);
lean_dec(x_90);
x_169 = lean_mk_string_unchecked("of_not_eq_true", 14, 14);
lean_inc(x_133);
x_170 = l_Lean_Name_mkStr2(x_133, x_169);
x_171 = lean_mk_empty_array_with_capacity(x_61);
x_172 = lean_array_push(x_171, x_3);
lean_inc(x_127);
lean_inc(x_126);
lean_inc(x_125);
lean_inc(x_124);
x_173 = l_Lean_Meta_mkAppM(x_170, x_172, x_124, x_125, x_126, x_127, x_128);
if (lean_obj_tag(x_173) == 0)
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_174 = lean_ctor_get(x_173, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_173, 1);
lean_inc(x_175);
lean_dec(x_173);
x_176 = lean_mk_string_unchecked("false", 5, 5);
x_177 = l_Lean_Name_mkStr2(x_133, x_176);
x_178 = lean_box(0);
x_179 = l_Lean_Expr_const___override(x_177, x_178);
x_180 = l_Lean_Meta_mkEq(x_131, x_179, x_124, x_125, x_126, x_127, x_175);
if (lean_obj_tag(x_180) == 0)
{
uint8_t x_181; 
x_181 = !lean_is_exclusive(x_180);
if (x_181 == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_182 = lean_ctor_get(x_180, 0);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_174);
lean_ctor_set(x_183, 1, x_182);
x_184 = lean_box(0);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
lean_ctor_set(x_180, 0, x_185);
return x_180;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_186 = lean_ctor_get(x_180, 0);
x_187 = lean_ctor_get(x_180, 1);
lean_inc(x_187);
lean_inc(x_186);
lean_dec(x_180);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_174);
lean_ctor_set(x_188, 1, x_186);
x_189 = lean_box(0);
x_190 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_190, 0, x_188);
lean_ctor_set(x_190, 1, x_189);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_190);
lean_ctor_set(x_191, 1, x_187);
return x_191;
}
}
else
{
uint8_t x_192; 
lean_dec(x_174);
x_192 = !lean_is_exclusive(x_180);
if (x_192 == 0)
{
return x_180;
}
else
{
lean_object* x_193; lean_object* x_194; lean_object* x_195; 
x_193 = lean_ctor_get(x_180, 0);
x_194 = lean_ctor_get(x_180, 1);
lean_inc(x_194);
lean_inc(x_193);
lean_dec(x_180);
x_195 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_195, 0, x_193);
lean_ctor_set(x_195, 1, x_194);
return x_195;
}
}
}
else
{
uint8_t x_196; 
lean_dec(x_133);
lean_dec(x_131);
lean_dec(x_127);
lean_dec(x_126);
lean_dec(x_125);
lean_dec(x_124);
x_196 = !lean_is_exclusive(x_173);
if (x_196 == 0)
{
return x_173;
}
else
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_197 = lean_ctor_get(x_173, 0);
x_198 = lean_ctor_get(x_173, 1);
lean_inc(x_198);
lean_inc(x_197);
lean_dec(x_173);
x_199 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_199, 0, x_197);
lean_ctor_set(x_199, 1, x_198);
return x_199;
}
}
}
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_49);
x_208 = l_Lean_Expr_appFn_x21(x_11);
x_209 = l_Lean_Expr_appArg_x21(x_208);
lean_dec(x_208);
x_210 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_1 == 0)
{
x_211 = x_5;
x_212 = x_6;
x_213 = x_7;
x_214 = x_8;
x_215 = x_12;
goto block_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; uint8_t x_323; 
lean_dec(x_210);
lean_dec(x_209);
lean_dec(x_3);
x_320 = lean_mk_string_unchecked("invalid '←' modifier in rewrite rule to 'False'", 49, 47);
x_321 = l_Lean_stringToMessageData(x_320);
lean_dec(x_320);
x_322 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_321, x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_323 = !lean_is_exclusive(x_322);
if (x_323 == 0)
{
return x_322;
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_322, 0);
x_325 = lean_ctor_get(x_322, 1);
lean_inc(x_325);
lean_inc(x_324);
lean_dec(x_322);
x_326 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_326, 0, x_324);
lean_ctor_set(x_326, 1, x_325);
return x_326;
}
}
block_319:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; uint8_t x_219; 
x_216 = lean_mk_string_unchecked("Bool", 4, 4);
x_217 = lean_mk_string_unchecked("true", 4, 4);
lean_inc(x_216);
x_218 = l_Lean_Name_mkStr2(x_216, x_217);
x_219 = l_Lean_Expr_isConstOf(x_210, x_218);
if (x_219 == 0)
{
lean_object* x_220; lean_object* x_221; uint8_t x_222; 
x_220 = lean_mk_string_unchecked("false", 5, 5);
lean_inc(x_216);
x_221 = l_Lean_Name_mkStr2(x_216, x_220);
x_222 = l_Lean_Expr_isConstOf(x_210, x_221);
lean_dec(x_221);
if (x_222 == 0)
{
lean_object* x_223; 
lean_dec(x_218);
lean_dec(x_216);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
x_223 = l_Lean_Meta_mkEq(x_209, x_210, x_211, x_212, x_213, x_214, x_215);
if (lean_obj_tag(x_223) == 0)
{
lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; 
x_224 = lean_ctor_get(x_223, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_223, 1);
lean_inc(x_225);
lean_dec(x_223);
x_226 = lean_mk_string_unchecked("False", 5, 5);
x_227 = l_Lean_Name_mkStr1(x_226);
x_228 = lean_box(0);
x_229 = l_Lean_Expr_const___override(x_227, x_228);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
x_230 = l_Lean_Meta_mkEq(x_224, x_229, x_211, x_212, x_213, x_214, x_225);
if (lean_obj_tag(x_230) == 0)
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_231 = lean_ctor_get(x_230, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_230, 1);
lean_inc(x_232);
lean_dec(x_230);
x_233 = l_Lean_Meta_mkEqFalse(x_3, x_211, x_212, x_213, x_214, x_232);
if (lean_obj_tag(x_233) == 0)
{
uint8_t x_234; 
x_234 = !lean_is_exclusive(x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_235 = lean_ctor_get(x_233, 0);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_231);
x_237 = lean_box(0);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
lean_ctor_set(x_233, 0, x_238);
return x_233;
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
x_239 = lean_ctor_get(x_233, 0);
x_240 = lean_ctor_get(x_233, 1);
lean_inc(x_240);
lean_inc(x_239);
lean_dec(x_233);
x_241 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_241, 0, x_239);
lean_ctor_set(x_241, 1, x_231);
x_242 = lean_box(0);
x_243 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_243, 0, x_241);
lean_ctor_set(x_243, 1, x_242);
x_244 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_240);
return x_244;
}
}
else
{
uint8_t x_245; 
lean_dec(x_231);
x_245 = !lean_is_exclusive(x_233);
if (x_245 == 0)
{
return x_233;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; 
x_246 = lean_ctor_get(x_233, 0);
x_247 = lean_ctor_get(x_233, 1);
lean_inc(x_247);
lean_inc(x_246);
lean_dec(x_233);
x_248 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_248, 0, x_246);
lean_ctor_set(x_248, 1, x_247);
return x_248;
}
}
}
else
{
uint8_t x_249; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_3);
x_249 = !lean_is_exclusive(x_230);
if (x_249 == 0)
{
return x_230;
}
else
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; 
x_250 = lean_ctor_get(x_230, 0);
x_251 = lean_ctor_get(x_230, 1);
lean_inc(x_251);
lean_inc(x_250);
lean_dec(x_230);
x_252 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
return x_252;
}
}
}
else
{
uint8_t x_253; 
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_3);
x_253 = !lean_is_exclusive(x_223);
if (x_253 == 0)
{
return x_223;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_223, 0);
x_255 = lean_ctor_get(x_223, 1);
lean_inc(x_255);
lean_inc(x_254);
lean_dec(x_223);
x_256 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_256, 0, x_254);
lean_ctor_set(x_256, 1, x_255);
return x_256;
}
}
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_210);
x_257 = lean_mk_string_unchecked("of_not_eq_false", 15, 15);
x_258 = l_Lean_Name_mkStr2(x_216, x_257);
x_259 = lean_unsigned_to_nat(1u);
x_260 = lean_mk_empty_array_with_capacity(x_259);
x_261 = lean_array_push(x_260, x_3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
x_262 = l_Lean_Meta_mkAppM(x_258, x_261, x_211, x_212, x_213, x_214, x_215);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_box(0);
x_266 = l_Lean_Expr_const___override(x_218, x_265);
x_267 = l_Lean_Meta_mkEq(x_209, x_266, x_211, x_212, x_213, x_214, x_264);
if (lean_obj_tag(x_267) == 0)
{
uint8_t x_268; 
x_268 = !lean_is_exclusive(x_267);
if (x_268 == 0)
{
lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
x_269 = lean_ctor_get(x_267, 0);
x_270 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_270, 0, x_263);
lean_ctor_set(x_270, 1, x_269);
x_271 = lean_box(0);
x_272 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_272, 0, x_270);
lean_ctor_set(x_272, 1, x_271);
lean_ctor_set(x_267, 0, x_272);
return x_267;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_273 = lean_ctor_get(x_267, 0);
x_274 = lean_ctor_get(x_267, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_267);
x_275 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_275, 0, x_263);
lean_ctor_set(x_275, 1, x_273);
x_276 = lean_box(0);
x_277 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_277, 0, x_275);
lean_ctor_set(x_277, 1, x_276);
x_278 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_278, 0, x_277);
lean_ctor_set(x_278, 1, x_274);
return x_278;
}
}
else
{
uint8_t x_279; 
lean_dec(x_263);
x_279 = !lean_is_exclusive(x_267);
if (x_279 == 0)
{
return x_267;
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_280 = lean_ctor_get(x_267, 0);
x_281 = lean_ctor_get(x_267, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_267);
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
lean_dec(x_218);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_209);
x_283 = !lean_is_exclusive(x_262);
if (x_283 == 0)
{
return x_262;
}
else
{
lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_284 = lean_ctor_get(x_262, 0);
x_285 = lean_ctor_get(x_262, 1);
lean_inc(x_285);
lean_inc(x_284);
lean_dec(x_262);
x_286 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_286, 0, x_284);
lean_ctor_set(x_286, 1, x_285);
return x_286;
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
lean_dec(x_218);
lean_dec(x_210);
x_287 = lean_mk_string_unchecked("of_not_eq_true", 14, 14);
lean_inc(x_216);
x_288 = l_Lean_Name_mkStr2(x_216, x_287);
x_289 = lean_unsigned_to_nat(1u);
x_290 = lean_mk_empty_array_with_capacity(x_289);
x_291 = lean_array_push(x_290, x_3);
lean_inc(x_214);
lean_inc(x_213);
lean_inc(x_212);
lean_inc(x_211);
x_292 = l_Lean_Meta_mkAppM(x_288, x_291, x_211, x_212, x_213, x_214, x_215);
if (lean_obj_tag(x_292) == 0)
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_293 = lean_ctor_get(x_292, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_292, 1);
lean_inc(x_294);
lean_dec(x_292);
x_295 = lean_mk_string_unchecked("false", 5, 5);
x_296 = l_Lean_Name_mkStr2(x_216, x_295);
x_297 = lean_box(0);
x_298 = l_Lean_Expr_const___override(x_296, x_297);
x_299 = l_Lean_Meta_mkEq(x_209, x_298, x_211, x_212, x_213, x_214, x_294);
if (lean_obj_tag(x_299) == 0)
{
uint8_t x_300; 
x_300 = !lean_is_exclusive(x_299);
if (x_300 == 0)
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_301 = lean_ctor_get(x_299, 0);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_293);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_box(0);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
lean_ctor_set(x_299, 0, x_304);
return x_299;
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; 
x_305 = lean_ctor_get(x_299, 0);
x_306 = lean_ctor_get(x_299, 1);
lean_inc(x_306);
lean_inc(x_305);
lean_dec(x_299);
x_307 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_307, 0, x_293);
lean_ctor_set(x_307, 1, x_305);
x_308 = lean_box(0);
x_309 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_309, 0, x_307);
lean_ctor_set(x_309, 1, x_308);
x_310 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_310, 0, x_309);
lean_ctor_set(x_310, 1, x_306);
return x_310;
}
}
else
{
uint8_t x_311; 
lean_dec(x_293);
x_311 = !lean_is_exclusive(x_299);
if (x_311 == 0)
{
return x_299;
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
x_312 = lean_ctor_get(x_299, 0);
x_313 = lean_ctor_get(x_299, 1);
lean_inc(x_313);
lean_inc(x_312);
lean_dec(x_299);
x_314 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_314, 0, x_312);
lean_ctor_set(x_314, 1, x_313);
return x_314;
}
}
}
else
{
uint8_t x_315; 
lean_dec(x_216);
lean_dec(x_214);
lean_dec(x_213);
lean_dec(x_212);
lean_dec(x_211);
lean_dec(x_209);
x_315 = !lean_is_exclusive(x_292);
if (x_315 == 0)
{
return x_292;
}
else
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; 
x_316 = lean_ctor_get(x_292, 0);
x_317 = lean_ctor_get(x_292, 1);
lean_inc(x_317);
lean_inc(x_316);
lean_dec(x_292);
x_318 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_318, 0, x_316);
lean_ctor_set(x_318, 1, x_317);
return x_318;
}
}
}
}
}
}
else
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; 
lean_dec(x_49);
x_327 = l_Lean_Expr_appFn_x21(x_11);
x_328 = l_Lean_Expr_appArg_x21(x_327);
lean_dec(x_327);
x_329 = l_Lean_Expr_appArg_x21(x_11);
lean_dec(x_11);
if (x_2 == 0)
{
x_330 = x_5;
x_331 = x_6;
x_332 = x_7;
x_333 = x_8;
x_334 = x_12;
goto block_388;
}
else
{
lean_object* x_389; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_329);
lean_inc(x_328);
x_389 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_328, x_329, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_389) == 0)
{
lean_object* x_390; 
x_390 = lean_ctor_get(x_389, 1);
lean_inc(x_390);
lean_dec(x_389);
x_330 = x_5;
x_331 = x_6;
x_332 = x_7;
x_333 = x_8;
x_334 = x_390;
goto block_388;
}
else
{
uint8_t x_391; 
lean_dec(x_329);
lean_dec(x_328);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_391 = !lean_is_exclusive(x_389);
if (x_391 == 0)
{
return x_389;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; 
x_392 = lean_ctor_get(x_389, 0);
x_393 = lean_ctor_get(x_389, 1);
lean_inc(x_393);
lean_inc(x_392);
lean_dec(x_389);
x_394 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_394, 0, x_392);
lean_ctor_set(x_394, 1, x_393);
return x_394;
}
}
}
block_388:
{
if (x_1 == 0)
{
lean_object* x_335; 
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
x_335 = l_Lean_Meta_mkEq(x_328, x_329, x_330, x_331, x_332, x_333, x_334);
if (lean_obj_tag(x_335) == 0)
{
lean_object* x_336; lean_object* x_337; lean_object* x_338; 
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = l_Lean_Meta_mkPropExt(x_3, x_330, x_331, x_332, x_333, x_337);
if (lean_obj_tag(x_338) == 0)
{
uint8_t x_339; 
x_339 = !lean_is_exclusive(x_338);
if (x_339 == 0)
{
lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
x_340 = lean_ctor_get(x_338, 0);
x_341 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_336);
x_342 = lean_box(0);
x_343 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
lean_ctor_set(x_338, 0, x_343);
return x_338;
}
else
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; 
x_344 = lean_ctor_get(x_338, 0);
x_345 = lean_ctor_get(x_338, 1);
lean_inc(x_345);
lean_inc(x_344);
lean_dec(x_338);
x_346 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_346, 0, x_344);
lean_ctor_set(x_346, 1, x_336);
x_347 = lean_box(0);
x_348 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_348, 0, x_346);
lean_ctor_set(x_348, 1, x_347);
x_349 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_349, 0, x_348);
lean_ctor_set(x_349, 1, x_345);
return x_349;
}
}
else
{
uint8_t x_350; 
lean_dec(x_336);
x_350 = !lean_is_exclusive(x_338);
if (x_350 == 0)
{
return x_338;
}
else
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; 
x_351 = lean_ctor_get(x_338, 0);
x_352 = lean_ctor_get(x_338, 1);
lean_inc(x_352);
lean_inc(x_351);
lean_dec(x_338);
x_353 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_353, 0, x_351);
lean_ctor_set(x_353, 1, x_352);
return x_353;
}
}
}
else
{
uint8_t x_354; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_3);
x_354 = !lean_is_exclusive(x_335);
if (x_354 == 0)
{
return x_335;
}
else
{
lean_object* x_355; lean_object* x_356; lean_object* x_357; 
x_355 = lean_ctor_get(x_335, 0);
x_356 = lean_ctor_get(x_335, 1);
lean_inc(x_356);
lean_inc(x_355);
lean_dec(x_335);
x_357 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_357, 0, x_355);
lean_ctor_set(x_357, 1, x_356);
return x_357;
}
}
}
else
{
lean_object* x_358; 
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
x_358 = l_Lean_Meta_mkEq(x_329, x_328, x_330, x_331, x_332, x_333, x_334);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
lean_inc(x_333);
lean_inc(x_332);
lean_inc(x_331);
lean_inc(x_330);
x_361 = l_Lean_Meta_mkPropExt(x_3, x_330, x_331, x_332, x_333, x_360);
if (lean_obj_tag(x_361) == 0)
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_361, 0);
lean_inc(x_362);
x_363 = lean_ctor_get(x_361, 1);
lean_inc(x_363);
lean_dec(x_361);
x_364 = l_Lean_Meta_mkEqSymm(x_362, x_330, x_331, x_332, x_333, x_363);
if (lean_obj_tag(x_364) == 0)
{
uint8_t x_365; 
x_365 = !lean_is_exclusive(x_364);
if (x_365 == 0)
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; 
x_366 = lean_ctor_get(x_364, 0);
x_367 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_367, 0, x_366);
lean_ctor_set(x_367, 1, x_359);
x_368 = lean_box(0);
x_369 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
lean_ctor_set(x_364, 0, x_369);
return x_364;
}
else
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_370 = lean_ctor_get(x_364, 0);
x_371 = lean_ctor_get(x_364, 1);
lean_inc(x_371);
lean_inc(x_370);
lean_dec(x_364);
x_372 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_372, 0, x_370);
lean_ctor_set(x_372, 1, x_359);
x_373 = lean_box(0);
x_374 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_371);
return x_375;
}
}
else
{
uint8_t x_376; 
lean_dec(x_359);
x_376 = !lean_is_exclusive(x_364);
if (x_376 == 0)
{
return x_364;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_364, 0);
x_378 = lean_ctor_get(x_364, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_364);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
else
{
uint8_t x_380; 
lean_dec(x_359);
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
x_380 = !lean_is_exclusive(x_361);
if (x_380 == 0)
{
return x_361;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; 
x_381 = lean_ctor_get(x_361, 0);
x_382 = lean_ctor_get(x_361, 1);
lean_inc(x_382);
lean_inc(x_381);
lean_dec(x_361);
x_383 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_383, 0, x_381);
lean_ctor_set(x_383, 1, x_382);
return x_383;
}
}
}
else
{
uint8_t x_384; 
lean_dec(x_333);
lean_dec(x_332);
lean_dec(x_331);
lean_dec(x_330);
lean_dec(x_3);
x_384 = !lean_is_exclusive(x_358);
if (x_384 == 0)
{
return x_358;
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; 
x_385 = lean_ctor_get(x_358, 0);
x_386 = lean_ctor_get(x_358, 1);
lean_inc(x_386);
lean_inc(x_385);
lean_dec(x_358);
x_387 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_387, 0, x_385);
lean_ctor_set(x_387, 1, x_386);
return x_387;
}
}
}
}
}
}
else
{
lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; 
lean_dec(x_49);
x_395 = l_Lean_Expr_appFn_x21(x_11);
x_396 = l_Lean_Expr_appArg_x21(x_395);
lean_dec(x_395);
x_397 = l_Lean_Expr_appArg_x21(x_11);
if (x_2 == 0)
{
x_398 = x_5;
x_399 = x_6;
x_400 = x_7;
x_401 = x_8;
x_402 = x_12;
goto block_430;
}
else
{
lean_object* x_431; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_397);
lean_inc(x_396);
x_431 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkBadRewrite(x_396, x_397, x_5, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_431) == 0)
{
lean_object* x_432; 
x_432 = lean_ctor_get(x_431, 1);
lean_inc(x_432);
lean_dec(x_431);
x_398 = x_5;
x_399 = x_6;
x_400 = x_7;
x_401 = x_8;
x_402 = x_432;
goto block_430;
}
else
{
uint8_t x_433; 
lean_dec(x_397);
lean_dec(x_396);
lean_dec(x_13);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_433 = !lean_is_exclusive(x_431);
if (x_433 == 0)
{
return x_431;
}
else
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; 
x_434 = lean_ctor_get(x_431, 0);
x_435 = lean_ctor_get(x_431, 1);
lean_inc(x_435);
lean_inc(x_434);
lean_dec(x_431);
x_436 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
return x_436;
}
}
}
block_430:
{
if (x_1 == 0)
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_397);
lean_dec(x_396);
x_403 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_403, 0, x_3);
lean_ctor_set(x_403, 1, x_11);
x_404 = lean_box(0);
x_405 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_405, 0, x_403);
lean_ctor_set(x_405, 1, x_404);
if (lean_is_scalar(x_13)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_13;
}
lean_ctor_set(x_406, 0, x_405);
lean_ctor_set(x_406, 1, x_402);
return x_406;
}
else
{
lean_object* x_407; 
lean_dec(x_13);
lean_dec(x_11);
lean_inc(x_401);
lean_inc(x_400);
lean_inc(x_399);
lean_inc(x_398);
x_407 = l_Lean_Meta_mkEq(x_397, x_396, x_398, x_399, x_400, x_401, x_402);
if (lean_obj_tag(x_407) == 0)
{
lean_object* x_408; lean_object* x_409; lean_object* x_410; 
x_408 = lean_ctor_get(x_407, 0);
lean_inc(x_408);
x_409 = lean_ctor_get(x_407, 1);
lean_inc(x_409);
lean_dec(x_407);
x_410 = l_Lean_Meta_mkEqSymm(x_3, x_398, x_399, x_400, x_401, x_409);
if (lean_obj_tag(x_410) == 0)
{
uint8_t x_411; 
x_411 = !lean_is_exclusive(x_410);
if (x_411 == 0)
{
lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; 
x_412 = lean_ctor_get(x_410, 0);
x_413 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_413, 0, x_412);
lean_ctor_set(x_413, 1, x_408);
x_414 = lean_box(0);
x_415 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_415, 0, x_413);
lean_ctor_set(x_415, 1, x_414);
lean_ctor_set(x_410, 0, x_415);
return x_410;
}
else
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; 
x_416 = lean_ctor_get(x_410, 0);
x_417 = lean_ctor_get(x_410, 1);
lean_inc(x_417);
lean_inc(x_416);
lean_dec(x_410);
x_418 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_408);
x_419 = lean_box(0);
x_420 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_421, 0, x_420);
lean_ctor_set(x_421, 1, x_417);
return x_421;
}
}
else
{
uint8_t x_422; 
lean_dec(x_408);
x_422 = !lean_is_exclusive(x_410);
if (x_422 == 0)
{
return x_410;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_423 = lean_ctor_get(x_410, 0);
x_424 = lean_ctor_get(x_410, 1);
lean_inc(x_424);
lean_inc(x_423);
lean_dec(x_410);
x_425 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
return x_425;
}
}
}
else
{
uint8_t x_426; 
lean_dec(x_401);
lean_dec(x_400);
lean_dec(x_399);
lean_dec(x_398);
lean_dec(x_3);
x_426 = !lean_is_exclusive(x_407);
if (x_426 == 0)
{
return x_407;
}
else
{
lean_object* x_427; lean_object* x_428; lean_object* x_429; 
x_427 = lean_ctor_get(x_407, 0);
x_428 = lean_ctor_get(x_407, 1);
lean_inc(x_428);
lean_inc(x_427);
lean_dec(x_407);
x_429 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_429, 0, x_427);
lean_ctor_set(x_429, 1, x_428);
return x_429;
}
}
}
}
}
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; uint8_t x_442; lean_object* x_443; 
lean_dec(x_13);
x_437 = lean_box(x_1);
x_438 = lean_box(x_2);
x_439 = lean_box(x_47);
x_440 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0___boxed), 11, 4);
lean_closure_set(x_440, 0, x_3);
lean_closure_set(x_440, 1, x_437);
lean_closure_set(x_440, 2, x_438);
lean_closure_set(x_440, 3, x_439);
x_441 = lean_box(0);
x_442 = lean_unbox(x_441);
x_443 = l_Lean_Meta_forallTelescopeReducing___at___Lean_Meta_getParamNames_spec__1(lean_box(0), x_11, x_440, x_442, x_5, x_6, x_7, x_8, x_12);
return x_443;
}
block_46:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_19 = lean_mk_string_unchecked("True", 4, 4);
x_20 = l_Lean_Name_mkStr1(x_19);
x_21 = lean_box(0);
x_22 = l_Lean_Expr_const___override(x_20, x_21);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
x_23 = l_Lean_Meta_mkEq(x_11, x_22, x_14, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 1);
lean_inc(x_25);
lean_dec(x_23);
x_26 = l_Lean_Meta_mkEqTrue(x_3, x_14, x_15, x_16, x_17, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
lean_ctor_set(x_26, 0, x_31);
return x_26;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_26, 0);
x_33 = lean_ctor_get(x_26, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_26);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_24);
x_35 = lean_box(0);
x_36 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_33);
return x_37;
}
}
else
{
uint8_t x_38; 
lean_dec(x_24);
x_38 = !lean_is_exclusive(x_26);
if (x_38 == 0)
{
return x_26;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_26, 0);
x_40 = lean_ctor_get(x_26, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_26);
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
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_3);
x_42 = !lean_is_exclusive(x_23);
if (x_42 == 0)
{
return x_23;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_23, 0);
x_44 = lean_ctor_get(x_23, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_23);
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
uint8_t x_444; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
x_444 = !lean_is_exclusive(x_10);
if (x_444 == 0)
{
return x_10;
}
else
{
lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_445 = lean_ctor_get(x_10, 0);
x_446 = lean_ctor_get(x_10, 1);
lean_inc(x_446);
lean_inc(x_445);
lean_dec(x_10);
x_447 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_447, 0, x_445);
lean_ctor_set(x_447, 1, x_446);
return x_447;
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = l_List_mapM_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___lam__0(x_1, x_12, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_1);
lean_dec(x_1);
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_10, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_4, x_1, x_2, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = lean_unbox(x_4);
lean_dec(x_4);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess(x_1, x_2, x_10, x_11, x_5, x_6, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_7 = l_Lean_Meta_isProp(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_unbox(x_8);
lean_dec(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_10 = lean_ctor_get(x_7, 1);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_mk_string_unchecked("invalid 'simp', proposition expected", 36, 36);
x_12 = l_Lean_stringToMessageData(x_11);
lean_dec(x_11);
x_13 = l_Lean_indentExpr(x_1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_mk_string_unchecked("", 0, 0);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_17, x_2, x_3, x_4, x_5, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_7);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_7, 0);
lean_dec(x_20);
x_21 = lean_box(0);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_7, 1);
lean_inc(x_22);
lean_dec(x_7);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
uint8_t x_25; 
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_7);
if (x_25 == 0)
{
return x_7;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_7, 0);
x_27 = lean_ctor_get(x_7, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_7);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_instInhabitedMetaM___lam__0___boxed), 5, 0);
x_8 = lean_panic_fn(x_7, x_1);
x_9 = lean_apply_5(x_8, x_2, x_3, x_4, x_5, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, uint8_t x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; 
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_15 = l_Lean_Meta_forallMetaTelescopeReducing(x_1, x_2, x_3, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_ctor_get(x_16, 1);
x_19 = lean_ctor_get(x_16, 0);
lean_dec(x_19);
x_20 = lean_ctor_get(x_15, 1);
lean_inc(x_20);
lean_dec(x_15);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_24 = l_Lean_Meta_whnfR(x_22, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_mk_string_unchecked("Eq", 2, 2);
x_28 = l_Lean_Name_mkStr1(x_27);
x_29 = lean_unsigned_to_nat(3u);
x_30 = l_Lean_Expr_isAppOfArity(x_25, x_28, x_29);
lean_dec(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_31 = lean_mk_string_unchecked("unexpected kind of 'simp' theorem", 33, 33);
x_32 = l_Lean_stringToMessageData(x_31);
lean_dec(x_31);
x_33 = l_Lean_indentExpr(x_25);
lean_ctor_set_tag(x_18, 7);
lean_ctor_set(x_18, 1, x_33);
lean_ctor_set(x_18, 0, x_32);
x_34 = lean_mk_string_unchecked("", 0, 0);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_35);
lean_ctor_set(x_16, 0, x_18);
x_36 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_16, x_10, x_11, x_12, x_13, x_26);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
return x_36;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = lean_ctor_get(x_36, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_36);
x_40 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_40, 0, x_38);
lean_ctor_set(x_40, 1, x_39);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_free_object(x_18);
lean_free_object(x_16);
x_41 = l_Lean_Expr_appFn_x21(x_25);
x_42 = l_Lean_Expr_appArg_x21(x_41);
lean_dec(x_41);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_42);
x_43 = l_Lean_Meta_DiscrTree_mkPath(x_42, x_9, x_10, x_11, x_12, x_13, x_26);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
lean_dec(x_43);
x_46 = l_Lean_Expr_appArg_x21(x_25);
lean_dec(x_25);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_47 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_42, x_46, x_10, x_11, x_12, x_13, x_45);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
lean_inc(x_4);
x_50 = l_Lean_Meta_isRflProof(x_4, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_53, 0, x_44);
lean_ctor_set(x_53, 1, x_5);
lean_ctor_set(x_53, 2, x_4);
lean_ctor_set(x_53, 3, x_6);
lean_ctor_set(x_53, 4, x_8);
lean_ctor_set_uint8(x_53, sizeof(void*)*5, x_7);
x_54 = lean_unbox(x_48);
lean_dec(x_48);
lean_ctor_set_uint8(x_53, sizeof(void*)*5 + 1, x_54);
x_55 = lean_unbox(x_52);
lean_dec(x_52);
lean_ctor_set_uint8(x_53, sizeof(void*)*5 + 2, x_55);
lean_ctor_set(x_50, 0, x_53);
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; uint8_t x_60; lean_object* x_61; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_58, 0, x_44);
lean_ctor_set(x_58, 1, x_5);
lean_ctor_set(x_58, 2, x_4);
lean_ctor_set(x_58, 3, x_6);
lean_ctor_set(x_58, 4, x_8);
lean_ctor_set_uint8(x_58, sizeof(void*)*5, x_7);
x_59 = lean_unbox(x_48);
lean_dec(x_48);
lean_ctor_set_uint8(x_58, sizeof(void*)*5 + 1, x_59);
x_60 = lean_unbox(x_56);
lean_dec(x_56);
lean_ctor_set_uint8(x_58, sizeof(void*)*5 + 2, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_58);
lean_ctor_set(x_61, 1, x_57);
return x_61;
}
}
else
{
uint8_t x_62; 
lean_dec(x_48);
lean_dec(x_44);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_50);
if (x_62 == 0)
{
return x_50;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_50, 0);
x_64 = lean_ctor_get(x_50, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_50);
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
lean_dec(x_44);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_66 = !lean_is_exclusive(x_47);
if (x_66 == 0)
{
return x_47;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_47, 0);
x_68 = lean_ctor_get(x_47, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_47);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
else
{
uint8_t x_70; 
lean_dec(x_42);
lean_dec(x_25);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_70 = !lean_is_exclusive(x_43);
if (x_70 == 0)
{
return x_43;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_71 = lean_ctor_get(x_43, 0);
x_72 = lean_ctor_get(x_43, 1);
lean_inc(x_72);
lean_inc(x_71);
lean_dec(x_43);
x_73 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
return x_73;
}
}
}
}
else
{
uint8_t x_74; 
lean_free_object(x_18);
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_18, 1);
lean_inc(x_78);
lean_dec(x_18);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_79 = l_Lean_Meta_whnfR(x_78, x_10, x_11, x_12, x_13, x_20);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
lean_dec(x_79);
x_82 = lean_mk_string_unchecked("Eq", 2, 2);
x_83 = l_Lean_Name_mkStr1(x_82);
x_84 = lean_unsigned_to_nat(3u);
x_85 = l_Lean_Expr_isAppOfArity(x_80, x_83, x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_86 = lean_mk_string_unchecked("unexpected kind of 'simp' theorem", 33, 33);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = l_Lean_indentExpr(x_80);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("", 0, 0);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
lean_ctor_set_tag(x_16, 7);
lean_ctor_set(x_16, 1, x_91);
lean_ctor_set(x_16, 0, x_89);
x_92 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_16, x_10, x_11, x_12, x_13, x_81);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_92, 1);
lean_inc(x_94);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_95 = x_92;
} else {
 lean_dec_ref(x_92);
 x_95 = lean_box(0);
}
if (lean_is_scalar(x_95)) {
 x_96 = lean_alloc_ctor(1, 2, 0);
} else {
 x_96 = x_95;
}
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_94);
return x_96;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_free_object(x_16);
x_97 = l_Lean_Expr_appFn_x21(x_80);
x_98 = l_Lean_Expr_appArg_x21(x_97);
lean_dec(x_97);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_98);
x_99 = l_Lean_Meta_DiscrTree_mkPath(x_98, x_9, x_10, x_11, x_12, x_13, x_81);
if (lean_obj_tag(x_99) == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_100 = lean_ctor_get(x_99, 0);
lean_inc(x_100);
x_101 = lean_ctor_get(x_99, 1);
lean_inc(x_101);
lean_dec(x_99);
x_102 = l_Lean_Expr_appArg_x21(x_80);
lean_dec(x_80);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_103 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_98, x_102, x_10, x_11, x_12, x_13, x_101);
if (lean_obj_tag(x_103) == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_104 = lean_ctor_get(x_103, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_103, 1);
lean_inc(x_105);
lean_dec(x_103);
lean_inc(x_4);
x_106 = l_Lean_Meta_isRflProof(x_4, x_10, x_11, x_12, x_13, x_105);
if (lean_obj_tag(x_106) == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; uint8_t x_112; lean_object* x_113; 
x_107 = lean_ctor_get(x_106, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_106, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_109 = x_106;
} else {
 lean_dec_ref(x_106);
 x_109 = lean_box(0);
}
x_110 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_110, 0, x_100);
lean_ctor_set(x_110, 1, x_5);
lean_ctor_set(x_110, 2, x_4);
lean_ctor_set(x_110, 3, x_6);
lean_ctor_set(x_110, 4, x_8);
lean_ctor_set_uint8(x_110, sizeof(void*)*5, x_7);
x_111 = lean_unbox(x_104);
lean_dec(x_104);
lean_ctor_set_uint8(x_110, sizeof(void*)*5 + 1, x_111);
x_112 = lean_unbox(x_107);
lean_dec(x_107);
lean_ctor_set_uint8(x_110, sizeof(void*)*5 + 2, x_112);
if (lean_is_scalar(x_109)) {
 x_113 = lean_alloc_ctor(0, 2, 0);
} else {
 x_113 = x_109;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_108);
return x_113;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; 
lean_dec(x_104);
lean_dec(x_100);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_114 = lean_ctor_get(x_106, 0);
lean_inc(x_114);
x_115 = lean_ctor_get(x_106, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_116 = x_106;
} else {
 lean_dec_ref(x_106);
 x_116 = lean_box(0);
}
if (lean_is_scalar(x_116)) {
 x_117 = lean_alloc_ctor(1, 2, 0);
} else {
 x_117 = x_116;
}
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_115);
return x_117;
}
}
else
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_100);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_118 = lean_ctor_get(x_103, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_103, 1);
lean_inc(x_119);
if (lean_is_exclusive(x_103)) {
 lean_ctor_release(x_103, 0);
 lean_ctor_release(x_103, 1);
 x_120 = x_103;
} else {
 lean_dec_ref(x_103);
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
else
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_98);
lean_dec(x_80);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_122 = lean_ctor_get(x_99, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_99, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_99)) {
 lean_ctor_release(x_99, 0);
 lean_ctor_release(x_99, 1);
 x_124 = x_99;
} else {
 lean_dec_ref(x_99);
 x_124 = lean_box(0);
}
if (lean_is_scalar(x_124)) {
 x_125 = lean_alloc_ctor(1, 2, 0);
} else {
 x_125 = x_124;
}
lean_ctor_set(x_125, 0, x_122);
lean_ctor_set(x_125, 1, x_123);
return x_125;
}
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_free_object(x_16);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_126 = lean_ctor_get(x_79, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_79, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_128 = x_79;
} else {
 lean_dec_ref(x_79);
 x_128 = lean_box(0);
}
if (lean_is_scalar(x_128)) {
 x_129 = lean_alloc_ctor(1, 2, 0);
} else {
 x_129 = x_128;
}
lean_ctor_set(x_129, 0, x_126);
lean_ctor_set(x_129, 1, x_127);
return x_129;
}
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_130 = lean_ctor_get(x_16, 1);
lean_inc(x_130);
lean_dec(x_16);
x_131 = lean_ctor_get(x_15, 1);
lean_inc(x_131);
lean_dec(x_15);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_133 = x_130;
} else {
 lean_dec_ref(x_130);
 x_133 = lean_box(0);
}
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
x_134 = l_Lean_Meta_whnfR(x_132, x_10, x_11, x_12, x_13, x_131);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_140; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_mk_string_unchecked("Eq", 2, 2);
x_138 = l_Lean_Name_mkStr1(x_137);
x_139 = lean_unsigned_to_nat(3u);
x_140 = l_Lean_Expr_isAppOfArity(x_135, x_138, x_139);
lean_dec(x_138);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_141 = lean_mk_string_unchecked("unexpected kind of 'simp' theorem", 33, 33);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
x_143 = l_Lean_indentExpr(x_135);
if (lean_is_scalar(x_133)) {
 x_144 = lean_alloc_ctor(7, 2, 0);
} else {
 x_144 = x_133;
 lean_ctor_set_tag(x_144, 7);
}
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("", 0, 0);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_147, x_10, x_11, x_12, x_13, x_136);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_149 = lean_ctor_get(x_148, 0);
lean_inc(x_149);
x_150 = lean_ctor_get(x_148, 1);
lean_inc(x_150);
if (lean_is_exclusive(x_148)) {
 lean_ctor_release(x_148, 0);
 lean_ctor_release(x_148, 1);
 x_151 = x_148;
} else {
 lean_dec_ref(x_148);
 x_151 = lean_box(0);
}
if (lean_is_scalar(x_151)) {
 x_152 = lean_alloc_ctor(1, 2, 0);
} else {
 x_152 = x_151;
}
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_150);
return x_152;
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_133);
x_153 = l_Lean_Expr_appFn_x21(x_135);
x_154 = l_Lean_Expr_appArg_x21(x_153);
lean_dec(x_153);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_154);
x_155 = l_Lean_Meta_DiscrTree_mkPath(x_154, x_9, x_10, x_11, x_12, x_13, x_136);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
lean_dec(x_155);
x_158 = l_Lean_Expr_appArg_x21(x_135);
lean_dec(x_135);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_159 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_isPerm(x_154, x_158, x_10, x_11, x_12, x_13, x_157);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
lean_inc(x_4);
x_162 = l_Lean_Meta_isRflProof(x_4, x_10, x_11, x_12, x_13, x_161);
if (lean_obj_tag(x_162) == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; uint8_t x_167; uint8_t x_168; lean_object* x_169; 
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_165 = x_162;
} else {
 lean_dec_ref(x_162);
 x_165 = lean_box(0);
}
x_166 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_166, 0, x_156);
lean_ctor_set(x_166, 1, x_5);
lean_ctor_set(x_166, 2, x_4);
lean_ctor_set(x_166, 3, x_6);
lean_ctor_set(x_166, 4, x_8);
lean_ctor_set_uint8(x_166, sizeof(void*)*5, x_7);
x_167 = lean_unbox(x_160);
lean_dec(x_160);
lean_ctor_set_uint8(x_166, sizeof(void*)*5 + 1, x_167);
x_168 = lean_unbox(x_163);
lean_dec(x_163);
lean_ctor_set_uint8(x_166, sizeof(void*)*5 + 2, x_168);
if (lean_is_scalar(x_165)) {
 x_169 = lean_alloc_ctor(0, 2, 0);
} else {
 x_169 = x_165;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_164);
return x_169;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_160);
lean_dec(x_156);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_170 = lean_ctor_get(x_162, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_162, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_162)) {
 lean_ctor_release(x_162, 0);
 lean_ctor_release(x_162, 1);
 x_172 = x_162;
} else {
 lean_dec_ref(x_162);
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
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_dec(x_156);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_174 = lean_ctor_get(x_159, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_159, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_159)) {
 lean_ctor_release(x_159, 0);
 lean_ctor_release(x_159, 1);
 x_176 = x_159;
} else {
 lean_dec_ref(x_159);
 x_176 = lean_box(0);
}
if (lean_is_scalar(x_176)) {
 x_177 = lean_alloc_ctor(1, 2, 0);
} else {
 x_177 = x_176;
}
lean_ctor_set(x_177, 0, x_174);
lean_ctor_set(x_177, 1, x_175);
return x_177;
}
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_154);
lean_dec(x_135);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_178 = lean_ctor_get(x_155, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_155, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_180 = x_155;
} else {
 lean_dec_ref(x_155);
 x_180 = lean_box(0);
}
if (lean_is_scalar(x_180)) {
 x_181 = lean_alloc_ctor(1, 2, 0);
} else {
 x_181 = x_180;
}
lean_ctor_set(x_181, 0, x_178);
lean_ctor_set(x_181, 1, x_179);
return x_181;
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_133);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_182 = lean_ctor_get(x_134, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_134, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_184 = x_134;
} else {
 lean_dec_ref(x_134);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
}
lean_ctor_set(x_185, 0, x_182);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
}
}
else
{
uint8_t x_186; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_186 = !lean_is_exclusive(x_15);
if (x_186 == 0)
{
return x_15;
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
x_187 = lean_ctor_get(x_15, 0);
x_188 = lean_ctor_get(x_15, 1);
lean_inc(x_188);
lean_inc(x_187);
lean_dec(x_15);
x_189 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
return x_189;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, uint8_t x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
goto block_31;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_43; 
x_32 = lean_box(0);
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
x_33 = x_43;
goto block_42;
block_42:
{
uint8_t x_34; 
x_34 = lean_name_eq(x_33, x_32);
lean_dec(x_33);
if (x_34 == 0)
{
goto block_31;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_35 = lean_mk_string_unchecked("Lean.Meta.Tactic.Simp.SimpTheorems", 34, 34);
x_36 = lean_mk_string_unchecked("_private.Lean.Meta.Tactic.Simp.SimpTheorems.0.Lean.Meta.mkSimpTheoremCore", 73, 73);
x_37 = lean_unsigned_to_nat(406u);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_mk_string_unchecked("assertion violation: origin != .fvar ⟨.anonymous⟩\n  ", 56, 52);
x_40 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_35, x_36, x_37, x_38, x_39);
lean_dec(x_39);
lean_dec(x_36);
lean_dec(x_35);
x_41 = l_panic___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore_spec__0(x_40, x_8, x_9, x_10, x_11, x_12);
return x_41;
}
}
}
block_31:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_13 = lean_infer_type(x_2, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = l_Lean_instantiateMVars___at_____private_Lean_Meta_Basic_0__Lean_Meta_isClassApp_x3f_spec__0___redArg(x_14, x_9, x_15);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_box(0);
x_21 = lean_box(x_5);
x_22 = lean_box(x_7);
x_23 = lean_alloc_closure((void*)(l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___boxed), 14, 9);
lean_closure_set(x_23, 0, x_17);
lean_closure_set(x_23, 1, x_19);
lean_closure_set(x_23, 2, x_20);
lean_closure_set(x_23, 3, x_4);
lean_closure_set(x_23, 4, x_3);
lean_closure_set(x_23, 5, x_6);
lean_closure_set(x_23, 6, x_21);
lean_closure_set(x_23, 7, x_1);
lean_closure_set(x_23, 8, x_22);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
x_26 = l_Lean_Meta_withNewMCtxDepth___at___Lean_Meta_matchesInstance_spec__0___redArg(x_23, x_25, x_8, x_9, x_10, x_11, x_18);
return x_26;
}
else
{
uint8_t x_27; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_13);
if (x_27 == 0)
{
return x_13;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_13, 0);
x_29 = lean_ctor_get(x_13, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_13);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_15 = lean_unbox(x_3);
lean_dec(x_3);
x_16 = lean_unbox(x_7);
lean_dec(x_7);
x_17 = lean_unbox(x_9);
lean_dec(x_9);
x_18 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___lam__0(x_1, x_2, x_15, x_4, x_5, x_6, x_16, x_8, x_17, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_2);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = lean_unbox(x_7);
lean_dec(x_7);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_1, x_2, x_3, x_4, x_13, x_6, x_14, x_8, x_9, x_10, x_11, x_12);
return x_15;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_14; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_8);
lean_ctor_set(x_14, 1, x_13);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_7, 1);
lean_inc(x_16);
lean_dec(x_7);
x_17 = lean_ctor_get(x_15, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 1);
lean_inc(x_18);
lean_dec(x_15);
x_19 = lean_box(1);
x_20 = lean_box(0);
x_21 = lean_unbox(x_19);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_1);
x_22 = l_Lean_Meta_mkAuxLemma(x_1, x_18, x_17, x_20, x_21, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
lean_inc(x_3);
x_25 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_25, 0, x_3);
lean_ctor_set_uint8(x_25, sizeof(void*)*1, x_4);
lean_ctor_set_uint8(x_25, sizeof(void*)*1 + 1, x_5);
lean_inc(x_2);
lean_inc(x_23);
x_26 = l_Lean_Expr_const___override(x_23, x_2);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_mk_empty_array_with_capacity(x_27);
x_29 = lean_box(0);
x_30 = l_Lean_Expr_const___override(x_23, x_29);
x_31 = lean_box(0);
x_32 = lean_unbox(x_31);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_6);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_25, x_26, x_28, x_30, x_4, x_6, x_32, x_9, x_10, x_11, x_12, x_24);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_array_push(x_8, x_34);
x_7 = x_16;
x_8 = x_36;
x_13 = x_35;
goto _start;
}
else
{
uint8_t x_38; 
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_38 = !lean_is_exclusive(x_33);
if (x_38 == 0)
{
return x_33;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_33, 0);
x_40 = lean_ctor_get(x_33, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_33);
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
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_22);
if (x_42 == 0)
{
return x_22;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_22, 0);
x_44 = lean_ctor_get(x_22, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_22);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
lean_inc(x_1);
x_10 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_1, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint64_t x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_box(0);
lean_inc(x_13);
x_15 = l_List_mapTR_loop___at___Lean_mkConstWithLevelParams___at___Lean_Meta_registerCoercion_spec__0_spec__0(x_13, x_14);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l_Lean_Expr_const___override(x_1, x_15);
x_17 = l_Lean_Meta_simpGlobalConfig;
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get_uint64(x_17, sizeof(void*)*1);
x_20 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 8);
x_21 = lean_ctor_get(x_5, 1);
x_22 = lean_ctor_get(x_5, 2);
x_23 = lean_ctor_get(x_5, 3);
x_24 = lean_ctor_get(x_5, 4);
x_25 = lean_ctor_get(x_5, 5);
x_26 = lean_ctor_get(x_5, 6);
x_27 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 9);
x_28 = lean_ctor_get_uint8(x_5, sizeof(void*)*7 + 10);
lean_inc(x_26);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
x_29 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_29, 0, x_18);
lean_ctor_set(x_29, 1, x_21);
lean_ctor_set(x_29, 2, x_22);
lean_ctor_set(x_29, 3, x_23);
lean_ctor_set(x_29, 4, x_24);
lean_ctor_set(x_29, 5, x_25);
lean_ctor_set(x_29, 6, x_26);
lean_ctor_set_uint64(x_29, sizeof(void*)*7, x_19);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 8, x_20);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 9, x_27);
lean_ctor_set_uint8(x_29, sizeof(void*)*7 + 10, x_28);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
lean_inc(x_16);
x_30 = lean_infer_type(x_16, x_29, x_6, x_7, x_8, x_12);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
lean_inc(x_31);
x_33 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_31, x_29, x_6, x_7, x_8, x_32);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; lean_object* x_35; 
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
lean_inc(x_31);
x_35 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_shouldPreprocess(x_31, x_29, x_6, x_7, x_8, x_34);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
if (x_3 == 0)
{
uint8_t x_51; 
x_51 = lean_unbox(x_36);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
lean_dec(x_31);
lean_dec(x_15);
lean_dec(x_13);
lean_inc(x_1);
x_52 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_52, 0, x_1);
lean_ctor_set_uint8(x_52, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_52, sizeof(void*)*1 + 1, x_3);
x_53 = lean_unsigned_to_nat(0u);
x_54 = lean_mk_empty_array_with_capacity(x_53);
x_55 = l_Lean_Expr_const___override(x_1, x_14);
x_56 = lean_unbox(x_36);
lean_dec(x_36);
x_57 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_52, x_16, x_54, x_55, x_2, x_4, x_56, x_29, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_unsigned_to_nat(1u);
x_61 = lean_mk_empty_array_with_capacity(x_60);
x_62 = lean_array_push(x_61, x_59);
lean_ctor_set(x_57, 0, x_62);
return x_57;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_63 = lean_ctor_get(x_57, 0);
x_64 = lean_ctor_get(x_57, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_57);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_mk_empty_array_with_capacity(x_65);
x_67 = lean_array_push(x_66, x_63);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
return x_68;
}
}
else
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_57);
if (x_69 == 0)
{
return x_57;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_57, 0);
x_71 = lean_ctor_get(x_57, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_57);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_dec(x_36);
goto block_50;
}
}
else
{
lean_dec(x_36);
goto block_50;
}
block_50:
{
lean_object* x_38; uint8_t x_39; lean_object* x_40; 
x_38 = lean_box(1);
x_39 = lean_unbox(x_38);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_29);
x_40 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_3, x_39, x_16, x_31, x_29, x_6, x_7, x_8, x_37);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_unsigned_to_nat(0u);
x_44 = lean_mk_empty_array_with_capacity(x_43);
x_45 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___redArg(x_13, x_15, x_1, x_2, x_3, x_4, x_41, x_44, x_29, x_6, x_7, x_8, x_42);
return x_45;
}
else
{
uint8_t x_46; 
lean_dec(x_29);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_40);
if (x_46 == 0)
{
return x_40;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_40, 0);
x_48 = lean_ctor_get(x_40, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_40);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
}
else
{
uint8_t x_73; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_73 = !lean_is_exclusive(x_35);
if (x_73 == 0)
{
return x_35;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_35, 0);
x_75 = lean_ctor_get(x_35, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_35);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
uint8_t x_77; 
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_33);
if (x_77 == 0)
{
return x_33;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_33, 0);
x_79 = lean_ctor_get(x_33, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_33);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
else
{
uint8_t x_81; 
lean_dec(x_29);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_13);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_81 = !lean_is_exclusive(x_30);
if (x_81 == 0)
{
return x_30;
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_82 = lean_ctor_get(x_30, 0);
x_83 = lean_ctor_get(x_30, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_30);
x_84 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_83);
return x_84;
}
}
}
else
{
uint8_t x_85; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
x_85 = !lean_is_exclusive(x_10);
if (x_85 == 0)
{
return x_10;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; 
x_86 = lean_ctor_get(x_10, 0);
x_87 = lean_ctor_get(x_10, 1);
lean_inc(x_87);
lean_inc(x_86);
lean_dec(x_10);
x_88 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_88, 0, x_86);
lean_ctor_set(x_88, 1, x_87);
return x_88;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_4);
lean_dec(x_4);
x_15 = lean_unbox(x_5);
lean_dec(x_5);
x_16 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___redArg(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
return x_16;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; lean_object* x_18; 
x_16 = lean_unbox(x_4);
lean_dec(x_4);
x_17 = lean_unbox(x_5);
lean_dec(x_5);
x_18 = l_List_forIn_x27_loop___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst_spec__0(x_1, x_2, x_3, x_16, x_17, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_7);
return x_18;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; uint8_t x_11; lean_object* x_12; 
x_10 = lean_unbox(x_2);
lean_dec(x_2);
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
return x_12;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedSimpEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; uint8_t x_11; lean_object* x_12; uint8_t x_13; uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_1 = l_Array_empty(lean_box(0));
x_2 = lean_mk_string_unchecked("_inhabitedExprDummy", 19, 19);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(0);
x_5 = l_Lean_Expr_const___override(x_3, x_4);
x_6 = lean_box(0);
x_7 = lean_box(0);
x_8 = lean_box(0);
x_9 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_9, 0, x_8);
x_10 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1, x_10);
x_11 = lean_unbox(x_7);
lean_ctor_set_uint8(x_9, sizeof(void*)*1 + 1, x_11);
lean_inc(x_1);
x_12 = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(x_12, 0, x_1);
lean_ctor_set(x_12, 1, x_1);
lean_ctor_set(x_12, 2, x_5);
lean_ctor_set(x_12, 3, x_6);
lean_ctor_set(x_12, 4, x_9);
x_13 = lean_unbox(x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*5, x_13);
x_14 = lean_unbox(x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 1, x_14);
x_15 = lean_unbox(x_7);
lean_ctor_set_uint8(x_12, sizeof(void*)*5 + 2, x_15);
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Meta_instInhabitedSimpTheorems;
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_ctor_get(x_9, 0);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
x_12 = l_Lean_ScopedEnvExtension_getState___redArg(x_7, x_1, x_8, x_11);
lean_ctor_set(x_4, 0, x_12);
return x_4;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_4, 0);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
lean_inc(x_13);
lean_dec(x_4);
x_15 = l_Lean_Meta_instInhabitedSimpTheorems;
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_1, 1);
x_18 = lean_ctor_get(x_17, 0);
x_19 = lean_ctor_get_uint8(x_18, sizeof(void*)*3);
x_20 = l_Lean_ScopedEnvExtension_getState___redArg(x_15, x_1, x_16, x_19);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_14);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SimpExtension_getTheorems___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpExtension_getTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpExtension_getTheorems(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_5, x_4);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_8);
lean_dec(x_1);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
lean_dec(x_6);
x_13 = lean_array_uget(x_3, x_5);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
lean_inc(x_8);
lean_inc(x_1);
x_15 = l_Lean_ScopedEnvExtension_add___at___Lean_Meta_addGlobalInstance_spec__0___redArg(x_1, x_14, x_2, x_7, x_8, x_9, x_10);
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_box(0);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_5, x_19);
x_5 = x_20;
x_6 = x_17;
x_10 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_12 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; uint8_t x_20; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_box(0);
x_16 = lean_array_size(x_13);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_5, x_13, x_16, x_18, x_15, x_8, x_9, x_10, x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_13);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; 
x_21 = lean_ctor_get(x_19, 0);
lean_dec(x_21);
lean_ctor_set(x_19, 0, x_15);
return x_19;
}
else
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_19, 1);
lean_inc(x_22);
lean_dec(x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_15);
lean_ctor_set(x_23, 1, x_22);
return x_23;
}
}
else
{
uint8_t x_24; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_24 = !lean_is_exclusive(x_12);
if (x_24 == 0)
{
return x_12;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_12, 0);
x_26 = lean_ctor_get(x_12, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_12);
x_27 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_27, 0, x_25);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; size_t x_12; size_t x_13; lean_object* x_14; 
x_11 = lean_unbox(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___redArg(x_1, x_11, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_addSimpTheorem_spec__0(x_1, x_12, x_3, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addSimpTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_unbox(x_3);
lean_dec(x_3);
x_13 = lean_unbox(x_4);
lean_dec(x_4);
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = l_Lean_Meta_addSimpTheorem(x_1, x_2, x_12, x_13, x_14, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_15;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5516_() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_1 = lean_box(2);
x_2 = lean_mk_string_unchecked("Lean", 4, 4);
x_3 = lean_mk_string_unchecked("Parser", 6, 6);
x_4 = lean_mk_string_unchecked("Tactic", 6, 6);
x_5 = lean_mk_string_unchecked("tacticSeq", 9, 9);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_6 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_5);
x_7 = l_Array_empty(lean_box(0));
x_8 = lean_mk_string_unchecked("tacticSeq1Indented", 18, 18);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_9 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_8);
x_10 = lean_mk_string_unchecked("null", 4, 4);
x_11 = l_Lean_Name_mkStr1(x_10);
x_12 = lean_mk_string_unchecked("exact", 5, 5);
lean_inc(x_12);
lean_inc(x_3);
lean_inc(x_2);
x_13 = l_Lean_Name_mkStr4(x_2, x_3, x_4, x_12);
x_14 = l_Lean_mkAtom(x_12);
lean_inc(x_7);
x_15 = lean_array_push(x_7, x_14);
x_16 = lean_mk_string_unchecked("Term", 4, 4);
x_17 = lean_mk_string_unchecked("declName", 8, 8);
x_18 = l_Lean_Name_mkStr4(x_2, x_3, x_16, x_17);
x_19 = lean_mk_string_unchecked("decl_name%", 10, 10);
x_20 = l_Lean_mkAtom(x_19);
lean_inc(x_7);
x_21 = lean_array_push(x_7, x_20);
x_22 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_18);
lean_ctor_set(x_22, 2, x_21);
x_23 = lean_array_push(x_15, x_22);
x_24 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_13);
lean_ctor_set(x_24, 2, x_23);
lean_inc(x_7);
x_25 = lean_array_push(x_7, x_24);
x_26 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_26, 0, x_1);
lean_ctor_set(x_26, 1, x_11);
lean_ctor_set(x_26, 2, x_25);
lean_inc(x_7);
x_27 = lean_array_push(x_7, x_26);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_9);
lean_ctor_set(x_28, 2, x_27);
x_29 = lean_array_push(x_7, x_28);
x_30 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_6);
lean_ctor_set(x_30, 2, x_29);
return x_30;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_Meta_addSimpTheoremEntry(x_1, x_3);
return x_4;
}
case 1:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
lean_dec(x_2);
x_6 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_5);
return x_6;
}
default: 
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_dec(x_2);
x_9 = l_Lean_Meta_SimpTheorems_registerDeclToUnfoldThms(x_1, x_7, x_8);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpExt___lam__0), 2, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_mkSimpExt___lam__1___boxed), 1, 0);
x_5 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_6 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_box(0));
x_7 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
x_8 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_8);
lean_inc(x_6);
lean_inc(x_5);
x_10 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_10, 0, x_5);
lean_ctor_set(x_10, 1, x_5);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_7);
lean_ctor_set(x_10, 4, x_6);
lean_ctor_set(x_10, 5, x_9);
x_11 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_3);
lean_ctor_set(x_11, 2, x_10);
lean_ctor_set(x_11, 3, x_4);
x_12 = l_Lean_registerSimpleScopedEnvExtension___redArg(x_11, x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_mkSimpExt___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_mkSimpExt___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5574_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_2 = lean_unsigned_to_nat(8u);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_unsigned_to_nat(2u);
x_5 = lean_nat_shiftl(x_2, x_4);
x_6 = lean_unsigned_to_nat(3u);
x_7 = lean_nat_div(x_5, x_6);
lean_dec(x_5);
x_8 = l_Nat_nextPowerOfTwo(x_7);
lean_dec(x_7);
x_9 = lean_box(0);
x_10 = lean_mk_array(x_8, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_st_mk_ref(x_11, x_1);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
return x_12;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_12, 0);
x_15 = lean_ctor_get(x_12, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_12);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_simpExtensionMapRef;
x_4 = lean_st_ref_get(x_3, x_2);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint64_t x_9; lean_object* x_10; uint64_t x_11; uint64_t x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; size_t x_18; size_t x_19; lean_object* x_20; size_t x_21; size_t x_22; size_t x_23; lean_object* x_24; lean_object* x_25; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_6, 1);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = l_Lean_Name_hash___override(x_1);
x_10 = lean_unsigned_to_nat(32u);
x_11 = lean_uint64_of_nat(x_10);
x_12 = lean_uint64_shift_right(x_9, x_11);
x_13 = lean_uint64_xor(x_9, x_12);
x_14 = lean_unsigned_to_nat(16u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_uint64_to_usize(x_17);
x_19 = lean_usize_of_nat(x_8);
lean_dec(x_8);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_sub(x_19, x_21);
x_23 = lean_usize_land(x_18, x_22);
x_24 = lean_array_uget(x_7, x_23);
lean_dec(x_7);
x_25 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_1, x_24);
lean_dec(x_24);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_get_size(x_28);
x_30 = l_Lean_Name_hash___override(x_1);
x_31 = lean_unsigned_to_nat(32u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_unsigned_to_nat(16u);
x_36 = lean_uint64_of_nat(x_35);
x_37 = lean_uint64_shift_right(x_34, x_36);
x_38 = lean_uint64_xor(x_34, x_37);
x_39 = lean_uint64_to_usize(x_38);
x_40 = lean_usize_of_nat(x_29);
lean_dec(x_29);
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_usize_of_nat(x_41);
x_43 = lean_usize_sub(x_40, x_42);
x_44 = lean_usize_land(x_39, x_43);
x_45 = lean_array_uget(x_28, x_44);
lean_dec(x_28);
x_46 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_1, x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_27);
return x_47;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getSimpExtension_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_getSimpExtension_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; 
x_6 = lean_array_uget(x_1, x_2);
x_7 = l_Lean_Meta_addSimpTheoremEntry(x_4, x_6);
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
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_2);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremsFromConst(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_13 = lean_ctor_get(x_11, 0);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
x_15 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_15, 0, x_2);
lean_ctor_set_uint8(x_15, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_15, sizeof(void*)*1 + 1, x_4);
x_16 = lean_ctor_get(x_1, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_1, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 2);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 3);
lean_inc(x_19);
x_20 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_14, x_15);
x_21 = lean_ctor_get(x_1, 5);
lean_inc(x_21);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_22, 0, x_16);
lean_ctor_set(x_22, 1, x_17);
lean_ctor_set(x_22, 2, x_18);
lean_ctor_set(x_22, 3, x_19);
lean_ctor_set(x_22, 4, x_20);
lean_ctor_set(x_22, 5, x_21);
x_23 = lean_unsigned_to_nat(0u);
x_24 = lean_array_get_size(x_13);
x_25 = lean_nat_dec_lt(x_23, x_24);
if (x_25 == 0)
{
lean_dec(x_24);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
uint8_t x_26; 
x_26 = lean_nat_dec_le(x_24, x_24);
if (x_26 == 0)
{
lean_dec(x_24);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_22);
return x_11;
}
else
{
size_t x_27; size_t x_28; lean_object* x_29; 
x_27 = lean_usize_of_nat(x_23);
x_28 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_29 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_13, x_27, x_28, x_22);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_29);
return x_11;
}
}
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_30 = lean_ctor_get(x_11, 0);
x_31 = lean_ctor_get(x_11, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_11);
x_32 = lean_ctor_get(x_1, 4);
lean_inc(x_32);
x_33 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_33, 0, x_2);
lean_ctor_set_uint8(x_33, sizeof(void*)*1, x_3);
lean_ctor_set_uint8(x_33, sizeof(void*)*1 + 1, x_4);
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 2);
lean_inc(x_36);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
x_38 = l_Lean_PersistentHashMap_erase___at___Lean_Meta_SimpTheorems_eraseCore_spec__0___redArg(x_32, x_33);
x_39 = lean_ctor_get(x_1, 5);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_40, 0, x_34);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_36);
lean_ctor_set(x_40, 3, x_37);
lean_ctor_set(x_40, 4, x_38);
lean_ctor_set(x_40, 5, x_39);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_get_size(x_30);
x_43 = lean_nat_dec_lt(x_41, x_42);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_42);
lean_dec(x_30);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_31);
return x_44;
}
else
{
uint8_t x_45; 
x_45 = lean_nat_dec_le(x_42, x_42);
if (x_45 == 0)
{
lean_object* x_46; 
lean_dec(x_42);
lean_dec(x_30);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_40);
lean_ctor_set(x_46, 1, x_31);
return x_46;
}
else
{
size_t x_47; size_t x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_usize_of_nat(x_41);
x_48 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_49 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_30, x_47, x_48, x_40);
lean_dec(x_30);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_31);
return x_50;
}
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_2);
lean_dec(x_1);
x_51 = !lean_is_exclusive(x_11);
if (x_51 == 0)
{
return x_11;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_11, 0);
x_53 = lean_ctor_get(x_11, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_11);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addConst___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; uint8_t x_12; lean_object* x_13; 
x_11 = lean_unbox(x_3);
lean_dec(x_3);
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; uint8_t x_93; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_93 = l_Lean_Expr_isConst(x_7);
if (x_93 == 0)
{
x_8 = x_93;
goto block_92;
}
else
{
lean_object* x_94; uint8_t x_95; 
x_94 = lean_ctor_get(x_1, 1);
lean_inc(x_94);
x_95 = l_Array_isEmpty___redArg(x_94);
lean_dec(x_94);
x_8 = x_95;
goto block_92;
}
block_92:
{
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; lean_object* x_11; size_t x_12; lean_object* x_13; uint8_t x_14; 
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_array_size(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_usize_of_nat(x_11);
lean_inc(x_9);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Meta_openAbstractMVarsResult_spec__0(x_10, x_12, x_9, x_2, x_3, x_4, x_5, x_6);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_9, x_15);
lean_dec(x_7);
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
x_19 = l_Lean_Expr_instantiateLevelParamsArray(x_7, x_9, x_17);
lean_dec(x_7);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_1);
x_21 = l_Lean_Expr_constName_x21(x_7);
x_22 = l_Lean_getConstVal___at_____private_Lean_Meta_InferType_0__Lean_Meta_inferConstType_spec__0(x_21, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_22) == 0)
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_24 = lean_ctor_get(x_22, 0);
x_25 = lean_ctor_get(x_22, 1);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_List_isEmpty___redArg(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; 
lean_free_object(x_22);
x_28 = lean_box(0);
x_29 = l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(x_26, x_28, x_2, x_3, x_4, x_5, x_25);
if (lean_obj_tag(x_7) == 4)
{
uint8_t x_30; 
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_7, 0);
lean_inc(x_32);
x_33 = lean_ctor_get(x_7, 1);
lean_inc(x_33);
x_34 = l_ptrEqList___redArg(x_33, x_31);
lean_dec(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
lean_dec(x_7);
x_35 = l_Lean_Expr_const___override(x_32, x_31);
lean_ctor_set(x_29, 0, x_35);
return x_29;
}
else
{
lean_dec(x_32);
lean_dec(x_31);
lean_ctor_set(x_29, 0, x_7);
return x_29;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_36 = lean_ctor_get(x_29, 0);
x_37 = lean_ctor_get(x_29, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_29);
x_38 = lean_ctor_get(x_7, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 1);
lean_inc(x_39);
x_40 = l_ptrEqList___redArg(x_39, x_36);
lean_dec(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_7);
x_41 = l_Lean_Expr_const___override(x_38, x_36);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
lean_object* x_43; 
lean_dec(x_38);
lean_dec(x_36);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_7);
lean_ctor_set(x_43, 1, x_37);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_7);
x_44 = !lean_is_exclusive(x_29);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_29, 0);
lean_dec(x_45);
x_46 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_47 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateConst!Impl", 47, 47);
x_48 = lean_unsigned_to_nat(1780u);
x_49 = lean_unsigned_to_nat(18u);
x_50 = lean_mk_string_unchecked("constant expected", 17, 17);
x_51 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_46, x_47, x_48, x_49, x_50);
lean_dec(x_50);
lean_dec(x_47);
lean_dec(x_46);
x_52 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_51);
lean_ctor_set(x_29, 0, x_52);
return x_29;
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_53 = lean_ctor_get(x_29, 1);
lean_inc(x_53);
lean_dec(x_29);
x_54 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_55 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateConst!Impl", 47, 47);
x_56 = lean_unsigned_to_nat(1780u);
x_57 = lean_unsigned_to_nat(18u);
x_58 = lean_mk_string_unchecked("constant expected", 17, 17);
x_59 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_54, x_55, x_56, x_57, x_58);
lean_dec(x_58);
lean_dec(x_55);
lean_dec(x_54);
x_60 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_53);
return x_61;
}
}
}
else
{
lean_dec(x_26);
lean_ctor_set(x_22, 0, x_7);
return x_22;
}
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_62 = lean_ctor_get(x_22, 0);
x_63 = lean_ctor_get(x_22, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_22);
x_64 = lean_ctor_get(x_62, 1);
lean_inc(x_64);
lean_dec(x_62);
x_65 = l_List_isEmpty___redArg(x_64);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_box(0);
x_67 = l_List_mapM_loop___at_____private_Lean_Meta_AppBuilder_0__Lean_Meta_mkFun_spec__0(x_64, x_66, x_2, x_3, x_4, x_5, x_63);
if (lean_obj_tag(x_7) == 4)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
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
x_71 = lean_ctor_get(x_7, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_7, 1);
lean_inc(x_72);
x_73 = l_ptrEqList___redArg(x_72, x_68);
lean_dec(x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_7);
x_74 = l_Lean_Expr_const___override(x_71, x_68);
if (lean_is_scalar(x_70)) {
 x_75 = lean_alloc_ctor(0, 2, 0);
} else {
 x_75 = x_70;
}
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_69);
return x_75;
}
else
{
lean_object* x_76; 
lean_dec(x_71);
lean_dec(x_68);
if (lean_is_scalar(x_70)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_70;
}
lean_ctor_set(x_76, 0, x_7);
lean_ctor_set(x_76, 1, x_69);
return x_76;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
lean_dec(x_7);
x_77 = lean_ctor_get(x_67, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_67)) {
 lean_ctor_release(x_67, 0);
 lean_ctor_release(x_67, 1);
 x_78 = x_67;
} else {
 lean_dec_ref(x_67);
 x_78 = lean_box(0);
}
x_79 = lean_mk_string_unchecked("Lean.Expr", 9, 9);
x_80 = lean_mk_string_unchecked("_private.Lean.Expr.0.Lean.Expr.updateConst!Impl", 47, 47);
x_81 = lean_unsigned_to_nat(1780u);
x_82 = lean_unsigned_to_nat(18u);
x_83 = lean_mk_string_unchecked("constant expected", 17, 17);
x_84 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_79, x_80, x_81, x_82, x_83);
lean_dec(x_83);
lean_dec(x_80);
lean_dec(x_79);
x_85 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_84);
if (lean_is_scalar(x_78)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_78;
}
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_86, 1, x_77);
return x_86;
}
}
else
{
lean_object* x_87; 
lean_dec(x_64);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_7);
lean_ctor_set(x_87, 1, x_63);
return x_87;
}
}
}
else
{
uint8_t x_88; 
lean_dec(x_7);
x_88 = !lean_is_exclusive(x_22);
if (x_88 == 0)
{
return x_22;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_22, 0);
x_90 = lean_ctor_get(x_22, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_22);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorem_getValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Meta_SimpTheorem_getValue(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(size_t x_1, size_t x_2, lean_object* x_3) {
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
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_12 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_11;
x_3 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_8 = lean_infer_type(x_1, x_3, x_4, x_5, x_6, x_7);
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
lean_inc(x_9);
x_11 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_checkTypeIsProp(x_9, x_3, x_4, x_5, x_6, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
x_15 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocess_go(x_2, x_14, x_1, x_9, x_3, x_4, x_5, x_6, x_12);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; size_t x_19; lean_object* x_20; size_t x_21; lean_object* x_22; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_array_mk(x_17);
x_19 = lean_array_size(x_18);
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_usize_of_nat(x_20);
x_22 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(x_19, x_21, x_18);
lean_ctor_set(x_15, 0, x_22);
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; size_t x_28; lean_object* x_29; lean_object* x_30; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_array_mk(x_23);
x_26 = lean_array_size(x_25);
x_27 = lean_unsigned_to_nat(0u);
x_28 = lean_usize_of_nat(x_27);
x_29 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(x_26, x_28, x_25);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_15);
if (x_31 == 0)
{
return x_15;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_15, 0);
x_33 = lean_ctor_get(x_15, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_15);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
uint8_t x_35; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_11);
if (x_35 == 0)
{
return x_11;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_11, 0);
x_37 = lean_ctor_get(x_11, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_11);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
else
{
uint8_t x_39; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_39 = !lean_is_exclusive(x_8);
if (x_39 == 0)
{
return x_8;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_8, 0);
x_41 = lean_ctor_get(x_8, 1);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_8);
x_42 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof_spec__0(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_2);
lean_dec(x_2);
x_9 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_1, x_8, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems_spec__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_6, x_5);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_7);
lean_ctor_set(x_14, 1, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_array_uget(x_7, x_6);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_15);
lean_inc(x_1);
x_16 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheoremCore(x_1, x_15, x_2, x_15, x_3, x_4, x_13, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; size_t x_22; size_t x_23; lean_object* x_24; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_array_uset(x_7, x_6, x_19);
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_usize_of_nat(x_21);
x_23 = lean_usize_add(x_6, x_22);
x_24 = lean_array_uset(x_20, x_6, x_17);
x_6 = x_23;
x_7 = x_24;
x_12 = x_18;
goto _start;
}
else
{
uint8_t x_26; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; uint8_t x_15; uint8_t x_16; uint8_t x_17; uint8_t x_18; uint8_t x_19; uint8_t x_20; uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; uint8_t x_30; lean_object* x_31; uint8_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; uint8_t x_38; uint64_t x_39; uint64_t x_40; uint8_t x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; uint8_t x_49; lean_object* x_50; lean_object* x_51; 
x_12 = lean_box(2);
x_13 = lean_ctor_get(x_7, 0);
x_14 = lean_ctor_get_uint8(x_13, 0);
x_15 = lean_ctor_get_uint8(x_13, 1);
x_16 = lean_ctor_get_uint8(x_13, 2);
x_17 = lean_ctor_get_uint8(x_13, 3);
x_18 = lean_ctor_get_uint8(x_13, 4);
x_19 = lean_ctor_get_uint8(x_13, 5);
x_20 = lean_ctor_get_uint8(x_13, 6);
x_21 = lean_ctor_get_uint8(x_13, 7);
x_22 = lean_ctor_get_uint8(x_13, 8);
x_23 = lean_ctor_get_uint8(x_13, 10);
x_24 = lean_ctor_get_uint8(x_13, 11);
x_25 = lean_ctor_get_uint8(x_13, 12);
x_26 = lean_ctor_get_uint8(x_13, 13);
x_27 = lean_ctor_get_uint8(x_13, 14);
x_28 = lean_ctor_get_uint8(x_13, 15);
x_29 = lean_ctor_get_uint8(x_13, 16);
x_30 = lean_ctor_get_uint8(x_13, 17);
x_31 = lean_alloc_ctor(0, 0, 18);
lean_ctor_set_uint8(x_31, 0, x_14);
lean_ctor_set_uint8(x_31, 1, x_15);
lean_ctor_set_uint8(x_31, 2, x_16);
lean_ctor_set_uint8(x_31, 3, x_17);
lean_ctor_set_uint8(x_31, 4, x_18);
lean_ctor_set_uint8(x_31, 5, x_19);
lean_ctor_set_uint8(x_31, 6, x_20);
lean_ctor_set_uint8(x_31, 7, x_21);
lean_ctor_set_uint8(x_31, 8, x_22);
x_32 = lean_unbox(x_12);
lean_ctor_set_uint8(x_31, 9, x_32);
lean_ctor_set_uint8(x_31, 10, x_23);
lean_ctor_set_uint8(x_31, 11, x_24);
lean_ctor_set_uint8(x_31, 12, x_25);
lean_ctor_set_uint8(x_31, 13, x_26);
lean_ctor_set_uint8(x_31, 14, x_27);
lean_ctor_set_uint8(x_31, 15, x_28);
lean_ctor_set_uint8(x_31, 16, x_29);
lean_ctor_set_uint8(x_31, 17, x_30);
x_33 = lean_ctor_get_uint64(x_7, sizeof(void*)*7);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_uint64_of_nat(x_34);
x_36 = lean_uint64_shift_right(x_33, x_35);
x_37 = lean_uint64_shift_left(x_36, x_35);
x_38 = lean_unbox(x_12);
x_39 = l_Lean_Meta_TransparencyMode_toUInt64(x_38);
x_40 = lean_uint64_lor(x_37, x_39);
x_41 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 8);
x_42 = lean_ctor_get(x_7, 1);
x_43 = lean_ctor_get(x_7, 2);
x_44 = lean_ctor_get(x_7, 3);
x_45 = lean_ctor_get(x_7, 4);
x_46 = lean_ctor_get(x_7, 5);
x_47 = lean_ctor_get(x_7, 6);
x_48 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 9);
x_49 = lean_ctor_get_uint8(x_7, sizeof(void*)*7 + 10);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
x_50 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_50, 0, x_31);
lean_ctor_set(x_50, 1, x_42);
lean_ctor_set(x_50, 2, x_43);
lean_ctor_set(x_50, 3, x_44);
lean_ctor_set(x_50, 4, x_45);
lean_ctor_set(x_50, 5, x_46);
lean_ctor_set(x_50, 6, x_47);
lean_ctor_set_uint64(x_50, sizeof(void*)*7, x_40);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 8, x_41);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 9, x_48);
lean_ctor_set_uint8(x_50, sizeof(void*)*7 + 10, x_49);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_50);
x_51 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_preprocessProof(x_3, x_5, x_50, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; size_t x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_array_size(x_52);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_usize_of_nat(x_55);
x_57 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems_spec__0(x_1, x_2, x_4, x_6, x_54, x_56, x_52, x_50, x_8, x_9, x_10, x_53);
return x_57;
}
else
{
uint8_t x_58; 
lean_dec(x_50);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_51);
if (x_58 == 0)
{
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_15 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_16 = l_Array_mapMUnsafe_map___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems_spec__0(x_1, x_2, x_13, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; uint8_t x_13; lean_object* x_14; 
x_12 = lean_unbox(x_4);
lean_dec(x_4);
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(x_1, x_2, x_3, x_12, x_13, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_8 = l_Lean_Environment_isProjectionFn(x_7, x_1);
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
x_13 = l_Lean_Environment_isProjectionFn(x_12, x_1);
x_14 = lean_box(x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_11);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
lean_inc(x_1);
x_5 = l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___redArg(x_1, x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_isReducible___at_____private_Lean_Meta_GetUnfoldableConst_0__Lean_Meta_canUnfoldDefault_spec__2(x_1, x_2, x_3, x_7);
x_9 = lean_unbox(x_6);
if (x_9 == 0)
{
lean_dec(x_6);
return x_8;
}
else
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_8, 0);
lean_dec(x_11);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_8, 1);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_6);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_isProjectionFn___at___Lean_Meta_SimpTheorems_ignoreEquations_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_ignoreEquations___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_ignoreEquations(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = lean_ctor_get(x_4, 1);
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_1);
x_9 = l_Lean_Meta_hasSmartUnfoldingDecl(x_8, x_1);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
lean_free_object(x_4);
x_10 = l_Lean_Meta_isRecursiveDefinition___redArg(x_1, x_2, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_unbox(x_11);
lean_dec(x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_10);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_10, 0);
lean_dec(x_14);
x_15 = lean_box(1);
lean_ctor_set(x_10, 0, x_15);
return x_10;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_10, 1);
lean_inc(x_16);
lean_dec(x_10);
x_17 = lean_box(1);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_ctor_get(x_10, 0);
lean_dec(x_20);
x_21 = lean_box(x_9);
lean_ctor_set(x_10, 0, x_21);
return x_10;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_box(x_9);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_22);
return x_24;
}
}
}
else
{
lean_object* x_25; 
lean_dec(x_1);
x_25 = lean_box(x_9);
lean_ctor_set(x_4, 0, x_25);
return x_4;
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_4, 0);
x_27 = lean_ctor_get(x_4, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_4);
x_28 = lean_ctor_get(x_26, 0);
lean_inc(x_28);
lean_dec(x_26);
lean_inc(x_1);
x_29 = l_Lean_Meta_hasSmartUnfoldingDecl(x_28, x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = l_Lean_Meta_isRecursiveDefinition___redArg(x_1, x_2, x_27);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_34 = x_30;
} else {
 lean_dec_ref(x_30);
 x_34 = lean_box(0);
}
x_35 = lean_box(1);
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
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 lean_ctor_release(x_30, 1);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_box(x_29);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(0, 2, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_37);
return x_40;
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_1);
x_41 = lean_box(x_29);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_27);
return x_42;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___redArg(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_ctor_get(x_4, 1);
x_13 = lean_nat_dec_lt(x_6, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_5);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_24; uint8_t x_25; 
x_15 = lean_array_fget(x_1, x_6);
x_24 = lean_unsigned_to_nat(100u);
x_25 = lean_nat_dec_lt(x_24, x_3);
if (x_25 == 0)
{
lean_object* x_26; 
x_26 = lean_nat_sub(x_24, x_6);
x_16 = x_26;
goto block_23;
}
else
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_6, x_27);
x_29 = lean_nat_dec_eq(x_28, x_3);
lean_dec(x_28);
if (x_29 == 0)
{
x_16 = x_27;
goto block_23;
}
else
{
lean_object* x_30; 
x_30 = lean_unsigned_to_nat(0u);
x_16 = x_30;
goto block_23;
}
}
block_23:
{
lean_object* x_17; 
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
x_17 = l_Lean_Meta_SimpTheorems_addConst(x_5, x_15, x_13, x_2, x_16, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_4, 2);
x_21 = lean_nat_add(x_6, x_20);
lean_dec(x_6);
x_5 = x_18;
x_6 = x_21;
x_11 = x_19;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_10, x_11, x_12, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
lean_inc(x_2);
x_8 = l_Lean_Meta_SimpTheorems_ignoreEquations(x_2, x_5, x_6, x_7);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_unbox(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
x_12 = l_Lean_Meta_getEqnsFor_x3f(x_2, x_3, x_4, x_5, x_6, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_unsigned_to_nat(0u);
x_23 = lean_array_get_size(x_21);
x_24 = lean_unsigned_to_nat(1u);
lean_inc(x_23);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_22);
lean_ctor_set(x_25, 1, x_23);
lean_ctor_set(x_25, 2, x_24);
x_26 = lean_unbox(x_9);
lean_dec(x_9);
lean_inc(x_6);
x_27 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___redArg(x_21, x_26, x_23, x_25, x_1, x_22, x_3, x_4, x_5, x_6, x_20);
lean_dec(x_25);
lean_dec(x_23);
lean_dec(x_21);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_2);
x_30 = l_Lean_Meta_SimpTheorems_unfoldEvenWithEqns___redArg(x_2, x_6, x_29);
lean_dec(x_6);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
uint8_t x_33; 
lean_dec(x_2);
x_33 = !lean_is_exclusive(x_30);
if (x_33 == 0)
{
lean_object* x_34; 
x_34 = lean_ctor_get(x_30, 0);
lean_dec(x_34);
lean_ctor_set(x_30, 0, x_28);
return x_30;
}
else
{
lean_object* x_35; lean_object* x_36; 
x_35 = lean_ctor_get(x_30, 1);
lean_inc(x_35);
lean_dec(x_30);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_28);
lean_ctor_set(x_36, 1, x_35);
return x_36;
}
}
else
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_30);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_30, 0);
lean_dec(x_38);
x_39 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_28, x_2);
lean_ctor_set(x_30, 0, x_39);
return x_30;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_30, 1);
lean_inc(x_40);
lean_dec(x_30);
x_41 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_28, x_2);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_40);
return x_42;
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_2);
return x_27;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_12);
if (x_43 == 0)
{
return x_12;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_44 = lean_ctor_get(x_12, 0);
x_45 = lean_ctor_get(x_12, 1);
lean_inc(x_45);
lean_inc(x_44);
lean_dec(x_12);
x_46 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
uint8_t x_47; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_47 = !lean_is_exclusive(x_8);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_8, 0);
lean_dec(x_48);
x_49 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
lean_ctor_set(x_8, 0, x_49);
return x_8;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_8, 1);
lean_inc(x_50);
lean_dec(x_8);
x_51 = l_Lean_Meta_SimpTheorems_addDeclToUnfoldCore(x_1, x_2);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_50);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_2);
lean_dec(x_2);
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___redArg(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_2);
lean_dec(x_2);
x_15 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_SimpTheorems_addDeclToUnfold_spec__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_addDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Meta_SimpTheorems_addDeclToUnfold(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; 
x_14 = l_Lean_Expr_isConst(x_4);
if (x_14 == 0)
{
lean_object* x_15; uint64_t x_16; uint8_t x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_15 = lean_ctor_get(x_8, 0);
x_16 = lean_ctor_get_uint64(x_8, sizeof(void*)*1);
x_17 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 8);
x_18 = lean_ctor_get(x_9, 1);
x_19 = lean_ctor_get(x_9, 2);
x_20 = lean_ctor_get(x_9, 3);
x_21 = lean_ctor_get(x_9, 4);
x_22 = lean_ctor_get(x_9, 5);
x_23 = lean_ctor_get(x_9, 6);
x_24 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 9);
x_25 = lean_ctor_get_uint8(x_9, sizeof(void*)*7 + 10);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_15);
x_26 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_26, 0, x_15);
lean_ctor_set(x_26, 1, x_18);
lean_ctor_set(x_26, 2, x_19);
lean_ctor_set(x_26, 3, x_20);
lean_ctor_set(x_26, 4, x_21);
lean_ctor_set(x_26, 5, x_22);
lean_ctor_set(x_26, 6, x_23);
lean_ctor_set_uint64(x_26, sizeof(void*)*7, x_16);
lean_ctor_set_uint8(x_26, sizeof(void*)*7 + 8, x_17);
lean_ctor_set_uint8(x_26, sizeof(void*)*7 + 9, x_24);
lean_ctor_set_uint8(x_26, sizeof(void*)*7 + 10, x_25);
x_27 = l___private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_mkSimpTheorems(x_2, x_3, x_4, x_6, x_5, x_7, x_26, x_10, x_11, x_12, x_13);
lean_dec(x_26);
if (lean_obj_tag(x_27) == 0)
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_29);
x_32 = lean_nat_dec_lt(x_30, x_31);
if (x_32 == 0)
{
lean_dec(x_31);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_31, x_31);
if (x_33 == 0)
{
lean_dec(x_31);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_1);
return x_27;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
x_34 = lean_usize_of_nat(x_30);
x_35 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_36 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_29, x_34, x_35, x_1);
lean_dec(x_29);
lean_ctor_set(x_27, 0, x_36);
return x_27;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_27, 0);
x_38 = lean_ctor_get(x_27, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_array_get_size(x_37);
x_41 = lean_nat_dec_lt(x_39, x_40);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_40);
lean_dec(x_37);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_1);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_40, x_40);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_40);
lean_dec(x_37);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_38);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_usize_of_nat(x_39);
x_46 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_Meta_SimpTheorems_addConst_spec__0(x_37, x_45, x_46, x_1);
lean_dec(x_37);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_38);
return x_48;
}
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_27);
if (x_49 == 0)
{
return x_27;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_27, 0);
x_51 = lean_ctor_get(x_27, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_27);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_3);
lean_dec(x_2);
x_53 = l_Lean_Expr_constName_x21(x_4);
lean_dec(x_4);
x_54 = l_Lean_Meta_SimpTheorems_addConst(x_1, x_53, x_6, x_5, x_7, x_9, x_10, x_11, x_12, x_13);
return x_54;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheorems_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; uint8_t x_15; lean_object* x_16; 
x_14 = lean_unbox(x_5);
lean_dec(x_5);
x_15 = lean_unbox(x_6);
lean_dec(x_6);
x_16 = l_Lean_Meta_SimpTheorems_add(x_1, x_2, x_3, x_4, x_14, x_15, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_9);
lean_dec(x_8);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = l_Array_isEmpty___redArg(x_1);
x_11 = lean_box(1);
if (x_10 == 0)
{
lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_array_get_size(x_1);
x_14 = lean_nat_dec_lt(x_12, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_1);
lean_ctor_set(x_15, 1, x_9);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_16 = lean_array_fget(x_1, x_12);
x_17 = lean_mk_empty_array_with_capacity(x_12);
x_18 = lean_unsigned_to_nat(1000u);
x_19 = lean_unbox(x_11);
x_20 = l_Lean_Meta_SimpTheorems_add(x_16, x_2, x_17, x_3, x_10, x_19, x_18, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_box(0);
x_24 = lean_array_fset(x_1, x_12, x_23);
x_25 = lean_array_fset(x_24, x_12, x_22);
lean_ctor_set(x_20, 0, x_25);
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_box(0);
x_29 = lean_array_fset(x_1, x_12, x_28);
x_30 = lean_array_fset(x_29, x_12, x_26);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_20);
if (x_32 == 0)
{
return x_20;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_20);
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
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_47; lean_object* x_48; 
lean_dec(x_1);
x_36 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_37 = l_Lean_PersistentHashMap_empty___at___Lean_Meta_mkSimpExt_spec__0(lean_box(0));
x_38 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
x_39 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_inc(x_37);
lean_inc(x_36);
x_41 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_41, 0, x_36);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_41, 2, x_37);
lean_ctor_set(x_41, 3, x_38);
lean_ctor_set(x_41, 4, x_37);
lean_ctor_set(x_41, 5, x_40);
x_42 = lean_unsigned_to_nat(0u);
x_43 = lean_mk_empty_array_with_capacity(x_42);
x_44 = lean_box(0);
x_45 = lean_unsigned_to_nat(1000u);
x_46 = lean_unbox(x_44);
x_47 = lean_unbox(x_11);
x_48 = l_Lean_Meta_SimpTheorems_add(x_41, x_2, x_43, x_3, x_46, x_47, x_45, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_48) == 0)
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_50 = lean_ctor_get(x_48, 0);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_mk_empty_array_with_capacity(x_51);
x_53 = lean_array_push(x_52, x_50);
lean_ctor_set(x_48, 0, x_53);
return x_48;
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = lean_ctor_get(x_48, 1);
lean_inc(x_55);
lean_inc(x_54);
lean_dec(x_48);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_mk_empty_array_with_capacity(x_56);
x_58 = lean_array_push(x_57, x_54);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_55);
return x_59;
}
}
else
{
uint8_t x_60; 
x_60 = !lean_is_exclusive(x_48);
if (x_60 == 0)
{
return x_48;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_48, 0);
x_62 = lean_ctor_get(x_48, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_48);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_addTheorem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Meta_SimpTheoremsArray_addTheorem(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_lt(x_3, x_2);
if (x_5 == 0)
{
lean_dec(x_1);
return x_4;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_6 = lean_array_uget(x_4, x_3);
x_7 = lean_box(0);
x_8 = lean_array_uset(x_4, x_3, x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_SimpTheorems_eraseCore(x_6, x_1);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_add(x_3, x_11);
x_13 = lean_array_uset(x_8, x_3, x_9);
x_3 = x_12;
x_4 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_eraseTheorem(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(x_2, x_3, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Meta_SimpTheoremsArray_eraseTheorem_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_PersistentHashMap_contains___at_____private_Lean_Meta_Tactic_Simp_SimpTheorems_0__Lean_Meta_eraseIfExists_spec__0___redArg(x_7, x_1);
if (x_8 == 0)
{
lean_object* x_9; size_t x_10; size_t x_11; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_3, x_10);
x_3 = x_11;
goto _start;
}
else
{
return x_8;
}
}
else
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_box(0);
x_14 = lean_unbox(x_13);
return x_14;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isErased(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isErased_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isErased___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isErased(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Meta_SimpTheorems_isDeclToUnfold(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isDeclToUnfold_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isDeclToUnfold(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = l_Lean_Meta_SimpTheorems_isLetDeclToUnfold(x_6, x_1);
if (x_7 == 0)
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
goto _start;
}
else
{
return x_7;
}
}
else
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(0);
x_13 = lean_unbox(x_12);
return x_13;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_3, x_4);
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
if (x_5 == 0)
{
lean_dec(x_4);
return x_5;
}
else
{
size_t x_6; size_t x_7; uint8_t x_8; 
x_6 = lean_usize_of_nat(x_3);
x_7 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_SimpTheoremsArray_isLetDeclToUnfold(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Util_Recognizers(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_AppBuilder(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Eqns(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_AuxLemma(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_DocString(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_PrettyPrinter(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_SimpTheorems(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Util_Recognizers(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_AppBuilder(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Eqns(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_AuxLemma(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_instInhabitedOrigin = _init_l_Lean_Meta_instInhabitedOrigin();
lean_mark_persistent(l_Lean_Meta_instInhabitedOrigin);
l_Lean_Meta_instReprOrigin = _init_l_Lean_Meta_instReprOrigin();
lean_mark_persistent(l_Lean_Meta_instReprOrigin);
l_Lean_Meta_instBEqOrigin = _init_l_Lean_Meta_instBEqOrigin();
lean_mark_persistent(l_Lean_Meta_instBEqOrigin);
l_Lean_Meta_instHashableOrigin = _init_l_Lean_Meta_instHashableOrigin();
lean_mark_persistent(l_Lean_Meta_instHashableOrigin);
l_Lean_Meta_instLTOrigin = _init_l_Lean_Meta_instLTOrigin();
lean_mark_persistent(l_Lean_Meta_instLTOrigin);
l_Lean_Meta_instInhabitedSimpTheorem = _init_l_Lean_Meta_instInhabitedSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorem);
l_Lean_Meta_instToFormatSimpTheorem = _init_l_Lean_Meta_instToFormatSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instToFormatSimpTheorem);
l_Lean_Meta_instBEqSimpTheorem = _init_l_Lean_Meta_instBEqSimpTheorem();
lean_mark_persistent(l_Lean_Meta_instBEqSimpTheorem);
l_Lean_Meta_instInhabitedSimpTheorems = _init_l_Lean_Meta_instInhabitedSimpTheorems();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpTheorems);
l_Lean_Meta_simpGlobalConfig = _init_l_Lean_Meta_simpGlobalConfig();
lean_mark_persistent(l_Lean_Meta_simpGlobalConfig);
l_Lean_Meta_instInhabitedSimpEntry = _init_l_Lean_Meta_instInhabitedSimpEntry();
lean_mark_persistent(l_Lean_Meta_instInhabitedSimpEntry);
l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5516_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5516_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5516_);
if (builtin) {res = l_Lean_Meta_initFn____x40_Lean_Meta_Tactic_Simp_SimpTheorems___hyg_5574_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_simpExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_simpExtensionMapRef);
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
