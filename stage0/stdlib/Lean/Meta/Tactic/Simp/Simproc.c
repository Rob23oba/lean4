// Lean compiler output
// Module: Lean.Meta.Tactic.Simp.Simproc
// Imports: Lean.ScopedEnvExtension Lean.Compiler.InitAttr Lean.Meta.DiscrTree Lean.Meta.Tactic.Simp.Types
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6000_(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_addInstanceEntry_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocArrayCore_spec__0(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_SimprocsArray_isErased_spec__0(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3___boxed(lean_object*, lean_object*);
lean_object* lean_name_append_after(lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Array_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6144_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_qpartition___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* l_Lean_ScopedEnvExtension_add___at___Lean_KeyedDeclsAttribute_init_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_modifyState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6114_(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getState(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6044_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_DStep_addExtraArgs(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_quickLt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocArrayCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Level_ofNat(lean_object*);
lean_object* l_Lean_Expr_appArg_x21(lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocDecl_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5382_(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_createNodes___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_initializing(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocs;
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSimprocsRef;
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_declareBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry;
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocArrayCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_eval_const(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_TransformStep_toStep(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_isErased___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5717_;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__0(lean_object*);
lean_object* l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_SimprocsArray_isErased_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerPersistentEnvExtensionUnsafe___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerScopedEnvExtensionUnsafe___redArg(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedSimprocDecl;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_59_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_appFn_x21(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry;
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_usize_to_nat(size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0___boxed(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
extern lean_object* l_Lean_Meta_Simp_instInhabitedSimprocs;
lean_object* l_Lean_Meta_Simp_mkEqTransOptProofResult(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_mkEqTrans_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1178_(lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1143_(lean_object*);
lean_object* l_Lean_Meta_Simp_Step_addExtraArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_DiscrTree_instInhabitedKey;
lean_object* l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_Simp_recordSimpTheorem___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4(lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocArrayCore_spec__0(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_mkApp3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__0___boxed(lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0_spec__0(lean_object*, uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_modifyState___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocsArray_isErased(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSimprocDeclsRef;
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0(lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__2____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_SimprocsArray_erase_spec__0(lean_object*, size_t, size_t, lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerBuiltinAttribute(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocDecl_lt___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l___private_Lean_ToExpr_0__Lean_Name_toExprAux(lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocExtensionMapRef;
lean_object* l_Lean_PersistentHashMap_find_x3f___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_getStarResult_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_io_error_to_string(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocSEvalExtension;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object*, lean_object*);
extern lean_object* l_Lean_Name_instBEq;
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_builtinSEvalprocsRef;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_getModuleEntries___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__5(lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocDeclExt;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocExtension;
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_SimprocsArray_erase_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_instHashableName;
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
lean_inc(x_10);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_59_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
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
lean_inc(x_11);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_st_mk_ref(x_12, x_1);
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
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
return x_17;
}
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Array_empty(lean_box(0));
x_3 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_1 = lean_unsigned_to_nat(8u);
x_2 = lean_unsigned_to_nat(0u);
x_3 = lean_unsigned_to_nat(2u);
x_4 = lean_nat_shiftl(x_1, x_3);
x_5 = lean_unsigned_to_nat(3u);
x_6 = lean_nat_div(x_4, x_5);
lean_dec(x_4);
x_7 = l_Nat_nextPowerOfTwo(x_6);
lean_dec(x_6);
x_8 = lean_box(0);
x_9 = lean_mk_array(x_7, x_8);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
x_11 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocDecl_lt(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Name_quickLt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocDecl_lt___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_SimprocDecl_lt(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_nat_dec_lt(x_2, x_3);
if (x_4 == 0)
{
lean_dec(x_2);
return x_1;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_SimprocDecl_lt___boxed), 2, 0);
lean_inc(x_2);
x_6 = l_Array_qpartition___redArg(x_1, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_nat_dec_le(x_3, x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg(x_8, x_2, x_7);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_7, x_11);
lean_dec(x_7);
x_1 = x_10;
x_2 = x_12;
goto _start;
}
else
{
lean_dec(x_7);
lean_dec(x_2);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg(x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_array_push(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_box(0);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__2____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_5 = lean_ctor_get(x_2, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_4, x_5, x_6);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_5 = lean_ctor_get(x_4, 1);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_mk_empty_array_with_capacity(x_6);
x_8 = l_Lean_PersistentHashMap_foldlM___at___Lean_PersistentHashMap_foldl_spec__0(lean_box(0), x_1, x_2, lean_box(0), lean_box(0), x_5, x_3, x_7);
x_9 = lean_array_get_size(x_8);
x_10 = lean_nat_dec_eq(x_9, x_6);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_16; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_9, x_11);
lean_dec(x_9);
x_16 = lean_nat_dec_le(x_6, x_12);
if (x_16 == 0)
{
lean_inc(x_12);
x_13 = x_12;
goto block_15;
}
else
{
x_13 = x_6;
goto block_15;
}
block_15:
{
lean_object* x_14; 
x_14 = l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg(x_8, x_13, x_12);
lean_dec(x_12);
return x_14;
}
}
else
{
lean_dec(x_9);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
lean_dec(x_5);
x_7 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_6);
lean_ctor_set(x_9, 1, x_8);
lean_ctor_set(x_3, 0, x_9);
return x_3;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_11);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_1, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_12 = lean_ctor_get(x_5, 0);
x_13 = lean_ctor_get(x_5, 1);
lean_inc(x_13);
lean_inc(x_12);
lean_dec(x_5);
x_14 = lean_ctor_get(x_12, 0);
lean_inc(x_14);
lean_dec(x_12);
x_15 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_16 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_13);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_), 3, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed), 1, 0);
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__2____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_), 2, 0);
x_5 = l_Lean_Name_instBEq;
x_6 = l_Lean_instHashableName;
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__3____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed), 4, 3);
lean_closure_set(x_7, 0, x_5);
lean_closure_set(x_7, 1, x_6);
lean_closure_set(x_7, 2, x_2);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = lean_mk_string_unchecked("Simp", 4, 4);
x_11 = lean_mk_string_unchecked("simprocDeclExt", 14, 14);
x_12 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_11);
x_13 = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
x_14 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__4____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed), 2, 1);
lean_closure_set(x_14, 0, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__5____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed), 4, 1);
lean_closure_set(x_15, 0, x_13);
x_16 = lean_box(2);
x_17 = lean_box(0);
lean_inc(x_7);
x_18 = lean_alloc_ctor(0, 8, 1);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_14);
lean_ctor_set(x_18, 2, x_15);
lean_ctor_set(x_18, 3, x_4);
lean_ctor_set(x_18, 4, x_7);
lean_ctor_set(x_18, 5, x_7);
lean_ctor_set(x_18, 6, x_3);
lean_ctor_set(x_18, 7, x_17);
x_19 = lean_unbox(x_16);
lean_ctor_set_uint8(x_18, sizeof(void*)*8, x_19);
x_20 = l_Lean_registerPersistentEnvExtensionUnsafe___redArg(x_18, x_1);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Array_qsort_sort___at___Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187__spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__3____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_initFn___lam__3____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__4____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_initFn___lam__4____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__5____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_initFn___lam__5____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_5 = lean_nat_add(x_3, x_4);
x_6 = lean_unsigned_to_nat(1u);
x_7 = lean_nat_shiftr(x_5, x_6);
lean_dec(x_5);
x_8 = lean_array_fget(x_1, x_7);
x_9 = l_Lean_Meta_Simp_SimprocDecl_lt(x_8, x_2);
if (x_9 == 0)
{
uint8_t x_10; 
lean_dec(x_4);
x_10 = l_Lean_Meta_Simp_SimprocDecl_lt(x_2, x_8);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_3);
x_11 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_11, 0, x_8);
return x_11;
}
else
{
lean_object* x_12; uint8_t x_13; 
lean_dec(x_8);
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_nat_dec_eq(x_7, x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_nat_sub(x_7, x_6);
lean_dec(x_7);
x_15 = lean_nat_dec_lt(x_14, x_3);
if (x_15 == 0)
{
x_4 = x_14;
goto _start;
}
else
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_3);
x_17 = lean_box(0);
return x_17;
}
}
else
{
lean_object* x_18; 
lean_dec(x_7);
lean_dec(x_3);
x_18 = lean_box(0);
return x_18;
}
}
}
else
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_8);
lean_dec(x_3);
x_19 = lean_nat_add(x_7, x_6);
lean_dec(x_7);
x_20 = lean_nat_dec_le(x_19, x_4);
if (x_20 == 0)
{
lean_object* x_21; 
lean_dec(x_19);
lean_dec(x_4);
x_21 = lean_box(0);
return x_21;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_36; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
if (lean_is_exclusive(x_4)) {
 lean_ctor_release(x_4, 0);
 lean_ctor_release(x_4, 1);
 x_7 = x_4;
} else {
 lean_dec_ref(x_4);
 x_7 = lean_box(0);
}
x_8 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_9 = lean_ctor_get(x_5, 0);
lean_inc(x_9);
lean_dec(x_5);
x_36 = l_Lean_Environment_getModuleIdxFor_x3f(x_9, x_1);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_37 = l_Lean_Meta_Simp_simprocDeclExt;
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get_uint8(x_38, sizeof(void*)*3);
lean_dec(x_38);
lean_inc(x_9);
x_40 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_8, x_37, x_9, x_39);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = l_Lean_PersistentHashMap_find_x3f___at___Lean_MetavarContext_findUserName_x3f_spec__0(lean_box(0), x_41, x_1);
if (lean_obj_tag(x_42) == 0)
{
goto block_35;
}
else
{
lean_object* x_43; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_6);
return x_43;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_44 = lean_ctor_get(x_36, 0);
lean_inc(x_44);
lean_dec(x_36);
x_45 = l_Lean_Meta_Simp_simprocDeclExt;
x_46 = lean_box(0);
x_47 = lean_unbox(x_46);
x_48 = l_Lean_PersistentEnvExtension_getModuleEntries___redArg(x_8, x_45, x_9, x_44, x_47);
lean_dec(x_44);
x_49 = lean_unsigned_to_nat(0u);
x_50 = lean_array_get_size(x_48);
x_51 = lean_nat_dec_lt(x_49, x_50);
if (x_51 == 0)
{
lean_dec(x_50);
lean_dec(x_48);
goto block_35;
}
else
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_nat_sub(x_50, x_52);
lean_dec(x_50);
x_54 = lean_nat_dec_le(x_49, x_53);
if (x_54 == 0)
{
lean_dec(x_53);
lean_dec(x_48);
goto block_35;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_mk_empty_array_with_capacity(x_49);
lean_inc(x_1);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_55);
x_57 = l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(x_48, x_56, x_49, x_53);
lean_dec(x_56);
lean_dec(x_48);
if (lean_obj_tag(x_57) == 0)
{
goto block_35;
}
else
{
uint8_t x_58; 
lean_dec(x_9);
lean_dec(x_7);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_57, 0);
x_60 = lean_ctor_get(x_59, 1);
lean_inc(x_60);
lean_dec(x_59);
lean_ctor_set(x_57, 0, x_60);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_57);
lean_ctor_set(x_61, 1, x_6);
return x_61;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_57, 0);
lean_inc(x_62);
lean_dec(x_57);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
lean_dec(x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_6);
return x_65;
}
}
}
}
}
block_35:
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; lean_object* x_22; uint64_t x_23; uint64_t x_24; uint64_t x_25; size_t x_26; size_t x_27; lean_object* x_28; size_t x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_10 = l_Lean_Meta_Simp_simprocDeclExt;
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get_uint8(x_11, sizeof(void*)*3);
lean_dec(x_11);
x_13 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_8, x_10, x_9, x_12);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_array_get_size(x_15);
x_17 = l_Lean_Name_hash___override(x_1);
x_18 = lean_unsigned_to_nat(32u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_unsigned_to_nat(16u);
x_23 = lean_uint64_of_nat(x_22);
x_24 = lean_uint64_shift_right(x_21, x_23);
x_25 = lean_uint64_xor(x_21, x_24);
x_26 = lean_uint64_to_usize(x_25);
x_27 = lean_usize_of_nat(x_16);
lean_dec(x_16);
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_usize_of_nat(x_28);
x_30 = lean_usize_sub(x_27, x_29);
x_31 = lean_usize_land(x_26, x_30);
x_32 = lean_array_uget(x_15, x_31);
lean_dec(x_15);
x_33 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_1, x_32);
lean_dec(x_32);
lean_dec(x_1);
if (lean_is_scalar(x_7)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_7;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_6);
return x_34;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binSearchAux___at___Lean_Meta_Simp_getSimprocDeclKeys_x3f_spec__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec(x_6);
x_9 = l_Lean_Meta_Simp_simprocDeclExt;
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get_uint8(x_10, sizeof(void*)*3);
lean_dec(x_10);
x_12 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_7, x_9, x_8, x_11);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_array_get_size(x_14);
x_16 = l_Lean_Name_hash___override(x_1);
x_17 = lean_unsigned_to_nat(32u);
x_18 = lean_uint64_of_nat(x_17);
x_19 = lean_uint64_shift_right(x_16, x_18);
x_20 = lean_uint64_xor(x_16, x_19);
x_21 = lean_unsigned_to_nat(16u);
x_22 = lean_uint64_of_nat(x_21);
x_23 = lean_uint64_shift_right(x_20, x_22);
x_24 = lean_uint64_xor(x_20, x_23);
x_25 = lean_uint64_to_usize(x_24);
x_26 = lean_usize_of_nat(x_15);
lean_dec(x_15);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_usize_of_nat(x_27);
x_29 = lean_usize_sub(x_26, x_28);
x_30 = lean_usize_land(x_25, x_29);
x_31 = lean_array_uget(x_14, x_30);
lean_dec(x_14);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_31);
lean_dec(x_31);
x_33 = lean_box(x_32);
lean_ctor_set(x_4, 0, x_33);
return x_4;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; lean_object* x_50; uint64_t x_51; uint64_t x_52; uint64_t x_53; size_t x_54; size_t x_55; lean_object* x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; lean_object* x_62; lean_object* x_63; 
x_34 = lean_ctor_get(x_4, 0);
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_inc(x_34);
lean_dec(x_4);
x_36 = l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState;
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = l_Lean_Meta_Simp_simprocDeclExt;
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get_uint8(x_39, sizeof(void*)*3);
lean_dec(x_39);
x_41 = l_Lean_PersistentEnvExtension_getState(lean_box(0), lean_box(0), lean_box(0), x_36, x_38, x_37, x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_array_get_size(x_43);
x_45 = l_Lean_Name_hash___override(x_1);
x_46 = lean_unsigned_to_nat(32u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_xor(x_45, x_48);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_uint64_of_nat(x_50);
x_52 = lean_uint64_shift_right(x_49, x_51);
x_53 = lean_uint64_xor(x_49, x_52);
x_54 = lean_uint64_to_usize(x_53);
x_55 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_usize_of_nat(x_56);
x_58 = lean_usize_sub(x_55, x_57);
x_59 = lean_usize_land(x_54, x_58);
x_60 = lean_array_uget(x_43, x_59);
lean_dec(x_43);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_60);
lean_dec(x_60);
x_62 = lean_box(x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_35);
return x_63;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isBuiltinSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_isBuiltinSimproc(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(x_1, x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_4, 0);
lean_dec(x_7);
x_8 = lean_box(0);
lean_ctor_set(x_4, 0, x_8);
return x_4;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
lean_dec(x_4);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
}
else
{
uint8_t x_12; 
lean_dec(x_5);
x_12 = !lean_is_exclusive(x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_4, 0);
lean_dec(x_13);
x_14 = lean_box(1);
lean_ctor_set(x_4, 0, x_14);
return x_4;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = lean_box(1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_isSimproc___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_isSimproc___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_isSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_isSimproc(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = l_Lean_initializing(x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_unbox(x_6);
lean_dec(x_6);
if (x_7 == 0)
{
uint8_t x_8; 
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_5, 0);
lean_dec(x_9);
x_10 = lean_mk_string_unchecked("invalid builtin simproc declaration, it can only be registered during initialization", 84, 84);
x_11 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set_tag(x_5, 1);
lean_ctor_set(x_5, 0, x_11);
return x_5;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_dec(x_5);
x_13 = lean_mk_string_unchecked("invalid builtin simproc declaration, it can only be registered during initialization", 84, 84);
x_14 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec(x_5);
x_17 = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
x_18 = lean_st_ref_get(x_17, x_16);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
lean_dec(x_19);
x_21 = !lean_is_exclusive(x_18);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_22 = lean_ctor_get(x_18, 1);
x_23 = lean_ctor_get(x_18, 0);
lean_dec(x_23);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Name_hash___override(x_1);
x_27 = lean_unsigned_to_nat(32u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_sub(x_36, x_38);
x_40 = lean_usize_land(x_35, x_39);
x_41 = lean_array_uget(x_24, x_40);
lean_dec(x_24);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_41);
lean_dec(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_108; 
lean_free_object(x_18);
x_43 = lean_st_ref_take(x_17, x_22);
x_44 = lean_ctor_get(x_43, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_43, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_43)) {
 lean_ctor_release(x_43, 0);
 lean_ctor_release(x_43, 1);
 x_46 = x_43;
} else {
 lean_dec_ref(x_43);
 x_46 = lean_box(0);
}
x_56 = lean_ctor_get(x_44, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_44, 1);
lean_inc(x_57);
lean_dec(x_44);
x_108 = !lean_is_exclusive(x_56);
if (x_108 == 0)
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; uint8_t x_116; 
x_109 = lean_ctor_get(x_56, 0);
x_110 = lean_ctor_get(x_56, 1);
x_111 = lean_array_get_size(x_110);
x_112 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_113 = lean_usize_sub(x_112, x_38);
x_114 = lean_usize_land(x_35, x_113);
x_115 = lean_array_uget(x_110, x_114);
x_116 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_117 = lean_nat_add(x_109, x_37);
lean_dec(x_109);
lean_inc(x_1);
x_118 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_118, 0, x_1);
lean_ctor_set(x_118, 1, x_2);
lean_ctor_set(x_118, 2, x_115);
x_119 = lean_array_uset(x_110, x_114, x_118);
x_120 = lean_unsigned_to_nat(2u);
x_121 = lean_nat_shiftl(x_117, x_120);
x_122 = lean_unsigned_to_nat(3u);
x_123 = lean_nat_div(x_121, x_122);
lean_dec(x_121);
x_124 = lean_array_get_size(x_119);
x_125 = lean_nat_dec_le(x_123, x_124);
lean_dec(x_124);
lean_dec(x_123);
if (x_125 == 0)
{
lean_object* x_126; 
x_126 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_119);
lean_ctor_set(x_56, 1, x_126);
lean_ctor_set(x_56, 0, x_117);
x_58 = x_56;
goto block_107;
}
else
{
lean_ctor_set(x_56, 1, x_119);
lean_ctor_set(x_56, 0, x_117);
x_58 = x_56;
goto block_107;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_127 = lean_box(0);
x_128 = lean_array_uset(x_110, x_114, x_127);
lean_inc(x_1);
x_129 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_2, x_115);
x_130 = lean_array_uset(x_128, x_114, x_129);
lean_ctor_set(x_56, 1, x_130);
x_58 = x_56;
goto block_107;
}
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; size_t x_134; size_t x_135; size_t x_136; lean_object* x_137; uint8_t x_138; 
x_131 = lean_ctor_get(x_56, 0);
x_132 = lean_ctor_get(x_56, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_56);
x_133 = lean_array_get_size(x_132);
x_134 = lean_usize_of_nat(x_133);
lean_dec(x_133);
x_135 = lean_usize_sub(x_134, x_38);
x_136 = lean_usize_land(x_35, x_135);
x_137 = lean_array_uget(x_132, x_136);
x_138 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_139 = lean_nat_add(x_131, x_37);
lean_dec(x_131);
lean_inc(x_1);
x_140 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_2);
lean_ctor_set(x_140, 2, x_137);
x_141 = lean_array_uset(x_132, x_136, x_140);
x_142 = lean_unsigned_to_nat(2u);
x_143 = lean_nat_shiftl(x_139, x_142);
x_144 = lean_unsigned_to_nat(3u);
x_145 = lean_nat_div(x_143, x_144);
lean_dec(x_143);
x_146 = lean_array_get_size(x_141);
x_147 = lean_nat_dec_le(x_145, x_146);
lean_dec(x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; 
x_148 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_141);
x_149 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_149, 0, x_139);
lean_ctor_set(x_149, 1, x_148);
x_58 = x_149;
goto block_107;
}
else
{
lean_object* x_150; 
x_150 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_150, 0, x_139);
lean_ctor_set(x_150, 1, x_141);
x_58 = x_150;
goto block_107;
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; 
x_151 = lean_box(0);
x_152 = lean_array_uset(x_132, x_136, x_151);
lean_inc(x_1);
x_153 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_2, x_137);
x_154 = lean_array_uset(x_152, x_136, x_153);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_131);
lean_ctor_set(x_155, 1, x_154);
x_58 = x_155;
goto block_107;
}
}
block_55:
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
if (lean_is_scalar(x_46)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_46;
}
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_st_ref_set(x_17, x_49, x_45);
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
return x_50;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_50, 0);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_50);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
block_107:
{
uint8_t x_59; 
x_59 = !lean_is_exclusive(x_57);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; size_t x_63; size_t x_64; size_t x_65; lean_object* x_66; uint8_t x_67; 
x_60 = lean_ctor_get(x_57, 0);
x_61 = lean_ctor_get(x_57, 1);
x_62 = lean_array_get_size(x_61);
x_63 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_64 = lean_usize_sub(x_63, x_38);
x_65 = lean_usize_land(x_35, x_64);
x_66 = lean_array_uget(x_61, x_65);
x_67 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint8_t x_76; 
x_68 = lean_nat_add(x_60, x_37);
lean_dec(x_60);
x_69 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_69, 0, x_1);
lean_ctor_set(x_69, 1, x_3);
lean_ctor_set(x_69, 2, x_66);
x_70 = lean_array_uset(x_61, x_65, x_69);
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
lean_object* x_77; 
x_77 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_70);
lean_ctor_set(x_57, 1, x_77);
lean_ctor_set(x_57, 0, x_68);
x_47 = x_58;
x_48 = x_57;
goto block_55;
}
else
{
lean_ctor_set(x_57, 1, x_70);
lean_ctor_set(x_57, 0, x_68);
x_47 = x_58;
x_48 = x_57;
goto block_55;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_78 = lean_box(0);
x_79 = lean_array_uset(x_61, x_65, x_78);
x_80 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_66);
x_81 = lean_array_uset(x_79, x_65, x_80);
lean_ctor_set(x_57, 1, x_81);
x_47 = x_58;
x_48 = x_57;
goto block_55;
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_82 = lean_ctor_get(x_57, 0);
x_83 = lean_ctor_get(x_57, 1);
lean_inc(x_83);
lean_inc(x_82);
lean_dec(x_57);
x_84 = lean_array_get_size(x_83);
x_85 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_86 = lean_usize_sub(x_85, x_38);
x_87 = lean_usize_land(x_35, x_86);
x_88 = lean_array_uget(x_83, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_nat_add(x_82, x_37);
lean_dec(x_82);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_3);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_array_uset(x_83, x_87, x_91);
x_93 = lean_unsigned_to_nat(2u);
x_94 = lean_nat_shiftl(x_90, x_93);
x_95 = lean_unsigned_to_nat(3u);
x_96 = lean_nat_div(x_94, x_95);
lean_dec(x_94);
x_97 = lean_array_get_size(x_92);
x_98 = lean_nat_dec_le(x_96, x_97);
lean_dec(x_97);
lean_dec(x_96);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_47 = x_58;
x_48 = x_100;
goto block_55;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
x_47 = x_58;
x_48 = x_101;
goto block_55;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_83, x_87, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_88);
x_105 = lean_array_uset(x_103, x_87, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_82);
lean_ctor_set(x_106, 1, x_105);
x_47 = x_58;
x_48 = x_106;
goto block_55;
}
}
}
}
else
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_3);
lean_dec(x_2);
x_156 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0___boxed), 1, 0);
x_157 = lean_mk_string_unchecked("invalid builtin simproc declaration '", 37, 37);
x_158 = l_Lean_Name_toString(x_1, x_42, x_156);
x_159 = lean_string_append(x_157, x_158);
lean_dec(x_158);
x_160 = lean_mk_string_unchecked("', it has already been declared", 31, 31);
x_161 = lean_string_append(x_159, x_160);
lean_dec(x_160);
x_162 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set_tag(x_18, 1);
lean_ctor_set(x_18, 0, x_162);
return x_18;
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; uint64_t x_166; lean_object* x_167; uint64_t x_168; uint64_t x_169; uint64_t x_170; lean_object* x_171; uint64_t x_172; uint64_t x_173; uint64_t x_174; size_t x_175; size_t x_176; lean_object* x_177; size_t x_178; size_t x_179; size_t x_180; lean_object* x_181; uint8_t x_182; 
x_163 = lean_ctor_get(x_18, 1);
lean_inc(x_163);
lean_dec(x_18);
x_164 = lean_ctor_get(x_20, 1);
lean_inc(x_164);
lean_dec(x_20);
x_165 = lean_array_get_size(x_164);
x_166 = l_Lean_Name_hash___override(x_1);
x_167 = lean_unsigned_to_nat(32u);
x_168 = lean_uint64_of_nat(x_167);
x_169 = lean_uint64_shift_right(x_166, x_168);
x_170 = lean_uint64_xor(x_166, x_169);
x_171 = lean_unsigned_to_nat(16u);
x_172 = lean_uint64_of_nat(x_171);
x_173 = lean_uint64_shift_right(x_170, x_172);
x_174 = lean_uint64_xor(x_170, x_173);
x_175 = lean_uint64_to_usize(x_174);
x_176 = lean_usize_of_nat(x_165);
lean_dec(x_165);
x_177 = lean_unsigned_to_nat(1u);
x_178 = lean_usize_of_nat(x_177);
x_179 = lean_usize_sub(x_176, x_178);
x_180 = lean_usize_land(x_175, x_179);
x_181 = lean_array_uget(x_164, x_180);
lean_dec(x_164);
x_182 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; size_t x_230; size_t x_231; size_t x_232; lean_object* x_233; uint8_t x_234; 
x_183 = lean_st_ref_take(x_17, x_163);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
x_185 = lean_ctor_get(x_183, 1);
lean_inc(x_185);
if (lean_is_exclusive(x_183)) {
 lean_ctor_release(x_183, 0);
 lean_ctor_release(x_183, 1);
 x_186 = x_183;
} else {
 lean_dec_ref(x_183);
 x_186 = lean_box(0);
}
x_196 = lean_ctor_get(x_184, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_184, 1);
lean_inc(x_197);
lean_dec(x_184);
x_226 = lean_ctor_get(x_196, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_196, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_228 = x_196;
} else {
 lean_dec_ref(x_196);
 x_228 = lean_box(0);
}
x_229 = lean_array_get_size(x_227);
x_230 = lean_usize_of_nat(x_229);
lean_dec(x_229);
x_231 = lean_usize_sub(x_230, x_178);
x_232 = lean_usize_land(x_175, x_231);
x_233 = lean_array_uget(x_227, x_232);
x_234 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_233);
if (x_234 == 0)
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; 
x_235 = lean_nat_add(x_226, x_177);
lean_dec(x_226);
lean_inc(x_1);
x_236 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_236, 0, x_1);
lean_ctor_set(x_236, 1, x_2);
lean_ctor_set(x_236, 2, x_233);
x_237 = lean_array_uset(x_227, x_232, x_236);
x_238 = lean_unsigned_to_nat(2u);
x_239 = lean_nat_shiftl(x_235, x_238);
x_240 = lean_unsigned_to_nat(3u);
x_241 = lean_nat_div(x_239, x_240);
lean_dec(x_239);
x_242 = lean_array_get_size(x_237);
x_243 = lean_nat_dec_le(x_241, x_242);
lean_dec(x_242);
lean_dec(x_241);
if (x_243 == 0)
{
lean_object* x_244; lean_object* x_245; 
x_244 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_237);
if (lean_is_scalar(x_228)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_228;
}
lean_ctor_set(x_245, 0, x_235);
lean_ctor_set(x_245, 1, x_244);
x_198 = x_245;
goto block_225;
}
else
{
lean_object* x_246; 
if (lean_is_scalar(x_228)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_228;
}
lean_ctor_set(x_246, 0, x_235);
lean_ctor_set(x_246, 1, x_237);
x_198 = x_246;
goto block_225;
}
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; 
x_247 = lean_box(0);
x_248 = lean_array_uset(x_227, x_232, x_247);
lean_inc(x_1);
x_249 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_2, x_233);
x_250 = lean_array_uset(x_248, x_232, x_249);
if (lean_is_scalar(x_228)) {
 x_251 = lean_alloc_ctor(0, 2, 0);
} else {
 x_251 = x_228;
}
lean_ctor_set(x_251, 0, x_226);
lean_ctor_set(x_251, 1, x_250);
x_198 = x_251;
goto block_225;
}
block_195:
{
lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
if (lean_is_scalar(x_186)) {
 x_189 = lean_alloc_ctor(0, 2, 0);
} else {
 x_189 = x_186;
}
lean_ctor_set(x_189, 0, x_187);
lean_ctor_set(x_189, 1, x_188);
x_190 = lean_st_ref_set(x_17, x_189, x_185);
x_191 = lean_ctor_get(x_190, 0);
lean_inc(x_191);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_193 = x_190;
} else {
 lean_dec_ref(x_190);
 x_193 = lean_box(0);
}
if (lean_is_scalar(x_193)) {
 x_194 = lean_alloc_ctor(0, 2, 0);
} else {
 x_194 = x_193;
}
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_192);
return x_194;
}
block_225:
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; size_t x_203; size_t x_204; size_t x_205; lean_object* x_206; uint8_t x_207; 
x_199 = lean_ctor_get(x_197, 0);
lean_inc(x_199);
x_200 = lean_ctor_get(x_197, 1);
lean_inc(x_200);
if (lean_is_exclusive(x_197)) {
 lean_ctor_release(x_197, 0);
 lean_ctor_release(x_197, 1);
 x_201 = x_197;
} else {
 lean_dec_ref(x_197);
 x_201 = lean_box(0);
}
x_202 = lean_array_get_size(x_200);
x_203 = lean_usize_of_nat(x_202);
lean_dec(x_202);
x_204 = lean_usize_sub(x_203, x_178);
x_205 = lean_usize_land(x_175, x_204);
x_206 = lean_array_uget(x_200, x_205);
x_207 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_206);
if (x_207 == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; uint8_t x_216; 
x_208 = lean_nat_add(x_199, x_177);
lean_dec(x_199);
x_209 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_209, 0, x_1);
lean_ctor_set(x_209, 1, x_3);
lean_ctor_set(x_209, 2, x_206);
x_210 = lean_array_uset(x_200, x_205, x_209);
x_211 = lean_unsigned_to_nat(2u);
x_212 = lean_nat_shiftl(x_208, x_211);
x_213 = lean_unsigned_to_nat(3u);
x_214 = lean_nat_div(x_212, x_213);
lean_dec(x_212);
x_215 = lean_array_get_size(x_210);
x_216 = lean_nat_dec_le(x_214, x_215);
lean_dec(x_215);
lean_dec(x_214);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; 
x_217 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_210);
if (lean_is_scalar(x_201)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_201;
}
lean_ctor_set(x_218, 0, x_208);
lean_ctor_set(x_218, 1, x_217);
x_187 = x_198;
x_188 = x_218;
goto block_195;
}
else
{
lean_object* x_219; 
if (lean_is_scalar(x_201)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_201;
}
lean_ctor_set(x_219, 0, x_208);
lean_ctor_set(x_219, 1, x_210);
x_187 = x_198;
x_188 = x_219;
goto block_195;
}
}
else
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_220 = lean_box(0);
x_221 = lean_array_uset(x_200, x_205, x_220);
x_222 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_3, x_206);
x_223 = lean_array_uset(x_221, x_205, x_222);
if (lean_is_scalar(x_201)) {
 x_224 = lean_alloc_ctor(0, 2, 0);
} else {
 x_224 = x_201;
}
lean_ctor_set(x_224, 0, x_199);
lean_ctor_set(x_224, 1, x_223);
x_187 = x_198;
x_188 = x_224;
goto block_195;
}
}
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; 
lean_dec(x_3);
lean_dec(x_2);
x_252 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0___boxed), 1, 0);
x_253 = lean_mk_string_unchecked("invalid builtin simproc declaration '", 37, 37);
x_254 = l_Lean_Name_toString(x_1, x_182, x_252);
x_255 = lean_string_append(x_253, x_254);
lean_dec(x_254);
x_256 = lean_mk_string_unchecked("', it has already been declared", 31, 31);
x_257 = lean_string_append(x_255, x_256);
lean_dec(x_256);
x_258 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_258, 0, x_257);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_258);
lean_ctor_set(x_259, 1, x_163);
return x_259;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l_Lean_Meta_Simp_registerBuiltinSimprocCore(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerBuiltinDSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
x_6 = l_Lean_Meta_Simp_registerBuiltinSimprocCore(x_1, x_2, x_5, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_5, x_1, x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
lean_inc(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerSimproc___lam__0), 3, 2);
lean_closure_set(x_6, 0, x_1);
lean_closure_set(x_6, 1, x_2);
x_7 = lean_st_ref_get(x_4, x_5);
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = lean_ctor_get(x_9, 0);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_Environment_getModuleIdxFor_x3f(x_11, x_1);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
lean_inc(x_1);
x_13 = l_Lean_Meta_Simp_isSimproc___redArg(x_1, x_4, x_10);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_unbox(x_14);
lean_dec(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
lean_free_object(x_7);
lean_dec(x_1);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_st_ref_take(x_4, x_16);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_19, 0);
lean_inc(x_21);
x_22 = l_Lean_Meta_Simp_simprocDeclExt;
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get_uint8(x_23, sizeof(void*)*3);
lean_dec(x_23);
x_25 = l_Lean_PersistentEnvExtension_modifyState(lean_box(0), lean_box(0), lean_box(0), x_22, x_21, x_6, x_24);
x_26 = lean_ctor_get(x_19, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_19, 2);
lean_inc(x_27);
x_28 = lean_ctor_get(x_19, 3);
lean_inc(x_28);
x_29 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_30 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_30, 0, x_29);
lean_inc(x_30);
lean_ctor_set(x_17, 1, x_30);
lean_ctor_set(x_17, 0, x_30);
x_31 = lean_ctor_get(x_19, 5);
lean_inc(x_31);
x_32 = lean_ctor_get(x_19, 6);
lean_inc(x_32);
x_33 = lean_ctor_get(x_19, 7);
lean_inc(x_33);
lean_dec(x_19);
x_34 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_34, 0, x_25);
lean_ctor_set(x_34, 1, x_26);
lean_ctor_set(x_34, 2, x_27);
lean_ctor_set(x_34, 3, x_28);
lean_ctor_set(x_34, 4, x_17);
lean_ctor_set(x_34, 5, x_31);
lean_ctor_set(x_34, 6, x_32);
lean_ctor_set(x_34, 7, x_33);
x_35 = lean_st_ref_set(x_4, x_34, x_20);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_35, 0);
lean_dec(x_37);
x_38 = lean_box(0);
lean_ctor_set(x_35, 0, x_38);
return x_35;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
lean_dec(x_35);
x_40 = lean_box(0);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_42 = lean_ctor_get(x_17, 0);
x_43 = lean_ctor_get(x_17, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_17);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = l_Lean_Meta_Simp_simprocDeclExt;
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get_uint8(x_46, sizeof(void*)*3);
lean_dec(x_46);
x_48 = l_Lean_PersistentEnvExtension_modifyState(lean_box(0), lean_box(0), lean_box(0), x_45, x_44, x_6, x_47);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
x_50 = lean_ctor_get(x_42, 2);
lean_inc(x_50);
x_51 = lean_ctor_get(x_42, 3);
lean_inc(x_51);
x_52 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_53 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_53, 0, x_52);
lean_inc(x_53);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_ctor_get(x_42, 5);
lean_inc(x_55);
x_56 = lean_ctor_get(x_42, 6);
lean_inc(x_56);
x_57 = lean_ctor_get(x_42, 7);
lean_inc(x_57);
lean_dec(x_42);
x_58 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_49);
lean_ctor_set(x_58, 2, x_50);
lean_ctor_set(x_58, 3, x_51);
lean_ctor_set(x_58, 4, x_54);
lean_ctor_set(x_58, 5, x_55);
lean_ctor_set(x_58, 6, x_56);
lean_ctor_set(x_58, 7, x_57);
x_59 = lean_st_ref_set(x_4, x_58, x_43);
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
uint8_t x_64; 
lean_dec(x_6);
x_64 = !lean_is_exclusive(x_13);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_13, 1);
x_66 = lean_ctor_get(x_13, 0);
lean_dec(x_66);
x_67 = lean_mk_string_unchecked("invalid simproc declaration '", 29, 29);
x_68 = l_Lean_stringToMessageData(x_67);
lean_dec(x_67);
x_69 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_13, 7);
lean_ctor_set(x_13, 1, x_69);
lean_ctor_set(x_13, 0, x_68);
x_70 = lean_mk_string_unchecked("', it has already been declared", 31, 31);
x_71 = l_Lean_stringToMessageData(x_70);
lean_dec(x_70);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_71);
lean_ctor_set(x_7, 0, x_13);
x_72 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_7, x_3, x_4, x_65);
return x_72;
}
else
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_73 = lean_ctor_get(x_13, 1);
lean_inc(x_73);
lean_dec(x_13);
x_74 = lean_mk_string_unchecked("invalid simproc declaration '", 29, 29);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = l_Lean_MessageData_ofName(x_1);
x_77 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_mk_string_unchecked("', it has already been declared", 31, 31);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_79);
lean_ctor_set(x_7, 0, x_77);
x_80 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_7, x_3, x_4, x_73);
return x_80;
}
}
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_12);
lean_dec(x_6);
x_81 = lean_mk_string_unchecked("invalid simproc declaration '", 29, 29);
x_82 = l_Lean_stringToMessageData(x_81);
lean_dec(x_81);
x_83 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_7, 7);
lean_ctor_set(x_7, 1, x_83);
lean_ctor_set(x_7, 0, x_82);
x_84 = lean_mk_string_unchecked("', function declaration is in an imported module", 48, 48);
x_85 = l_Lean_stringToMessageData(x_84);
lean_dec(x_84);
x_86 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_86, 0, x_7);
lean_ctor_set(x_86, 1, x_85);
x_87 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_86, x_3, x_4, x_10);
return x_87;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_88 = lean_ctor_get(x_7, 0);
x_89 = lean_ctor_get(x_7, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_7);
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = l_Lean_Environment_getModuleIdxFor_x3f(x_90, x_1);
lean_dec(x_90);
if (lean_obj_tag(x_91) == 0)
{
lean_object* x_92; lean_object* x_93; uint8_t x_94; 
lean_inc(x_1);
x_92 = l_Lean_Meta_Simp_isSimproc___redArg(x_1, x_4, x_89);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
x_94 = lean_unbox(x_93);
lean_dec(x_93);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; uint8_t x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_1);
x_95 = lean_ctor_get(x_92, 1);
lean_inc(x_95);
lean_dec(x_92);
x_96 = lean_st_ref_take(x_4, x_95);
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_99 = x_96;
} else {
 lean_dec_ref(x_96);
 x_99 = lean_box(0);
}
x_100 = lean_ctor_get(x_97, 0);
lean_inc(x_100);
x_101 = l_Lean_Meta_Simp_simprocDeclExt;
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get_uint8(x_102, sizeof(void*)*3);
lean_dec(x_102);
x_104 = l_Lean_PersistentEnvExtension_modifyState(lean_box(0), lean_box(0), lean_box(0), x_101, x_100, x_6, x_103);
x_105 = lean_ctor_get(x_97, 1);
lean_inc(x_105);
x_106 = lean_ctor_get(x_97, 2);
lean_inc(x_106);
x_107 = lean_ctor_get(x_97, 3);
lean_inc(x_107);
x_108 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_109, 0, x_108);
lean_inc(x_109);
if (lean_is_scalar(x_99)) {
 x_110 = lean_alloc_ctor(0, 2, 0);
} else {
 x_110 = x_99;
}
lean_ctor_set(x_110, 0, x_109);
lean_ctor_set(x_110, 1, x_109);
x_111 = lean_ctor_get(x_97, 5);
lean_inc(x_111);
x_112 = lean_ctor_get(x_97, 6);
lean_inc(x_112);
x_113 = lean_ctor_get(x_97, 7);
lean_inc(x_113);
lean_dec(x_97);
x_114 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_105);
lean_ctor_set(x_114, 2, x_106);
lean_ctor_set(x_114, 3, x_107);
lean_ctor_set(x_114, 4, x_110);
lean_ctor_set(x_114, 5, x_111);
lean_ctor_set(x_114, 6, x_112);
lean_ctor_set(x_114, 7, x_113);
x_115 = lean_st_ref_set(x_4, x_114, x_98);
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
lean_dec(x_6);
x_120 = lean_ctor_get(x_92, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_92)) {
 lean_ctor_release(x_92, 0);
 lean_ctor_release(x_92, 1);
 x_121 = x_92;
} else {
 lean_dec_ref(x_92);
 x_121 = lean_box(0);
}
x_122 = lean_mk_string_unchecked("invalid simproc declaration '", 29, 29);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
x_124 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_121)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_121;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked("', it has already been declared", 31, 31);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
x_129 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_128, x_3, x_4, x_120);
return x_129;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; 
lean_dec(x_91);
lean_dec(x_6);
x_130 = lean_mk_string_unchecked("invalid simproc declaration '", 29, 29);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = l_Lean_MessageData_ofName(x_1);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("', function declaration is in an imported module", 48, 48);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_136, x_3, x_4, x_89);
return x_137;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimproc___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_registerSimproc(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_3, 0);
x_5 = lean_ctor_get(x_2, 0);
x_6 = lean_ctor_get(x_5, 0);
x_7 = lean_name_eq(x_4, x_6);
return x_7;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instBEqSimprocEntry() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_instBEqSimprocEntry___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_instToFormatSimprocEntry___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
lean_dec(x_3);
x_5 = lean_box(1);
x_6 = lean_unbox(x_5);
x_7 = l_Lean_Name_toString(x_4, x_6, x_1);
x_8 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
static lean_object* _init_l_Lean_Meta_Simp_instToFormatSimprocEntry() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_registerBuiltinSimprocCore___lam__0___boxed), 1, 0);
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_instToFormatSimprocEntry___lam__1), 2, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_erase(lean_object* x_1, lean_object* x_2) {
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
x_6 = l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0(lean_box(0), x_5, x_2);
x_7 = lean_ctor_get(x_1, 3);
lean_inc(x_7);
lean_dec(x_1);
x_8 = lean_box(0);
x_9 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_7, x_2, x_8);
x_10 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_10, 0, x_3);
lean_ctor_set(x_10, 1, x_4);
lean_ctor_set(x_10, 2, x_6);
lean_ctor_set(x_10, 3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1143_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_3 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
x_5 = lean_st_mk_ref(x_4, x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1178_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_2 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_3 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
lean_inc(x_3);
lean_inc(x_2);
x_4 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_2);
lean_ctor_set(x_4, 2, x_3);
lean_ctor_set(x_4, 3, x_3);
x_5 = lean_st_mk_ref(x_4, x_1);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_5, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_7);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_mk_string_unchecked("unexpected type at simproc", 26, 26);
x_5 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_5, 0, x_4);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_unbox(x_5);
lean_inc(x_1);
lean_inc(x_4);
x_7 = l_Lean_Environment_find_x3f(x_4, x_1, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_4);
lean_dec(x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__0___boxed), 1, 0);
x_9 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_10 = lean_box(1);
x_11 = lean_unbox(x_10);
x_12 = l_Lean_Name_toString(x_1, x_11, x_8);
x_13 = lean_string_append(x_9, x_12);
lean_dec(x_12);
x_14 = lean_mk_string_unchecked("'", 1, 1);
x_15 = lean_string_append(x_13, x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_3);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_7);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_7, 0);
x_20 = l_Lean_ConstantInfo_type(x_19);
lean_dec(x_19);
switch (lean_obj_tag(x_20)) {
case 0:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = l_Lean_Expr_bvar___override(x_21);
x_23 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_22, x_2, x_3);
lean_dec(x_2);
lean_dec(x_22);
return x_23;
}
case 1:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_24 = lean_ctor_get(x_20, 0);
lean_inc(x_24);
lean_dec(x_20);
x_25 = l_Lean_Expr_fvar___override(x_24);
x_26 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_25, x_2, x_3);
lean_dec(x_2);
lean_dec(x_25);
return x_26;
}
case 2:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_27 = lean_ctor_get(x_20, 0);
lean_inc(x_27);
lean_dec(x_20);
x_28 = l_Lean_Expr_mvar___override(x_27);
x_29 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_28, x_2, x_3);
lean_dec(x_2);
lean_dec(x_28);
return x_29;
}
case 3:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_30 = lean_ctor_get(x_20, 0);
lean_inc(x_30);
lean_dec(x_20);
x_31 = l_Lean_Expr_sort___override(x_30);
x_32 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_31, x_2, x_3);
lean_dec(x_2);
lean_dec(x_31);
return x_32;
}
case 4:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_20, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_20, 1);
lean_inc(x_34);
lean_dec(x_20);
x_35 = lean_box(0);
switch (lean_obj_tag(x_33)) {
case 0:
{
lean_object* x_36; lean_object* x_37; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_36 = l_Lean_Expr_const___override(x_35, x_34);
x_37 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_36, x_2, x_3);
lean_dec(x_2);
lean_dec(x_36);
return x_37;
}
case 1:
{
lean_object* x_38; 
x_38 = lean_ctor_get(x_33, 0);
lean_inc(x_38);
switch (lean_obj_tag(x_38)) {
case 0:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
lean_dec(x_33);
x_40 = l_Lean_Name_str___override(x_35, x_39);
x_41 = l_Lean_Expr_const___override(x_40, x_34);
x_42 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_41, x_2, x_3);
lean_dec(x_2);
lean_dec(x_41);
return x_42;
}
case 1:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_33, 1);
lean_inc(x_43);
lean_dec(x_33);
x_44 = lean_ctor_get(x_38, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_38, 1);
lean_inc(x_45);
lean_dec(x_38);
lean_inc(x_45);
x_46 = l_Lean_Name_str___override(x_35, x_45);
switch (lean_obj_tag(x_44)) {
case 0:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_45);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_47 = l_Lean_Name_str___override(x_46, x_43);
x_48 = l_Lean_Expr_const___override(x_47, x_34);
x_49 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_48, x_2, x_3);
lean_dec(x_2);
lean_dec(x_48);
return x_49;
}
case 1:
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_46);
x_50 = lean_ctor_get(x_44, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_44, 1);
lean_inc(x_51);
lean_dec(x_44);
lean_inc(x_51);
x_52 = l_Lean_Name_str___override(x_35, x_51);
lean_inc(x_45);
x_53 = l_Lean_Name_str___override(x_52, x_45);
switch (lean_obj_tag(x_50)) {
case 0:
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_51);
lean_dec(x_45);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_54 = l_Lean_Name_str___override(x_53, x_43);
x_55 = l_Lean_Expr_const___override(x_54, x_34);
x_56 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_55, x_2, x_3);
lean_dec(x_2);
lean_dec(x_55);
return x_56;
}
case 1:
{
lean_object* x_57; 
lean_dec(x_53);
x_57 = lean_ctor_get(x_50, 0);
lean_inc(x_57);
switch (lean_obj_tag(x_57)) {
case 0:
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = lean_ctor_get(x_50, 1);
lean_inc(x_58);
lean_dec(x_50);
x_59 = lean_mk_string_unchecked("Lean", 4, 4);
x_60 = lean_string_dec_eq(x_58, x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_59);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_61 = l_Lean_Name_str___override(x_35, x_58);
x_62 = l_Lean_Name_str___override(x_61, x_51);
x_63 = l_Lean_Name_str___override(x_62, x_45);
x_64 = l_Lean_Name_str___override(x_63, x_43);
x_65 = l_Lean_Expr_const___override(x_64, x_34);
x_66 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_65, x_2, x_3);
lean_dec(x_2);
lean_dec(x_65);
return x_66;
}
else
{
lean_object* x_67; uint8_t x_68; 
lean_dec(x_58);
x_67 = lean_mk_string_unchecked("Meta", 4, 4);
x_68 = lean_string_dec_eq(x_51, x_67);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
lean_dec(x_67);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_69 = l_Lean_Name_str___override(x_35, x_59);
x_70 = l_Lean_Name_str___override(x_69, x_51);
x_71 = l_Lean_Name_str___override(x_70, x_45);
x_72 = l_Lean_Name_str___override(x_71, x_43);
x_73 = l_Lean_Expr_const___override(x_72, x_34);
x_74 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_73, x_2, x_3);
lean_dec(x_2);
lean_dec(x_73);
return x_74;
}
else
{
lean_object* x_75; uint8_t x_76; 
lean_dec(x_51);
x_75 = lean_mk_string_unchecked("Simp", 4, 4);
x_76 = lean_string_dec_eq(x_45, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_75);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_77 = l_Lean_Name_str___override(x_35, x_59);
x_78 = l_Lean_Name_str___override(x_77, x_67);
x_79 = l_Lean_Name_str___override(x_78, x_45);
x_80 = l_Lean_Name_str___override(x_79, x_43);
x_81 = l_Lean_Expr_const___override(x_80, x_34);
x_82 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_81, x_2, x_3);
lean_dec(x_2);
lean_dec(x_81);
return x_82;
}
else
{
lean_object* x_83; uint8_t x_84; 
lean_dec(x_45);
x_83 = lean_mk_string_unchecked("Simproc", 7, 7);
x_84 = lean_string_dec_eq(x_43, x_83);
lean_dec(x_83);
if (x_84 == 0)
{
lean_object* x_85; uint8_t x_86; 
x_85 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_86 = lean_string_dec_eq(x_43, x_85);
lean_dec(x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_87 = l_Lean_Name_str___override(x_35, x_59);
x_88 = l_Lean_Name_str___override(x_87, x_67);
x_89 = l_Lean_Name_str___override(x_88, x_75);
x_90 = l_Lean_Name_str___override(x_89, x_43);
x_91 = l_Lean_Expr_const___override(x_90, x_34);
x_92 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_91, x_2, x_3);
lean_dec(x_2);
lean_dec(x_91);
return x_92;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_dec(x_75);
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_43);
lean_dec(x_34);
x_93 = lean_ctor_get(x_2, 1);
lean_inc(x_93);
lean_dec(x_2);
x_94 = lean_eval_const(x_4, x_93, x_1);
lean_dec(x_1);
lean_dec(x_93);
lean_dec(x_4);
x_95 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_94, x_3);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; 
x_97 = lean_ctor_get(x_95, 0);
lean_ctor_set(x_7, 0, x_97);
lean_ctor_set(x_95, 0, x_7);
return x_95;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_95, 0);
x_99 = lean_ctor_get(x_95, 1);
lean_inc(x_99);
lean_inc(x_98);
lean_dec(x_95);
lean_ctor_set(x_7, 0, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_7);
lean_ctor_set(x_100, 1, x_99);
return x_100;
}
}
else
{
uint8_t x_101; 
lean_free_object(x_7);
x_101 = !lean_is_exclusive(x_95);
if (x_101 == 0)
{
return x_95;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_95, 0);
x_103 = lean_ctor_get(x_95, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_95);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_75);
lean_dec(x_67);
lean_dec(x_59);
lean_dec(x_43);
lean_dec(x_34);
x_105 = lean_ctor_get(x_2, 1);
lean_inc(x_105);
lean_dec(x_2);
x_106 = lean_eval_const(x_4, x_105, x_1);
lean_dec(x_1);
lean_dec(x_105);
lean_dec(x_4);
x_107 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_106, x_3);
if (lean_obj_tag(x_107) == 0)
{
uint8_t x_108; 
x_108 = !lean_is_exclusive(x_107);
if (x_108 == 0)
{
lean_object* x_109; 
x_109 = lean_ctor_get(x_107, 0);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_109);
lean_ctor_set(x_107, 0, x_7);
return x_107;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_110 = lean_ctor_get(x_107, 0);
x_111 = lean_ctor_get(x_107, 1);
lean_inc(x_111);
lean_inc(x_110);
lean_dec(x_107);
lean_ctor_set_tag(x_7, 0);
lean_ctor_set(x_7, 0, x_110);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_7);
lean_ctor_set(x_112, 1, x_111);
return x_112;
}
}
else
{
uint8_t x_113; 
lean_free_object(x_7);
x_113 = !lean_is_exclusive(x_107);
if (x_113 == 0)
{
return x_107;
}
else
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_107, 0);
x_115 = lean_ctor_get(x_107, 1);
lean_inc(x_115);
lean_inc(x_114);
lean_dec(x_107);
x_116 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
return x_116;
}
}
}
}
}
}
}
case 1:
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_117 = lean_ctor_get(x_50, 1);
lean_inc(x_117);
lean_dec(x_50);
x_118 = lean_ctor_get(x_57, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_57, 1);
lean_inc(x_119);
lean_dec(x_57);
x_120 = l_Lean_Name_str___override(x_118, x_119);
x_121 = l_Lean_Name_str___override(x_120, x_117);
x_122 = l_Lean_Name_str___override(x_121, x_51);
x_123 = l_Lean_Name_str___override(x_122, x_45);
x_124 = l_Lean_Name_str___override(x_123, x_43);
x_125 = l_Lean_Expr_const___override(x_124, x_34);
x_126 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_125, x_2, x_3);
lean_dec(x_2);
lean_dec(x_125);
return x_126;
}
default: 
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_127 = lean_ctor_get(x_50, 1);
lean_inc(x_127);
lean_dec(x_50);
x_128 = lean_ctor_get(x_57, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_57, 1);
lean_inc(x_129);
lean_dec(x_57);
x_130 = l_Lean_Name_num___override(x_128, x_129);
x_131 = l_Lean_Name_str___override(x_130, x_127);
x_132 = l_Lean_Name_str___override(x_131, x_51);
x_133 = l_Lean_Name_str___override(x_132, x_45);
x_134 = l_Lean_Name_str___override(x_133, x_43);
x_135 = l_Lean_Expr_const___override(x_134, x_34);
x_136 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_135, x_2, x_3);
lean_dec(x_2);
lean_dec(x_135);
return x_136;
}
}
}
default: 
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; 
lean_dec(x_53);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_137 = lean_ctor_get(x_50, 0);
lean_inc(x_137);
x_138 = lean_ctor_get(x_50, 1);
lean_inc(x_138);
lean_dec(x_50);
x_139 = l_Lean_Name_num___override(x_137, x_138);
x_140 = l_Lean_Name_str___override(x_139, x_51);
x_141 = l_Lean_Name_str___override(x_140, x_45);
x_142 = l_Lean_Name_str___override(x_141, x_43);
x_143 = l_Lean_Expr_const___override(x_142, x_34);
x_144 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_143, x_2, x_3);
lean_dec(x_2);
lean_dec(x_143);
return x_144;
}
}
}
default: 
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; 
lean_dec(x_46);
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_145 = lean_ctor_get(x_44, 0);
lean_inc(x_145);
x_146 = lean_ctor_get(x_44, 1);
lean_inc(x_146);
lean_dec(x_44);
x_147 = l_Lean_Name_num___override(x_145, x_146);
x_148 = l_Lean_Name_str___override(x_147, x_45);
x_149 = l_Lean_Name_str___override(x_148, x_43);
x_150 = l_Lean_Expr_const___override(x_149, x_34);
x_151 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_150, x_2, x_3);
lean_dec(x_2);
lean_dec(x_150);
return x_151;
}
}
}
default: 
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_152 = lean_ctor_get(x_33, 1);
lean_inc(x_152);
lean_dec(x_33);
x_153 = lean_ctor_get(x_38, 0);
lean_inc(x_153);
x_154 = lean_ctor_get(x_38, 1);
lean_inc(x_154);
lean_dec(x_38);
x_155 = l_Lean_Name_num___override(x_153, x_154);
x_156 = l_Lean_Name_str___override(x_155, x_152);
x_157 = l_Lean_Expr_const___override(x_156, x_34);
x_158 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_157, x_2, x_3);
lean_dec(x_2);
lean_dec(x_157);
return x_158;
}
}
}
default: 
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_159 = lean_ctor_get(x_33, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_33, 1);
lean_inc(x_160);
lean_dec(x_33);
x_161 = l_Lean_Name_num___override(x_159, x_160);
x_162 = l_Lean_Expr_const___override(x_161, x_34);
x_163 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_162, x_2, x_3);
lean_dec(x_2);
lean_dec(x_162);
return x_163;
}
}
}
case 5:
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_164 = lean_ctor_get(x_20, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_20, 1);
lean_inc(x_165);
lean_dec(x_20);
x_166 = l_Lean_Expr_app___override(x_164, x_165);
x_167 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_166, x_2, x_3);
lean_dec(x_2);
lean_dec(x_166);
return x_167;
}
case 6:
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; lean_object* x_172; lean_object* x_173; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_168 = lean_ctor_get(x_20, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_20, 1);
lean_inc(x_169);
x_170 = lean_ctor_get(x_20, 2);
lean_inc(x_170);
x_171 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_172 = l_Lean_Expr_lam___override(x_168, x_169, x_170, x_171);
x_173 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_172, x_2, x_3);
lean_dec(x_2);
lean_dec(x_172);
return x_173;
}
case 7:
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; uint8_t x_177; lean_object* x_178; lean_object* x_179; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_174 = lean_ctor_get(x_20, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_20, 1);
lean_inc(x_175);
x_176 = lean_ctor_get(x_20, 2);
lean_inc(x_176);
x_177 = lean_ctor_get_uint8(x_20, sizeof(void*)*3 + 8);
lean_dec(x_20);
x_178 = l_Lean_Expr_forallE___override(x_174, x_175, x_176, x_177);
x_179 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_178, x_2, x_3);
lean_dec(x_2);
lean_dec(x_178);
return x_179;
}
case 8:
{
lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; uint8_t x_184; lean_object* x_185; lean_object* x_186; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_180 = lean_ctor_get(x_20, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_20, 1);
lean_inc(x_181);
x_182 = lean_ctor_get(x_20, 2);
lean_inc(x_182);
x_183 = lean_ctor_get(x_20, 3);
lean_inc(x_183);
x_184 = lean_ctor_get_uint8(x_20, sizeof(void*)*4 + 8);
lean_dec(x_20);
x_185 = l_Lean_Expr_letE___override(x_180, x_181, x_182, x_183, x_184);
x_186 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_185, x_2, x_3);
lean_dec(x_2);
lean_dec(x_185);
return x_186;
}
case 9:
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_187 = lean_ctor_get(x_20, 0);
lean_inc(x_187);
lean_dec(x_20);
x_188 = l_Lean_Expr_lit___override(x_187);
x_189 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_188, x_2, x_3);
lean_dec(x_2);
lean_dec(x_188);
return x_189;
}
case 10:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_190 = lean_ctor_get(x_20, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_20, 1);
lean_inc(x_191);
lean_dec(x_20);
x_192 = l_Lean_Expr_mdata___override(x_190, x_191);
x_193 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_192, x_2, x_3);
lean_dec(x_2);
lean_dec(x_192);
return x_193;
}
default: 
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; 
lean_free_object(x_7);
lean_dec(x_4);
lean_dec(x_1);
x_194 = lean_ctor_get(x_20, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_20, 1);
lean_inc(x_195);
x_196 = lean_ctor_get(x_20, 2);
lean_inc(x_196);
lean_dec(x_20);
x_197 = l_Lean_Expr_proj___override(x_194, x_195, x_196);
x_198 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_197, x_2, x_3);
lean_dec(x_2);
lean_dec(x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; 
x_199 = lean_ctor_get(x_7, 0);
lean_inc(x_199);
lean_dec(x_7);
x_200 = l_Lean_ConstantInfo_type(x_199);
lean_dec(x_199);
switch (lean_obj_tag(x_200)) {
case 0:
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_dec(x_4);
lean_dec(x_1);
x_201 = lean_ctor_get(x_200, 0);
lean_inc(x_201);
lean_dec(x_200);
x_202 = l_Lean_Expr_bvar___override(x_201);
x_203 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_202, x_2, x_3);
lean_dec(x_2);
lean_dec(x_202);
return x_203;
}
case 1:
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_4);
lean_dec(x_1);
x_204 = lean_ctor_get(x_200, 0);
lean_inc(x_204);
lean_dec(x_200);
x_205 = l_Lean_Expr_fvar___override(x_204);
x_206 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_205, x_2, x_3);
lean_dec(x_2);
lean_dec(x_205);
return x_206;
}
case 2:
{
lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_4);
lean_dec(x_1);
x_207 = lean_ctor_get(x_200, 0);
lean_inc(x_207);
lean_dec(x_200);
x_208 = l_Lean_Expr_mvar___override(x_207);
x_209 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_208, x_2, x_3);
lean_dec(x_2);
lean_dec(x_208);
return x_209;
}
case 3:
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_4);
lean_dec(x_1);
x_210 = lean_ctor_get(x_200, 0);
lean_inc(x_210);
lean_dec(x_200);
x_211 = l_Lean_Expr_sort___override(x_210);
x_212 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_211, x_2, x_3);
lean_dec(x_2);
lean_dec(x_211);
return x_212;
}
case 4:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_200, 0);
lean_inc(x_213);
x_214 = lean_ctor_get(x_200, 1);
lean_inc(x_214);
lean_dec(x_200);
x_215 = lean_box(0);
switch (lean_obj_tag(x_213)) {
case 0:
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_4);
lean_dec(x_1);
x_216 = l_Lean_Expr_const___override(x_215, x_214);
x_217 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_216, x_2, x_3);
lean_dec(x_2);
lean_dec(x_216);
return x_217;
}
case 1:
{
lean_object* x_218; 
x_218 = lean_ctor_get(x_213, 0);
lean_inc(x_218);
switch (lean_obj_tag(x_218)) {
case 0:
{
lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; 
lean_dec(x_4);
lean_dec(x_1);
x_219 = lean_ctor_get(x_213, 1);
lean_inc(x_219);
lean_dec(x_213);
x_220 = l_Lean_Name_str___override(x_215, x_219);
x_221 = l_Lean_Expr_const___override(x_220, x_214);
x_222 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_221, x_2, x_3);
lean_dec(x_2);
lean_dec(x_221);
return x_222;
}
case 1:
{
lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; 
x_223 = lean_ctor_get(x_213, 1);
lean_inc(x_223);
lean_dec(x_213);
x_224 = lean_ctor_get(x_218, 0);
lean_inc(x_224);
x_225 = lean_ctor_get(x_218, 1);
lean_inc(x_225);
lean_dec(x_218);
lean_inc(x_225);
x_226 = l_Lean_Name_str___override(x_215, x_225);
switch (lean_obj_tag(x_224)) {
case 0:
{
lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_225);
lean_dec(x_4);
lean_dec(x_1);
x_227 = l_Lean_Name_str___override(x_226, x_223);
x_228 = l_Lean_Expr_const___override(x_227, x_214);
x_229 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_228, x_2, x_3);
lean_dec(x_2);
lean_dec(x_228);
return x_229;
}
case 1:
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_226);
x_230 = lean_ctor_get(x_224, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_224, 1);
lean_inc(x_231);
lean_dec(x_224);
lean_inc(x_231);
x_232 = l_Lean_Name_str___override(x_215, x_231);
lean_inc(x_225);
x_233 = l_Lean_Name_str___override(x_232, x_225);
switch (lean_obj_tag(x_230)) {
case 0:
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; 
lean_dec(x_231);
lean_dec(x_225);
lean_dec(x_4);
lean_dec(x_1);
x_234 = l_Lean_Name_str___override(x_233, x_223);
x_235 = l_Lean_Expr_const___override(x_234, x_214);
x_236 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_235, x_2, x_3);
lean_dec(x_2);
lean_dec(x_235);
return x_236;
}
case 1:
{
lean_object* x_237; 
lean_dec(x_233);
x_237 = lean_ctor_get(x_230, 0);
lean_inc(x_237);
switch (lean_obj_tag(x_237)) {
case 0:
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_230, 1);
lean_inc(x_238);
lean_dec(x_230);
x_239 = lean_mk_string_unchecked("Lean", 4, 4);
x_240 = lean_string_dec_eq(x_238, x_239);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_dec(x_239);
lean_dec(x_4);
lean_dec(x_1);
x_241 = l_Lean_Name_str___override(x_215, x_238);
x_242 = l_Lean_Name_str___override(x_241, x_231);
x_243 = l_Lean_Name_str___override(x_242, x_225);
x_244 = l_Lean_Name_str___override(x_243, x_223);
x_245 = l_Lean_Expr_const___override(x_244, x_214);
x_246 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_245, x_2, x_3);
lean_dec(x_2);
lean_dec(x_245);
return x_246;
}
else
{
lean_object* x_247; uint8_t x_248; 
lean_dec(x_238);
x_247 = lean_mk_string_unchecked("Meta", 4, 4);
x_248 = lean_string_dec_eq(x_231, x_247);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; 
lean_dec(x_247);
lean_dec(x_4);
lean_dec(x_1);
x_249 = l_Lean_Name_str___override(x_215, x_239);
x_250 = l_Lean_Name_str___override(x_249, x_231);
x_251 = l_Lean_Name_str___override(x_250, x_225);
x_252 = l_Lean_Name_str___override(x_251, x_223);
x_253 = l_Lean_Expr_const___override(x_252, x_214);
x_254 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_253, x_2, x_3);
lean_dec(x_2);
lean_dec(x_253);
return x_254;
}
else
{
lean_object* x_255; uint8_t x_256; 
lean_dec(x_231);
x_255 = lean_mk_string_unchecked("Simp", 4, 4);
x_256 = lean_string_dec_eq(x_225, x_255);
if (x_256 == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_255);
lean_dec(x_4);
lean_dec(x_1);
x_257 = l_Lean_Name_str___override(x_215, x_239);
x_258 = l_Lean_Name_str___override(x_257, x_247);
x_259 = l_Lean_Name_str___override(x_258, x_225);
x_260 = l_Lean_Name_str___override(x_259, x_223);
x_261 = l_Lean_Expr_const___override(x_260, x_214);
x_262 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_261, x_2, x_3);
lean_dec(x_2);
lean_dec(x_261);
return x_262;
}
else
{
lean_object* x_263; uint8_t x_264; 
lean_dec(x_225);
x_263 = lean_mk_string_unchecked("Simproc", 7, 7);
x_264 = lean_string_dec_eq(x_223, x_263);
lean_dec(x_263);
if (x_264 == 0)
{
lean_object* x_265; uint8_t x_266; 
x_265 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_266 = lean_string_dec_eq(x_223, x_265);
lean_dec(x_265);
if (x_266 == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; 
lean_dec(x_4);
lean_dec(x_1);
x_267 = l_Lean_Name_str___override(x_215, x_239);
x_268 = l_Lean_Name_str___override(x_267, x_247);
x_269 = l_Lean_Name_str___override(x_268, x_255);
x_270 = l_Lean_Name_str___override(x_269, x_223);
x_271 = l_Lean_Expr_const___override(x_270, x_214);
x_272 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_271, x_2, x_3);
lean_dec(x_2);
lean_dec(x_271);
return x_272;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_dec(x_255);
lean_dec(x_247);
lean_dec(x_239);
lean_dec(x_223);
lean_dec(x_214);
x_273 = lean_ctor_get(x_2, 1);
lean_inc(x_273);
lean_dec(x_2);
x_274 = lean_eval_const(x_4, x_273, x_1);
lean_dec(x_1);
lean_dec(x_273);
lean_dec(x_4);
x_275 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_274, x_3);
if (lean_obj_tag(x_275) == 0)
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; 
x_276 = lean_ctor_get(x_275, 0);
lean_inc(x_276);
x_277 = lean_ctor_get(x_275, 1);
lean_inc(x_277);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_278 = x_275;
} else {
 lean_dec_ref(x_275);
 x_278 = lean_box(0);
}
x_279 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_279, 0, x_276);
if (lean_is_scalar(x_278)) {
 x_280 = lean_alloc_ctor(0, 2, 0);
} else {
 x_280 = x_278;
}
lean_ctor_set(x_280, 0, x_279);
lean_ctor_set(x_280, 1, x_277);
return x_280;
}
else
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; 
x_281 = lean_ctor_get(x_275, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_275, 1);
lean_inc(x_282);
if (lean_is_exclusive(x_275)) {
 lean_ctor_release(x_275, 0);
 lean_ctor_release(x_275, 1);
 x_283 = x_275;
} else {
 lean_dec_ref(x_275);
 x_283 = lean_box(0);
}
if (lean_is_scalar(x_283)) {
 x_284 = lean_alloc_ctor(1, 2, 0);
} else {
 x_284 = x_283;
}
lean_ctor_set(x_284, 0, x_281);
lean_ctor_set(x_284, 1, x_282);
return x_284;
}
}
}
else
{
lean_object* x_285; lean_object* x_286; lean_object* x_287; 
lean_dec(x_255);
lean_dec(x_247);
lean_dec(x_239);
lean_dec(x_223);
lean_dec(x_214);
x_285 = lean_ctor_get(x_2, 1);
lean_inc(x_285);
lean_dec(x_2);
x_286 = lean_eval_const(x_4, x_285, x_1);
lean_dec(x_1);
lean_dec(x_285);
lean_dec(x_4);
x_287 = l_IO_ofExcept___at___IO_FS_Stream_readJson_spec__0(lean_box(0), x_286, x_3);
if (lean_obj_tag(x_287) == 0)
{
lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; 
x_288 = lean_ctor_get(x_287, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_287, 1);
lean_inc(x_289);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_290 = x_287;
} else {
 lean_dec_ref(x_287);
 x_290 = lean_box(0);
}
x_291 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_291, 0, x_288);
if (lean_is_scalar(x_290)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_290;
}
lean_ctor_set(x_292, 0, x_291);
lean_ctor_set(x_292, 1, x_289);
return x_292;
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_293 = lean_ctor_get(x_287, 0);
lean_inc(x_293);
x_294 = lean_ctor_get(x_287, 1);
lean_inc(x_294);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_295 = x_287;
} else {
 lean_dec_ref(x_287);
 x_295 = lean_box(0);
}
if (lean_is_scalar(x_295)) {
 x_296 = lean_alloc_ctor(1, 2, 0);
} else {
 x_296 = x_295;
}
lean_ctor_set(x_296, 0, x_293);
lean_ctor_set(x_296, 1, x_294);
return x_296;
}
}
}
}
}
}
case 1:
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; 
lean_dec(x_4);
lean_dec(x_1);
x_297 = lean_ctor_get(x_230, 1);
lean_inc(x_297);
lean_dec(x_230);
x_298 = lean_ctor_get(x_237, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_237, 1);
lean_inc(x_299);
lean_dec(x_237);
x_300 = l_Lean_Name_str___override(x_298, x_299);
x_301 = l_Lean_Name_str___override(x_300, x_297);
x_302 = l_Lean_Name_str___override(x_301, x_231);
x_303 = l_Lean_Name_str___override(x_302, x_225);
x_304 = l_Lean_Name_str___override(x_303, x_223);
x_305 = l_Lean_Expr_const___override(x_304, x_214);
x_306 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_305, x_2, x_3);
lean_dec(x_2);
lean_dec(x_305);
return x_306;
}
default: 
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; 
lean_dec(x_4);
lean_dec(x_1);
x_307 = lean_ctor_get(x_230, 1);
lean_inc(x_307);
lean_dec(x_230);
x_308 = lean_ctor_get(x_237, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_237, 1);
lean_inc(x_309);
lean_dec(x_237);
x_310 = l_Lean_Name_num___override(x_308, x_309);
x_311 = l_Lean_Name_str___override(x_310, x_307);
x_312 = l_Lean_Name_str___override(x_311, x_231);
x_313 = l_Lean_Name_str___override(x_312, x_225);
x_314 = l_Lean_Name_str___override(x_313, x_223);
x_315 = l_Lean_Expr_const___override(x_314, x_214);
x_316 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_315, x_2, x_3);
lean_dec(x_2);
lean_dec(x_315);
return x_316;
}
}
}
default: 
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
lean_dec(x_233);
lean_dec(x_4);
lean_dec(x_1);
x_317 = lean_ctor_get(x_230, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_230, 1);
lean_inc(x_318);
lean_dec(x_230);
x_319 = l_Lean_Name_num___override(x_317, x_318);
x_320 = l_Lean_Name_str___override(x_319, x_231);
x_321 = l_Lean_Name_str___override(x_320, x_225);
x_322 = l_Lean_Name_str___override(x_321, x_223);
x_323 = l_Lean_Expr_const___override(x_322, x_214);
x_324 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_323, x_2, x_3);
lean_dec(x_2);
lean_dec(x_323);
return x_324;
}
}
}
default: 
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_226);
lean_dec(x_4);
lean_dec(x_1);
x_325 = lean_ctor_get(x_224, 0);
lean_inc(x_325);
x_326 = lean_ctor_get(x_224, 1);
lean_inc(x_326);
lean_dec(x_224);
x_327 = l_Lean_Name_num___override(x_325, x_326);
x_328 = l_Lean_Name_str___override(x_327, x_225);
x_329 = l_Lean_Name_str___override(x_328, x_223);
x_330 = l_Lean_Expr_const___override(x_329, x_214);
x_331 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_330, x_2, x_3);
lean_dec(x_2);
lean_dec(x_330);
return x_331;
}
}
}
default: 
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; 
lean_dec(x_4);
lean_dec(x_1);
x_332 = lean_ctor_get(x_213, 1);
lean_inc(x_332);
lean_dec(x_213);
x_333 = lean_ctor_get(x_218, 0);
lean_inc(x_333);
x_334 = lean_ctor_get(x_218, 1);
lean_inc(x_334);
lean_dec(x_218);
x_335 = l_Lean_Name_num___override(x_333, x_334);
x_336 = l_Lean_Name_str___override(x_335, x_332);
x_337 = l_Lean_Expr_const___override(x_336, x_214);
x_338 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_337, x_2, x_3);
lean_dec(x_2);
lean_dec(x_337);
return x_338;
}
}
}
default: 
{
lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; 
lean_dec(x_4);
lean_dec(x_1);
x_339 = lean_ctor_get(x_213, 0);
lean_inc(x_339);
x_340 = lean_ctor_get(x_213, 1);
lean_inc(x_340);
lean_dec(x_213);
x_341 = l_Lean_Name_num___override(x_339, x_340);
x_342 = l_Lean_Expr_const___override(x_341, x_214);
x_343 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_342, x_2, x_3);
lean_dec(x_2);
lean_dec(x_342);
return x_343;
}
}
}
case 5:
{
lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; 
lean_dec(x_4);
lean_dec(x_1);
x_344 = lean_ctor_get(x_200, 0);
lean_inc(x_344);
x_345 = lean_ctor_get(x_200, 1);
lean_inc(x_345);
lean_dec(x_200);
x_346 = l_Lean_Expr_app___override(x_344, x_345);
x_347 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_346, x_2, x_3);
lean_dec(x_2);
lean_dec(x_346);
return x_347;
}
case 6:
{
lean_object* x_348; lean_object* x_349; lean_object* x_350; uint8_t x_351; lean_object* x_352; lean_object* x_353; 
lean_dec(x_4);
lean_dec(x_1);
x_348 = lean_ctor_get(x_200, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_200, 1);
lean_inc(x_349);
x_350 = lean_ctor_get(x_200, 2);
lean_inc(x_350);
x_351 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_352 = l_Lean_Expr_lam___override(x_348, x_349, x_350, x_351);
x_353 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_352, x_2, x_3);
lean_dec(x_2);
lean_dec(x_352);
return x_353;
}
case 7:
{
lean_object* x_354; lean_object* x_355; lean_object* x_356; uint8_t x_357; lean_object* x_358; lean_object* x_359; 
lean_dec(x_4);
lean_dec(x_1);
x_354 = lean_ctor_get(x_200, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_200, 1);
lean_inc(x_355);
x_356 = lean_ctor_get(x_200, 2);
lean_inc(x_356);
x_357 = lean_ctor_get_uint8(x_200, sizeof(void*)*3 + 8);
lean_dec(x_200);
x_358 = l_Lean_Expr_forallE___override(x_354, x_355, x_356, x_357);
x_359 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_358, x_2, x_3);
lean_dec(x_2);
lean_dec(x_358);
return x_359;
}
case 8:
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; uint8_t x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_4);
lean_dec(x_1);
x_360 = lean_ctor_get(x_200, 0);
lean_inc(x_360);
x_361 = lean_ctor_get(x_200, 1);
lean_inc(x_361);
x_362 = lean_ctor_get(x_200, 2);
lean_inc(x_362);
x_363 = lean_ctor_get(x_200, 3);
lean_inc(x_363);
x_364 = lean_ctor_get_uint8(x_200, sizeof(void*)*4 + 8);
lean_dec(x_200);
x_365 = l_Lean_Expr_letE___override(x_360, x_361, x_362, x_363, x_364);
x_366 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_365, x_2, x_3);
lean_dec(x_2);
lean_dec(x_365);
return x_366;
}
case 9:
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; 
lean_dec(x_4);
lean_dec(x_1);
x_367 = lean_ctor_get(x_200, 0);
lean_inc(x_367);
lean_dec(x_200);
x_368 = l_Lean_Expr_lit___override(x_367);
x_369 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_368, x_2, x_3);
lean_dec(x_2);
lean_dec(x_368);
return x_369;
}
case 10:
{
lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_4);
lean_dec(x_1);
x_370 = lean_ctor_get(x_200, 0);
lean_inc(x_370);
x_371 = lean_ctor_get(x_200, 1);
lean_inc(x_371);
lean_dec(x_200);
x_372 = l_Lean_Expr_mdata___override(x_370, x_371);
x_373 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_372, x_2, x_3);
lean_dec(x_2);
lean_dec(x_372);
return x_373;
}
default: 
{
lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
lean_dec(x_4);
lean_dec(x_1);
x_374 = lean_ctor_get(x_200, 0);
lean_inc(x_374);
x_375 = lean_ctor_get(x_200, 1);
lean_inc(x_375);
x_376 = lean_ctor_get(x_200, 2);
lean_inc(x_376);
lean_dec(x_200);
x_377 = l_Lean_Expr_proj___override(x_374, x_375, x_376);
x_378 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_377, x_2, x_3);
lean_dec(x_2);
lean_dec(x_377);
return x_378;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__0___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__0(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_getSimprocFromDeclImpl___lam__1(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_toSimprocEntry(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc(x_4);
x_5 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_4, x_2, x_3);
if (lean_obj_tag(x_5) == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
lean_ctor_set(x_5, 0, x_8);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_5, 0);
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_inc(x_9);
lean_dec(x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
lean_dec(x_1);
x_13 = !lean_is_exclusive(x_5);
if (x_13 == 0)
{
return x_5;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_5, 0);
x_15 = lean_ctor_get(x_5, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_5);
x_16 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_Simprocs_erase(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
lean_inc(x_2);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___lam__0), 2, 1);
lean_closure_set(x_10, 0, x_2);
x_11 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_12 = lean_ctor_get(x_8, 0);
lean_inc(x_12);
lean_dec(x_8);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get_uint8(x_14, sizeof(void*)*3);
lean_dec(x_14);
x_16 = l_Lean_ScopedEnvExtension_getState___redArg(x_11, x_1, x_12, x_15);
x_17 = lean_ctor_get(x_16, 2);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_17, x_2);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
lean_dec(x_10);
lean_dec(x_1);
x_19 = lean_mk_string_unchecked("'", 1, 1);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = l_Lean_MessageData_ofName(x_2);
lean_ctor_set_tag(x_6, 7);
lean_ctor_set(x_6, 1, x_21);
lean_ctor_set(x_6, 0, x_20);
x_22 = lean_mk_string_unchecked("' does not have a simproc attribute", 35, 35);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_6);
lean_ctor_set(x_24, 1, x_23);
x_25 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_24, x_3, x_4, x_9);
return x_25;
}
else
{
lean_object* x_26; uint8_t x_27; 
lean_free_object(x_6);
lean_dec(x_2);
x_26 = lean_st_ref_take(x_4, x_9);
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; uint8_t x_42; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = lean_ctor_get(x_26, 1);
x_30 = lean_ctor_get(x_28, 0);
lean_inc(x_30);
x_31 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_1, x_30, x_10);
x_32 = lean_ctor_get(x_28, 1);
lean_inc(x_32);
x_33 = lean_ctor_get(x_28, 2);
lean_inc(x_33);
x_34 = lean_ctor_get(x_28, 3);
lean_inc(x_34);
x_35 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_35);
lean_inc(x_36);
lean_ctor_set(x_26, 1, x_36);
lean_ctor_set(x_26, 0, x_36);
x_37 = lean_ctor_get(x_28, 5);
lean_inc(x_37);
x_38 = lean_ctor_get(x_28, 6);
lean_inc(x_38);
x_39 = lean_ctor_get(x_28, 7);
lean_inc(x_39);
lean_dec(x_28);
x_40 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_40, 0, x_31);
lean_ctor_set(x_40, 1, x_32);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_26);
lean_ctor_set(x_40, 5, x_37);
lean_ctor_set(x_40, 6, x_38);
lean_ctor_set(x_40, 7, x_39);
x_41 = lean_st_ref_set(x_4, x_40, x_29);
x_42 = !lean_is_exclusive(x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_41, 0);
lean_dec(x_43);
x_44 = lean_box(0);
lean_ctor_set(x_41, 0, x_44);
return x_41;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_41, 1);
lean_inc(x_45);
lean_dec(x_41);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_45);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_48 = lean_ctor_get(x_26, 0);
x_49 = lean_ctor_get(x_26, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_26);
x_50 = lean_ctor_get(x_48, 0);
lean_inc(x_50);
x_51 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_1, x_50, x_10);
x_52 = lean_ctor_get(x_48, 1);
lean_inc(x_52);
x_53 = lean_ctor_get(x_48, 2);
lean_inc(x_53);
x_54 = lean_ctor_get(x_48, 3);
lean_inc(x_54);
x_55 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_56 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_56, 0, x_55);
lean_inc(x_56);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_56);
x_58 = lean_ctor_get(x_48, 5);
lean_inc(x_58);
x_59 = lean_ctor_get(x_48, 6);
lean_inc(x_59);
x_60 = lean_ctor_get(x_48, 7);
lean_inc(x_60);
lean_dec(x_48);
x_61 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_61, 0, x_51);
lean_ctor_set(x_61, 1, x_52);
lean_ctor_set(x_61, 2, x_53);
lean_ctor_set(x_61, 3, x_54);
lean_ctor_set(x_61, 4, x_57);
lean_ctor_set(x_61, 5, x_58);
lean_ctor_set(x_61, 6, x_59);
lean_ctor_set(x_61, 7, x_60);
x_62 = lean_st_ref_set(x_4, x_61, x_49);
x_63 = lean_ctor_get(x_62, 1);
lean_inc(x_63);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 x_64 = x_62;
} else {
 lean_dec_ref(x_62);
 x_64 = lean_box(0);
}
x_65 = lean_box(0);
if (lean_is_scalar(x_64)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_64;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_63);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_67 = lean_ctor_get(x_6, 0);
x_68 = lean_ctor_get(x_6, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_6);
lean_inc(x_2);
x_69 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___lam__0), 2, 1);
lean_closure_set(x_69, 0, x_2);
x_70 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_71 = lean_ctor_get(x_67, 0);
lean_inc(x_71);
lean_dec(x_67);
x_72 = lean_ctor_get(x_1, 1);
lean_inc(x_72);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
lean_dec(x_72);
x_74 = lean_ctor_get_uint8(x_73, sizeof(void*)*3);
lean_dec(x_73);
x_75 = l_Lean_ScopedEnvExtension_getState___redArg(x_70, x_1, x_71, x_74);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
lean_dec(x_75);
x_77 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_76, x_2);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
lean_dec(x_69);
lean_dec(x_1);
x_78 = lean_mk_string_unchecked("'", 1, 1);
x_79 = l_Lean_stringToMessageData(x_78);
lean_dec(x_78);
x_80 = l_Lean_MessageData_ofName(x_2);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("' does not have a simproc attribute", 35, 35);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_84, x_3, x_4, x_68);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
lean_dec(x_2);
x_86 = lean_st_ref_take(x_4, x_68);
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
x_90 = lean_ctor_get(x_87, 0);
lean_inc(x_90);
x_91 = l_Lean_ScopedEnvExtension_modifyState___redArg(x_1, x_90, x_69);
x_92 = lean_ctor_get(x_87, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_87, 2);
lean_inc(x_93);
x_94 = lean_ctor_get(x_87, 3);
lean_inc(x_94);
x_95 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_96 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_96, 0, x_95);
lean_inc(x_96);
if (lean_is_scalar(x_89)) {
 x_97 = lean_alloc_ctor(0, 2, 0);
} else {
 x_97 = x_89;
}
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_96);
x_98 = lean_ctor_get(x_87, 5);
lean_inc(x_98);
x_99 = lean_ctor_get(x_87, 6);
lean_inc(x_99);
x_100 = lean_ctor_get(x_87, 7);
lean_inc(x_100);
lean_dec(x_87);
x_101 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_101, 0, x_91);
lean_ctor_set(x_101, 1, x_92);
lean_ctor_set(x_101, 2, x_93);
lean_ctor_set(x_101, 3, x_94);
lean_ctor_set(x_101, 4, x_97);
lean_ctor_set(x_101, 5, x_98);
lean_ctor_set(x_101, 6, x_99);
lean_ctor_set(x_101, 7, x_100);
x_102 = lean_st_ref_set(x_4, x_101, x_88);
x_103 = lean_ctor_get(x_102, 1);
lean_inc(x_103);
if (lean_is_exclusive(x_102)) {
 lean_ctor_release(x_102, 0);
 lean_ctor_release(x_102, 1);
 x_104 = x_102;
} else {
 lean_dec_ref(x_102);
 x_104 = lean_box(0);
}
x_105 = lean_box(0);
if (lean_is_scalar(x_104)) {
 x_106 = lean_alloc_ctor(0, 2, 0);
} else {
 x_106 = x_104;
}
lean_ctor_set(x_106, 0, x_105);
lean_ctor_set(x_106, 1, x_103);
return x_106;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_eraseSimprocAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Meta_Simp_eraseSimprocAttr(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_get(x_6, x_7);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_5, 2);
lean_inc(x_13);
lean_ctor_set(x_8, 1, x_13);
lean_ctor_set(x_8, 0, x_12);
lean_inc(x_2);
x_14 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_8, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_2);
x_17 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(x_2, x_6, x_16);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
if (lean_obj_tag(x_18) == 0)
{
uint8_t x_19; 
lean_dec(x_15);
lean_dec(x_1);
x_19 = !lean_is_exclusive(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_20 = lean_ctor_get(x_17, 1);
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_23 = l_Lean_stringToMessageData(x_22);
lean_dec(x_22);
x_24 = l_Lean_MessageData_ofName(x_2);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_24);
lean_ctor_set(x_17, 0, x_23);
x_25 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_17);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_27, x_5, x_6, x_20);
lean_dec(x_5);
return x_28;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = l_Lean_MessageData_ofName(x_2);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
x_37 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_36, x_5, x_6, x_29);
lean_dec(x_5);
return x_37;
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_17);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_39 = lean_ctor_get(x_17, 1);
x_40 = lean_ctor_get(x_17, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_18, 0);
lean_inc(x_41);
lean_dec(x_18);
x_42 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_42, 0, x_2);
lean_ctor_set(x_42, 1, x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*2, x_4);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 0, x_42);
x_43 = l_Lean_ScopedEnvExtension_add___at___Lean_KeyedDeclsAttribute_init_spec__1(lean_box(0), lean_box(0), lean_box(0), x_1, x_17, x_3, x_5, x_6, x_39);
return x_43;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_44 = lean_ctor_get(x_17, 1);
lean_inc(x_44);
lean_dec(x_17);
x_45 = lean_ctor_get(x_18, 0);
lean_inc(x_45);
lean_dec(x_18);
x_46 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_46, 0, x_2);
lean_ctor_set(x_46, 1, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*2, x_4);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_15);
x_48 = l_Lean_ScopedEnvExtension_add___at___Lean_KeyedDeclsAttribute_init_spec__1(lean_box(0), lean_box(0), lean_box(0), x_1, x_47, x_3, x_5, x_6, x_44);
return x_48;
}
}
}
else
{
uint8_t x_49; 
lean_dec(x_2);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_14);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_14, 0);
x_51 = lean_ctor_get(x_5, 5);
lean_inc(x_51);
lean_dec(x_5);
x_52 = lean_io_error_to_string(x_50);
x_53 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = l_Lean_MessageData_ofFormat(x_53);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_51);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set(x_14, 0, x_55);
return x_14;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_14, 0);
x_57 = lean_ctor_get(x_14, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_14);
x_58 = lean_ctor_get(x_5, 5);
lean_inc(x_58);
lean_dec(x_5);
x_59 = lean_io_error_to_string(x_56);
x_60 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_60, 0, x_59);
x_61 = l_Lean_MessageData_ofFormat(x_60);
x_62 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_62, 0, x_58);
lean_ctor_set(x_62, 1, x_61);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_62);
lean_ctor_set(x_63, 1, x_57);
return x_63;
}
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_64 = lean_ctor_get(x_8, 0);
x_65 = lean_ctor_get(x_8, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_8);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
lean_dec(x_64);
x_67 = lean_ctor_get(x_5, 2);
lean_inc(x_67);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_2);
x_69 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_68, x_65);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_2);
x_72 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(x_2, x_6, x_71);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_70);
lean_dec(x_1);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
x_76 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_77 = l_Lean_stringToMessageData(x_76);
lean_dec(x_76);
x_78 = l_Lean_MessageData_ofName(x_2);
if (lean_is_scalar(x_75)) {
 x_79 = lean_alloc_ctor(7, 2, 0);
} else {
 x_79 = x_75;
 lean_ctor_set_tag(x_79, 7);
}
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
x_80 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_79);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_82, x_5, x_6, x_74);
lean_dec(x_5);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_84 = lean_ctor_get(x_72, 1);
lean_inc(x_84);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_85 = x_72;
} else {
 lean_dec_ref(x_72);
 x_85 = lean_box(0);
}
x_86 = lean_ctor_get(x_73, 0);
lean_inc(x_86);
lean_dec(x_73);
x_87 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_87, 0, x_2);
lean_ctor_set(x_87, 1, x_86);
lean_ctor_set_uint8(x_87, sizeof(void*)*2, x_4);
if (lean_is_scalar(x_85)) {
 x_88 = lean_alloc_ctor(0, 2, 0);
} else {
 x_88 = x_85;
}
lean_ctor_set(x_88, 0, x_87);
lean_ctor_set(x_88, 1, x_70);
x_89 = l_Lean_ScopedEnvExtension_add___at___Lean_KeyedDeclsAttribute_init_spec__1(lean_box(0), lean_box(0), lean_box(0), x_1, x_88, x_3, x_5, x_6, x_84);
return x_89;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_2);
lean_dec(x_1);
x_90 = lean_ctor_get(x_69, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_69, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_92 = x_69;
} else {
 lean_dec_ref(x_69);
 x_92 = lean_box(0);
}
x_93 = lean_ctor_get(x_5, 5);
lean_inc(x_93);
lean_dec(x_5);
x_94 = lean_io_error_to_string(x_90);
x_95 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_95, 0, x_94);
x_96 = l_Lean_MessageData_ofFormat(x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_93);
lean_ctor_set(x_97, 1, x_96);
if (lean_is_scalar(x_92)) {
 x_98 = lean_alloc_ctor(1, 2, 0);
} else {
 x_98 = x_92;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_91);
return x_98;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttrCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; uint8_t x_9; lean_object* x_10; 
x_8 = lean_unbox(x_3);
lean_dec(x_3);
x_9 = lean_unbox(x_4);
lean_dec(x_4);
x_10 = l_Lean_Meta_Simp_addSimprocAttrCore(x_1, x_2, x_8, x_9, x_5, x_6, x_7);
lean_dec(x_6);
return x_10;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_7 = lean_array_fget(x_1, x_3);
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = lean_ctor_get(x_7, 0);
lean_inc(x_10);
lean_dec(x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_name_eq(x_9, x_11);
lean_dec(x_11);
lean_dec(x_9);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_nat_add(x_3, x_13);
lean_dec(x_3);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; 
x_16 = lean_array_fset(x_1, x_3, x_2);
lean_dec(x_3);
return x_16;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal_loop___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__0_spec__0(x_1, x_2, x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_8 = lean_array_fget(x_2, x_1);
x_9 = lean_nat_add(x_6, x_7);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_shiftr(x_9, x_10);
lean_dec(x_9);
x_12 = lean_array_fget(x_4, x_11);
x_13 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_12, x_5);
if (x_13 == 0)
{
uint8_t x_14; 
lean_dec(x_7);
x_14 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_5, x_12);
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
x_23 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(x_2, x_3, x_22, x_18);
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
x_29 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(x_2, x_3, x_28, x_25);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
LEAN_EXPORT uint8_t l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = l_Lean_Meta_DiscrTree_Key_lt(x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(x_2, x_3, x_10, x_7);
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
x_15 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(x_2, x_3, x_14, x_12);
lean_dec(x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1(x_5, x_10);
if (x_11 == 0)
{
uint8_t x_12; 
x_12 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1(x_10, x_5);
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
x_16 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_10);
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
x_21 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1(x_20, x_5);
if (x_21 == 0)
{
uint8_t x_22; 
x_22 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1(x_5, x_20);
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
x_26 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_20);
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
x_28 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_19);
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
x_32 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_20);
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
x_35 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_34);
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
x_40 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_6, x_10);
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
x_43 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_42);
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
x_47 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_6, x_46);
x_48 = lean_array_push(x_4, x_47);
return x_48;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
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
x_10 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__0(x_6, x_2);
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
x_15 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_7, x_14);
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
x_21 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertVal___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__0(x_17, x_2);
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
x_28 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2(x_3, x_1, x_2, x_18, x_27);
lean_dec(x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_17);
lean_ctor_set(x_29, 1, x_28);
return x_29;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__5(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_14 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(x_2, x_3, x_13, x_12);
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
x_22 = l_panic___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__5(x_21);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 2);
lean_inc(x_8);
x_9 = lean_box(0);
lean_inc(x_3);
x_10 = l_Lean_PersistentHashMap_insert___at___Lean_MetavarContext_addExprMVarDecl_spec__0(lean_box(0), x_8, x_3, x_9);
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_3);
x_12 = l_Lean_PersistentHashMap_erase___at___Lean_MetavarContext_setMVarUserName_spec__0(lean_box(0), x_11, x_3);
if (x_4 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_inc(x_2);
x_13 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_13, 0, x_3);
lean_ctor_set(x_13, 1, x_2);
lean_ctor_set_uint8(x_13, sizeof(void*)*2, x_4);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
x_15 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0(x_6, x_2, x_14);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_7);
lean_ctor_set(x_16, 2, x_10);
lean_ctor_set(x_16, 3, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_inc(x_2);
x_17 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_2);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_4);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_5);
x_19 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0(x_7, x_2, x_18);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_20, 0, x_6);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set(x_20, 2, x_10);
lean_ctor_set(x_20, 3, x_12);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___lam__0(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__0(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__1(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Array_binInsertM___at_____private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lean_Meta_DiscrTree_0__Lean_Meta_DiscrTree_insertAux___at___Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_DiscrTree_insertCore___at___Lean_Meta_Simp_Simprocs_addCore_spec__0(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_addCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_4);
lean_dec(x_4);
x_7 = l_Lean_Meta_Simp_Simprocs_addCore(x_1, x_2, x_3, x_6, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
x_7 = lean_st_ref_get(x_6, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
lean_dec(x_8);
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; lean_object* x_31; 
x_11 = lean_ctor_get(x_7, 1);
x_12 = lean_ctor_get(x_7, 0);
lean_dec(x_12);
x_13 = lean_ctor_get(x_9, 1);
lean_inc(x_13);
lean_dec(x_9);
x_14 = lean_array_get_size(x_13);
x_15 = l_Lean_Name_hash___override(x_2);
x_16 = lean_unsigned_to_nat(32u);
x_17 = lean_uint64_of_nat(x_16);
x_18 = lean_uint64_shift_right(x_15, x_17);
x_19 = lean_uint64_xor(x_15, x_18);
x_20 = lean_unsigned_to_nat(16u);
x_21 = lean_uint64_of_nat(x_20);
x_22 = lean_uint64_shift_right(x_19, x_21);
x_23 = lean_uint64_xor(x_19, x_22);
x_24 = lean_uint64_to_usize(x_23);
x_25 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_usize_of_nat(x_26);
x_28 = lean_usize_sub(x_25, x_27);
x_29 = lean_usize_land(x_24, x_28);
x_30 = lean_array_uget(x_13, x_29);
lean_dec(x_13);
x_31 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_2, x_30);
lean_dec(x_30);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_4);
lean_dec(x_2);
x_32 = lean_mk_string_unchecked("invalid [builtin_simproc] attribute, '{declName}' is not a builtin simproc", 74, 74);
x_33 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set_tag(x_7, 1);
lean_ctor_set(x_7, 0, x_33);
return x_7;
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_free_object(x_7);
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
lean_dec(x_31);
x_35 = lean_st_ref_take(x_1, x_11);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Meta_Simp_Simprocs_addCore(x_36, x_34, x_2, x_3, x_4);
x_39 = lean_st_ref_set(x_1, x_38, x_37);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
return x_39;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_39);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; uint64_t x_47; lean_object* x_48; uint64_t x_49; uint64_t x_50; uint64_t x_51; lean_object* x_52; uint64_t x_53; uint64_t x_54; uint64_t x_55; size_t x_56; size_t x_57; lean_object* x_58; size_t x_59; size_t x_60; size_t x_61; lean_object* x_62; lean_object* x_63; 
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
lean_dec(x_7);
x_45 = lean_ctor_get(x_9, 1);
lean_inc(x_45);
lean_dec(x_9);
x_46 = lean_array_get_size(x_45);
x_47 = l_Lean_Name_hash___override(x_2);
x_48 = lean_unsigned_to_nat(32u);
x_49 = lean_uint64_of_nat(x_48);
x_50 = lean_uint64_shift_right(x_47, x_49);
x_51 = lean_uint64_xor(x_47, x_50);
x_52 = lean_unsigned_to_nat(16u);
x_53 = lean_uint64_of_nat(x_52);
x_54 = lean_uint64_shift_right(x_51, x_53);
x_55 = lean_uint64_xor(x_51, x_54);
x_56 = lean_uint64_to_usize(x_55);
x_57 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_58 = lean_unsigned_to_nat(1u);
x_59 = lean_usize_of_nat(x_58);
x_60 = lean_usize_sub(x_57, x_59);
x_61 = lean_usize_land(x_56, x_60);
x_62 = lean_array_uget(x_45, x_61);
lean_dec(x_45);
x_63 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_2, x_62);
lean_dec(x_62);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_4);
lean_dec(x_2);
x_64 = lean_mk_string_unchecked("invalid [builtin_simproc] attribute, '{declName}' is not a builtin simproc", 74, 74);
x_65 = lean_alloc_ctor(18, 1, 0);
lean_ctor_set(x_65, 0, x_64);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_44);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_67 = lean_ctor_get(x_63, 0);
lean_inc(x_67);
lean_dec(x_63);
x_68 = lean_st_ref_take(x_1, x_44);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = l_Lean_Meta_Simp_Simprocs_addCore(x_69, x_67, x_2, x_3, x_4);
x_72 = lean_st_ref_set(x_1, x_71, x_70);
x_73 = lean_ctor_get(x_72, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_72, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_72)) {
 lean_ctor_release(x_72, 0);
 lean_ctor_release(x_72, 1);
 x_75 = x_72;
} else {
 lean_dec_ref(x_72);
 x_75 = lean_box(0);
}
if (lean_is_scalar(x_75)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttrCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_3);
lean_dec(x_3);
x_7 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_1, x_2, x_6, x_4, x_5);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Simp_builtinSimprocsRef;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocBuiltinAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttr(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Meta_Simp_builtinSEvalprocsRef;
x_6 = l_Lean_Meta_Simp_addSimprocBuiltinAttrCore(x_5, x_1, x_2, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSEvalprocBuiltinAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_2);
lean_dec(x_2);
x_6 = l_Lean_Meta_Simp_addSEvalprocBuiltinAttr(x_1, x_5, x_3, x_4);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_29; uint8_t x_30; 
x_29 = lean_st_ref_get(x_5, x_6);
x_30 = !lean_is_exclusive(x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_29, 0);
x_32 = lean_ctor_get(x_29, 1);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
lean_dec(x_31);
x_34 = lean_ctor_get(x_4, 2);
lean_inc(x_34);
lean_ctor_set(x_29, 1, x_34);
lean_ctor_set(x_29, 0, x_33);
lean_inc(x_2);
x_35 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_29, x_32);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_7 = x_36;
x_8 = x_37;
goto block_28;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; uint8_t x_161; 
x_38 = lean_ctor_get(x_35, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_35)) {
 lean_ctor_release(x_35, 0);
 lean_ctor_release(x_35, 1);
 x_40 = x_35;
} else {
 lean_dec_ref(x_35);
 x_40 = lean_box(0);
}
x_41 = lean_ctor_get(x_4, 5);
x_42 = lean_io_error_to_string(x_38);
x_43 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_43, 0, x_42);
x_44 = l_Lean_MessageData_ofFormat(x_43);
lean_inc(x_41);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_44);
x_161 = l_Lean_Exception_isInterrupt(x_45);
if (x_161 == 0)
{
uint8_t x_162; 
x_162 = l_Lean_Exception_isRuntime(x_45);
x_46 = x_162;
goto block_160;
}
else
{
x_46 = x_161;
goto block_160;
}
block_160:
{
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; uint8_t x_49; 
lean_dec(x_40);
x_47 = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(x_2, x_5, x_39);
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
x_49 = lean_unbox(x_48);
lean_dec(x_48);
if (x_49 == 0)
{
uint8_t x_50; 
lean_dec(x_2);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_47);
if (x_50 == 0)
{
lean_object* x_51; 
x_51 = lean_ctor_get(x_47, 0);
lean_dec(x_51);
lean_ctor_set_tag(x_47, 1);
lean_ctor_set(x_47, 0, x_45);
return x_47;
}
else
{
lean_object* x_52; lean_object* x_53; 
x_52 = lean_ctor_get(x_47, 1);
lean_inc(x_52);
lean_dec(x_47);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_45);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
lean_dec(x_45);
x_54 = lean_ctor_get(x_47, 1);
lean_inc(x_54);
lean_dec(x_47);
x_55 = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
x_56 = lean_st_ref_get(x_55, x_54);
x_57 = lean_ctor_get(x_56, 0);
lean_inc(x_57);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = !lean_is_exclusive(x_56);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_ctor_get(x_56, 1);
x_61 = lean_ctor_get(x_56, 0);
lean_dec(x_61);
x_62 = !lean_is_exclusive(x_58);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; uint64_t x_66; lean_object* x_67; uint64_t x_68; uint64_t x_69; uint64_t x_70; lean_object* x_71; uint64_t x_72; uint64_t x_73; uint64_t x_74; size_t x_75; size_t x_76; lean_object* x_77; size_t x_78; size_t x_79; size_t x_80; lean_object* x_81; lean_object* x_82; 
x_63 = lean_ctor_get(x_58, 1);
x_64 = lean_ctor_get(x_58, 0);
lean_dec(x_64);
x_65 = lean_array_get_size(x_63);
x_66 = l_Lean_Name_hash___override(x_2);
x_67 = lean_unsigned_to_nat(32u);
x_68 = lean_uint64_of_nat(x_67);
x_69 = lean_uint64_shift_right(x_66, x_68);
x_70 = lean_uint64_xor(x_66, x_69);
x_71 = lean_unsigned_to_nat(16u);
x_72 = lean_uint64_of_nat(x_71);
x_73 = lean_uint64_shift_right(x_70, x_72);
x_74 = lean_uint64_xor(x_70, x_73);
x_75 = lean_uint64_to_usize(x_74);
x_76 = lean_usize_of_nat(x_65);
lean_dec(x_65);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_usize_of_nat(x_77);
x_79 = lean_usize_sub(x_76, x_78);
x_80 = lean_usize_land(x_75, x_79);
x_81 = lean_array_uget(x_63, x_80);
lean_dec(x_63);
x_82 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_2, x_81);
lean_dec(x_81);
if (lean_obj_tag(x_82) == 0)
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
lean_dec(x_1);
x_83 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_84 = l_Lean_stringToMessageData(x_83);
lean_dec(x_83);
x_85 = l_Lean_MessageData_ofName(x_2);
lean_ctor_set_tag(x_58, 7);
lean_ctor_set(x_58, 1, x_85);
lean_ctor_set(x_58, 0, x_84);
x_86 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_87);
lean_ctor_set(x_56, 0, x_58);
x_88 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_56, x_4, x_5, x_60);
x_89 = !lean_is_exclusive(x_88);
if (x_89 == 0)
{
return x_88;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_88, 0);
x_91 = lean_ctor_get(x_88, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_88);
x_92 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_92, 0, x_90);
lean_ctor_set(x_92, 1, x_91);
return x_92;
}
}
else
{
lean_object* x_93; 
lean_free_object(x_58);
lean_free_object(x_56);
x_93 = lean_ctor_get(x_82, 0);
lean_inc(x_93);
lean_dec(x_82);
x_7 = x_93;
x_8 = x_60;
goto block_28;
}
}
else
{
lean_object* x_94; lean_object* x_95; uint64_t x_96; lean_object* x_97; uint64_t x_98; uint64_t x_99; uint64_t x_100; lean_object* x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; size_t x_105; size_t x_106; lean_object* x_107; size_t x_108; size_t x_109; size_t x_110; lean_object* x_111; lean_object* x_112; 
x_94 = lean_ctor_get(x_58, 1);
lean_inc(x_94);
lean_dec(x_58);
x_95 = lean_array_get_size(x_94);
x_96 = l_Lean_Name_hash___override(x_2);
x_97 = lean_unsigned_to_nat(32u);
x_98 = lean_uint64_of_nat(x_97);
x_99 = lean_uint64_shift_right(x_96, x_98);
x_100 = lean_uint64_xor(x_96, x_99);
x_101 = lean_unsigned_to_nat(16u);
x_102 = lean_uint64_of_nat(x_101);
x_103 = lean_uint64_shift_right(x_100, x_102);
x_104 = lean_uint64_xor(x_100, x_103);
x_105 = lean_uint64_to_usize(x_104);
x_106 = lean_usize_of_nat(x_95);
lean_dec(x_95);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_usize_of_nat(x_107);
x_109 = lean_usize_sub(x_106, x_108);
x_110 = lean_usize_land(x_105, x_109);
x_111 = lean_array_uget(x_94, x_110);
lean_dec(x_94);
x_112 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_2, x_111);
lean_dec(x_111);
if (lean_obj_tag(x_112) == 0)
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_1);
x_113 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = l_Lean_MessageData_ofName(x_2);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_114);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
lean_ctor_set_tag(x_56, 7);
lean_ctor_set(x_56, 1, x_118);
lean_ctor_set(x_56, 0, x_116);
x_119 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_56, x_4, x_5, x_60);
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_122 = x_119;
} else {
 lean_dec_ref(x_119);
 x_122 = lean_box(0);
}
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(1, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_120);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; 
lean_free_object(x_56);
x_124 = lean_ctor_get(x_112, 0);
lean_inc(x_124);
lean_dec(x_112);
x_7 = x_124;
x_8 = x_60;
goto block_28;
}
}
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint64_t x_129; lean_object* x_130; uint64_t x_131; uint64_t x_132; uint64_t x_133; lean_object* x_134; uint64_t x_135; uint64_t x_136; uint64_t x_137; size_t x_138; size_t x_139; lean_object* x_140; size_t x_141; size_t x_142; size_t x_143; lean_object* x_144; lean_object* x_145; 
x_125 = lean_ctor_get(x_56, 1);
lean_inc(x_125);
lean_dec(x_56);
x_126 = lean_ctor_get(x_58, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_58)) {
 lean_ctor_release(x_58, 0);
 lean_ctor_release(x_58, 1);
 x_127 = x_58;
} else {
 lean_dec_ref(x_58);
 x_127 = lean_box(0);
}
x_128 = lean_array_get_size(x_126);
x_129 = l_Lean_Name_hash___override(x_2);
x_130 = lean_unsigned_to_nat(32u);
x_131 = lean_uint64_of_nat(x_130);
x_132 = lean_uint64_shift_right(x_129, x_131);
x_133 = lean_uint64_xor(x_129, x_132);
x_134 = lean_unsigned_to_nat(16u);
x_135 = lean_uint64_of_nat(x_134);
x_136 = lean_uint64_shift_right(x_133, x_135);
x_137 = lean_uint64_xor(x_133, x_136);
x_138 = lean_uint64_to_usize(x_137);
x_139 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_140 = lean_unsigned_to_nat(1u);
x_141 = lean_usize_of_nat(x_140);
x_142 = lean_usize_sub(x_139, x_141);
x_143 = lean_usize_land(x_138, x_142);
x_144 = lean_array_uget(x_126, x_143);
lean_dec(x_126);
x_145 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_2, x_144);
lean_dec(x_144);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_1);
x_146 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_147 = l_Lean_stringToMessageData(x_146);
lean_dec(x_146);
x_148 = l_Lean_MessageData_ofName(x_2);
if (lean_is_scalar(x_127)) {
 x_149 = lean_alloc_ctor(7, 2, 0);
} else {
 x_149 = x_127;
 lean_ctor_set_tag(x_149, 7);
}
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_152, x_4, x_5, x_125);
x_154 = lean_ctor_get(x_153, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_153, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_153)) {
 lean_ctor_release(x_153, 0);
 lean_ctor_release(x_153, 1);
 x_156 = x_153;
} else {
 lean_dec_ref(x_153);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(1, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_154);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
else
{
lean_object* x_158; 
lean_dec(x_127);
x_158 = lean_ctor_get(x_145, 0);
lean_inc(x_158);
lean_dec(x_145);
x_7 = x_158;
x_8 = x_125;
goto block_28;
}
}
}
}
else
{
lean_object* x_159; 
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_40)) {
 x_159 = lean_alloc_ctor(1, 2, 0);
} else {
 x_159 = x_40;
}
lean_ctor_set(x_159, 0, x_45);
lean_ctor_set(x_159, 1, x_39);
return x_159;
}
}
}
}
else
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_163 = lean_ctor_get(x_29, 0);
x_164 = lean_ctor_get(x_29, 1);
lean_inc(x_164);
lean_inc(x_163);
lean_dec(x_29);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_4, 2);
lean_inc(x_166);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_165);
lean_ctor_set(x_167, 1, x_166);
lean_inc(x_2);
x_168 = l_Lean_Meta_Simp_getSimprocFromDeclImpl(x_2, x_167, x_164);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; 
x_169 = lean_ctor_get(x_168, 0);
lean_inc(x_169);
x_170 = lean_ctor_get(x_168, 1);
lean_inc(x_170);
lean_dec(x_168);
x_7 = x_169;
x_8 = x_170;
goto block_28;
}
else
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; uint8_t x_179; uint8_t x_228; 
x_171 = lean_ctor_get(x_168, 0);
lean_inc(x_171);
x_172 = lean_ctor_get(x_168, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_173 = x_168;
} else {
 lean_dec_ref(x_168);
 x_173 = lean_box(0);
}
x_174 = lean_ctor_get(x_4, 5);
x_175 = lean_io_error_to_string(x_171);
x_176 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_176, 0, x_175);
x_177 = l_Lean_MessageData_ofFormat(x_176);
lean_inc(x_174);
x_178 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_178, 0, x_174);
lean_ctor_set(x_178, 1, x_177);
x_228 = l_Lean_Exception_isInterrupt(x_178);
if (x_228 == 0)
{
uint8_t x_229; 
x_229 = l_Lean_Exception_isRuntime(x_178);
x_179 = x_229;
goto block_227;
}
else
{
x_179 = x_228;
goto block_227;
}
block_227:
{
if (x_179 == 0)
{
lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_173);
x_180 = l_Lean_Meta_Simp_isBuiltinSimproc___redArg(x_2, x_5, x_172);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
lean_dec(x_2);
lean_dec(x_1);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
if (lean_is_exclusive(x_180)) {
 lean_ctor_release(x_180, 0);
 lean_ctor_release(x_180, 1);
 x_184 = x_180;
} else {
 lean_dec_ref(x_180);
 x_184 = lean_box(0);
}
if (lean_is_scalar(x_184)) {
 x_185 = lean_alloc_ctor(1, 2, 0);
} else {
 x_185 = x_184;
 lean_ctor_set_tag(x_185, 1);
}
lean_ctor_set(x_185, 0, x_178);
lean_ctor_set(x_185, 1, x_183);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; uint64_t x_196; lean_object* x_197; uint64_t x_198; uint64_t x_199; uint64_t x_200; lean_object* x_201; uint64_t x_202; uint64_t x_203; uint64_t x_204; size_t x_205; size_t x_206; lean_object* x_207; size_t x_208; size_t x_209; size_t x_210; lean_object* x_211; lean_object* x_212; 
lean_dec(x_178);
x_186 = lean_ctor_get(x_180, 1);
lean_inc(x_186);
lean_dec(x_180);
x_187 = l_Lean_Meta_Simp_builtinSimprocDeclsRef;
x_188 = lean_st_ref_get(x_187, x_186);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = lean_ctor_get(x_188, 1);
lean_inc(x_191);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_192 = x_188;
} else {
 lean_dec_ref(x_188);
 x_192 = lean_box(0);
}
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
if (lean_is_exclusive(x_190)) {
 lean_ctor_release(x_190, 0);
 lean_ctor_release(x_190, 1);
 x_194 = x_190;
} else {
 lean_dec_ref(x_190);
 x_194 = lean_box(0);
}
x_195 = lean_array_get_size(x_193);
x_196 = l_Lean_Name_hash___override(x_2);
x_197 = lean_unsigned_to_nat(32u);
x_198 = lean_uint64_of_nat(x_197);
x_199 = lean_uint64_shift_right(x_196, x_198);
x_200 = lean_uint64_xor(x_196, x_199);
x_201 = lean_unsigned_to_nat(16u);
x_202 = lean_uint64_of_nat(x_201);
x_203 = lean_uint64_shift_right(x_200, x_202);
x_204 = lean_uint64_xor(x_200, x_203);
x_205 = lean_uint64_to_usize(x_204);
x_206 = lean_usize_of_nat(x_195);
lean_dec(x_195);
x_207 = lean_unsigned_to_nat(1u);
x_208 = lean_usize_of_nat(x_207);
x_209 = lean_usize_sub(x_206, x_208);
x_210 = lean_usize_land(x_205, x_209);
x_211 = lean_array_uget(x_193, x_210);
lean_dec(x_193);
x_212 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_SMap_find_x3f_x27___at___Lean_Kernel_Environment_find_x3f_spec__0_spec__0(lean_box(0), x_2, x_211);
lean_dec(x_211);
if (lean_obj_tag(x_212) == 0)
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; 
lean_dec(x_1);
x_213 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_214 = l_Lean_stringToMessageData(x_213);
lean_dec(x_213);
x_215 = l_Lean_MessageData_ofName(x_2);
if (lean_is_scalar(x_194)) {
 x_216 = lean_alloc_ctor(7, 2, 0);
} else {
 x_216 = x_194;
 lean_ctor_set_tag(x_216, 7);
}
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
x_217 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
if (lean_is_scalar(x_192)) {
 x_219 = lean_alloc_ctor(7, 2, 0);
} else {
 x_219 = x_192;
 lean_ctor_set_tag(x_219, 7);
}
lean_ctor_set(x_219, 0, x_216);
lean_ctor_set(x_219, 1, x_218);
x_220 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_219, x_4, x_5, x_191);
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
if (lean_is_scalar(x_223)) {
 x_224 = lean_alloc_ctor(1, 2, 0);
} else {
 x_224 = x_223;
}
lean_ctor_set(x_224, 0, x_221);
lean_ctor_set(x_224, 1, x_222);
return x_224;
}
else
{
lean_object* x_225; 
lean_dec(x_194);
lean_dec(x_192);
x_225 = lean_ctor_get(x_212, 0);
lean_inc(x_225);
lean_dec(x_212);
x_7 = x_225;
x_8 = x_191;
goto block_28;
}
}
}
else
{
lean_object* x_226; 
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_scalar(x_173)) {
 x_226 = lean_alloc_ctor(1, 2, 0);
} else {
 x_226 = x_173;
}
lean_ctor_set(x_226, 0, x_178);
lean_ctor_set(x_226, 1, x_172);
return x_226;
}
}
}
}
block_28:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_2);
x_9 = l_Lean_Meta_Simp_getSimprocDeclKeys_x3f___redArg(x_2, x_5, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
lean_dec(x_7);
lean_dec(x_1);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_mk_string_unchecked("invalid [simproc] attribute, '", 30, 30);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = l_Lean_MessageData_ofName(x_2);
x_15 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_mk_string_unchecked("' is not a simproc", 18, 18);
x_17 = l_Lean_stringToMessageData(x_16);
lean_dec(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_18, x_4, x_5, x_11);
return x_19;
}
else
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_9);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_9, 0);
lean_dec(x_21);
x_22 = lean_ctor_get(x_10, 0);
lean_inc(x_22);
lean_dec(x_10);
x_23 = l_Lean_Meta_Simp_Simprocs_addCore(x_1, x_22, x_2, x_3, x_7);
lean_ctor_set(x_9, 0, x_23);
return x_9;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_24 = lean_ctor_get(x_9, 1);
lean_inc(x_24);
lean_dec(x_9);
x_25 = lean_ctor_get(x_10, 0);
lean_inc(x_25);
lean_dec(x_10);
x_26 = l_Lean_Meta_Simp_Simprocs_addCore(x_1, x_25, x_2, x_3, x_7);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_Simprocs_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_Simp_Simprocs_add(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_ctor_get(x_1, 1);
x_6 = lean_nat_dec_lt(x_3, x_5);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_3);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_2);
lean_ctor_set(x_7, 1, x_4);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_8 = lean_ctor_get(x_2, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = l_Lean_Expr_appArg_x21(x_8);
x_11 = lean_array_push(x_9, x_10);
x_12 = l_Lean_Expr_appFn_x21(x_8);
lean_dec(x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_11);
x_14 = lean_ctor_get(x_1, 2);
x_15 = lean_nat_add(x_3, x_14);
lean_dec(x_3);
x_2 = x_13;
x_3 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(x_1, x_2, x_3, x_13);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_try(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_13);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(x_15, x_16, x_12, x_11);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_18, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_18, 1);
lean_inc(x_21);
lean_dec(x_18);
x_22 = l_Array_reverse(lean_box(0), x_21);
x_23 = lean_ctor_get(x_1, 1);
lean_inc(x_23);
lean_dec(x_1);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_25 = lean_apply_9(x_24, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = l_Lean_Meta_Simp_Step_addExtraArgs(x_26, x_22, x_7, x_8, x_9, x_10, x_27);
lean_dec(x_22);
return x_28;
}
else
{
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
return x_25;
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_23, 0);
lean_inc(x_29);
lean_dec(x_23);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
x_30 = lean_apply_9(x_29, x_20, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_19);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = l_Lean_TransformStep_toStep(x_31);
x_34 = l_Lean_Meta_Simp_Step_addExtraArgs(x_33, x_22, x_7, x_8, x_9, x_10, x_32);
lean_dec(x_22);
return x_34;
}
else
{
uint8_t x_35; 
lean_dec(x_22);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_35 = !lean_is_exclusive(x_30);
if (x_35 == 0)
{
return x_30;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_30, 0);
x_37 = lean_ctor_get(x_30, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_30);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocEntry_tryD(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_12 = lean_unsigned_to_nat(0u);
x_13 = lean_mk_empty_array_with_capacity(x_12);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_15, 0, x_12);
lean_ctor_set(x_15, 1, x_2);
lean_ctor_set(x_15, 2, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_3);
lean_ctor_set(x_16, 1, x_13);
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Meta_Simp_SimprocEntry_try_spec__0___redArg(x_15, x_16, x_12, x_11);
lean_dec(x_15);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 1);
lean_inc(x_19);
lean_dec(x_1);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_20 = !lean_is_exclusive(x_17);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_17, 0);
lean_dec(x_21);
x_22 = !lean_is_exclusive(x_19);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set_tag(x_19, 2);
lean_ctor_set(x_19, 0, x_24);
lean_ctor_set(x_17, 0, x_19);
return x_17;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_19);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_17, 0, x_26);
return x_17;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_dec(x_17);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_28 = x_19;
} else {
 lean_dec_ref(x_19);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
if (lean_is_scalar(x_28)) {
 x_30 = lean_alloc_ctor(2, 1, 0);
} else {
 x_30 = x_28;
 lean_ctor_set_tag(x_30, 2);
}
lean_ctor_set(x_30, 0, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_27);
return x_31;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_32 = lean_ctor_get(x_17, 1);
lean_inc(x_32);
lean_dec(x_17);
x_33 = lean_ctor_get(x_18, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_18, 1);
lean_inc(x_34);
lean_dec(x_18);
x_35 = lean_ctor_get(x_19, 0);
lean_inc(x_35);
lean_dec(x_19);
x_36 = lean_apply_9(x_35, x_33, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_32);
if (lean_obj_tag(x_36) == 0)
{
uint8_t x_37; 
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_38 = lean_ctor_get(x_36, 0);
x_39 = l_Array_reverse(lean_box(0), x_34);
x_40 = l_Lean_Meta_Simp_DStep_addExtraArgs(x_38, x_39);
lean_dec(x_39);
lean_ctor_set(x_36, 0, x_40);
return x_36;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_ctor_get(x_36, 0);
x_42 = lean_ctor_get(x_36, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_36);
x_43 = l_Array_reverse(lean_box(0), x_34);
x_44 = l_Lean_Meta_Simp_DStep_addExtraArgs(x_41, x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_42);
return x_45;
}
}
else
{
lean_dec(x_34);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_25 = lean_array_uget(x_4, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_1);
x_39 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_33);
x_40 = l_Lean_Meta_Simp_SimprocEntry_try(x_26, x_27, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_95 = lean_mk_string_unchecked("Debug", 5, 5);
x_96 = lean_mk_string_unchecked("Meta", 4, 4);
x_97 = lean_mk_string_unchecked("Tactic", 6, 6);
x_98 = lean_mk_string_unchecked("simp", 4, 4);
x_99 = l_Lean_Name_mkStr4(x_95, x_96, x_97, x_98);
lean_inc(x_99);
x_100 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_99, x_13, x_42);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_45 = x_10;
x_46 = x_11;
x_47 = x_12;
x_48 = x_13;
x_49 = x_14;
x_50 = x_103;
goto block_94;
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_105 = lean_ctor_get(x_100, 1);
x_106 = lean_ctor_get(x_100, 0);
lean_dec(x_106);
x_107 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
lean_inc(x_33);
x_109 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_100, 7);
lean_ctor_set(x_100, 1, x_109);
lean_ctor_set(x_100, 0, x_108);
x_110 = lean_mk_string_unchecked(" => ", 4, 4);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_100);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_ctor_get(x_43, 0);
lean_inc(x_113);
x_114 = l_Lean_MessageData_ofExpr(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("", 0, 0);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_99, x_118, x_11, x_12, x_13, x_14, x_105);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_45 = x_10;
x_46 = x_11;
x_47 = x_12;
x_48 = x_13;
x_49 = x_14;
x_50 = x_120;
goto block_94;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_121 = lean_ctor_get(x_100, 1);
lean_inc(x_121);
lean_dec(x_100);
x_122 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
lean_inc(x_33);
x_124 = l_Lean_MessageData_ofExpr(x_33);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked(" => ", 4, 4);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_ctor_get(x_43, 0);
lean_inc(x_129);
x_130 = l_Lean_MessageData_ofExpr(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_mk_string_unchecked("", 0, 0);
x_133 = l_Lean_stringToMessageData(x_132);
lean_dec(x_132);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_99, x_134, x_11, x_12, x_13, x_14, x_121);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_45 = x_10;
x_46 = x_11;
x_47 = x_12;
x_48 = x_13;
x_49 = x_14;
x_50 = x_136;
goto block_94;
}
}
block_94:
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_51, sizeof(void*)*1 + 1, x_3);
x_52 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_51, x_45, x_48, x_49, x_50);
lean_dec(x_45);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = lean_unbox(x_31);
lean_inc(x_36);
x_57 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_56, x_43, x_46, x_47, x_48, x_49, x_54);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_57, 0);
if (lean_is_scalar(x_44)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_44;
}
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_52, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_28;
}
lean_ctor_set(x_62, 0, x_33);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_31);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_57, 0, x_64);
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
if (lean_is_scalar(x_44)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_44;
}
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_52, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_28;
}
lean_ctor_set(x_69, 0, x_33);
lean_ctor_set(x_69, 1, x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_31);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_free_object(x_52);
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_73 = !lean_is_exclusive(x_57);
if (x_73 == 0)
{
return x_57;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_57, 0);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_57);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_52, 1);
lean_inc(x_77);
lean_dec(x_52);
x_78 = lean_unbox(x_31);
lean_inc(x_36);
x_79 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_78, x_43, x_46, x_47, x_48, x_49, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_44;
}
lean_ctor_set(x_83, 0, x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
if (lean_is_scalar(x_28)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_28;
}
lean_ctor_set(x_86, 0, x_33);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_31);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_82)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_82;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_137 = lean_ctor_get(x_40, 1);
lean_inc(x_137);
lean_dec(x_40);
x_138 = lean_ctor_get(x_41, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_139 = x_41;
} else {
 lean_dec_ref(x_41);
 x_139 = lean_box(0);
}
x_190 = lean_mk_string_unchecked("Debug", 5, 5);
x_191 = lean_mk_string_unchecked("Meta", 4, 4);
x_192 = lean_mk_string_unchecked("Tactic", 6, 6);
x_193 = lean_mk_string_unchecked("simp", 4, 4);
x_194 = l_Lean_Name_mkStr4(x_190, x_191, x_192, x_193);
lean_inc(x_194);
x_195 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_194, x_13, x_137);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; 
lean_dec(x_194);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_140 = x_10;
x_141 = x_11;
x_142 = x_12;
x_143 = x_13;
x_144 = x_14;
x_145 = x_198;
goto block_189;
}
else
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_195);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_200 = lean_ctor_get(x_195, 1);
x_201 = lean_ctor_get(x_195, 0);
lean_dec(x_201);
x_202 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_203 = l_Lean_stringToMessageData(x_202);
lean_dec(x_202);
lean_inc(x_33);
x_204 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_195, 7);
lean_ctor_set(x_195, 1, x_204);
lean_ctor_set(x_195, 0, x_203);
x_205 = lean_mk_string_unchecked(" => ", 4, 4);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_195);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_ctor_get(x_138, 0);
lean_inc(x_208);
x_209 = l_Lean_MessageData_ofExpr(x_208);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("", 0, 0);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_194, x_213, x_11, x_12, x_13, x_14, x_200);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_140 = x_10;
x_141 = x_11;
x_142 = x_12;
x_143 = x_13;
x_144 = x_14;
x_145 = x_215;
goto block_189;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_216 = lean_ctor_get(x_195, 1);
lean_inc(x_216);
lean_dec(x_195);
x_217 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
lean_inc(x_33);
x_219 = l_Lean_MessageData_ofExpr(x_33);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_mk_string_unchecked(" => ", 4, 4);
x_222 = l_Lean_stringToMessageData(x_221);
lean_dec(x_221);
x_223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_ctor_get(x_138, 0);
lean_inc(x_224);
x_225 = l_Lean_MessageData_ofExpr(x_224);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_mk_string_unchecked("", 0, 0);
x_228 = l_Lean_stringToMessageData(x_227);
lean_dec(x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_194, x_229, x_11, x_12, x_13, x_14, x_216);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_140 = x_10;
x_141 = x_11;
x_142 = x_12;
x_143 = x_13;
x_144 = x_14;
x_145 = x_231;
goto block_189;
}
}
block_189:
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_146, 0, x_38);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_146, sizeof(void*)*1 + 1, x_3);
x_147 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_146, x_140, x_143, x_144, x_145);
lean_dec(x_140);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_147, 1);
x_150 = lean_ctor_get(x_147, 0);
lean_dec(x_150);
x_151 = lean_unbox(x_31);
lean_inc(x_36);
x_152 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_151, x_138, x_141, x_142, x_143, x_144, x_149);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_152, 0);
if (lean_is_scalar(x_139)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_139;
}
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_147, 1, x_36);
lean_ctor_set(x_147, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_28;
}
lean_ctor_set(x_157, 0, x_33);
lean_ctor_set(x_157, 1, x_147);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_31);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_152, 0, x_159);
return x_152;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_152, 0);
x_161 = lean_ctor_get(x_152, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_152);
if (lean_is_scalar(x_139)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_139;
}
lean_ctor_set(x_162, 0, x_160);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_147, 1, x_36);
lean_ctor_set(x_147, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_28;
}
lean_ctor_set(x_164, 0, x_33);
lean_ctor_set(x_164, 1, x_147);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_31);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
return x_167;
}
}
else
{
uint8_t x_168; 
lean_free_object(x_147);
lean_dec(x_139);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_168 = !lean_is_exclusive(x_152);
if (x_168 == 0)
{
return x_152;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_152, 0);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_152);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_147, 1);
lean_inc(x_172);
lean_dec(x_147);
x_173 = lean_unbox(x_31);
lean_inc(x_36);
x_174 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_173, x_138, x_141, x_142, x_143, x_144, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_139;
}
lean_ctor_set(x_178, 0, x_175);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_35);
lean_ctor_set(x_180, 1, x_36);
if (lean_is_scalar(x_28)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_28;
}
lean_ctor_set(x_181, 0, x_33);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_31);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_177)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_177;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_176);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_139);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_185 = lean_ctor_get(x_174, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_187 = x_174;
} else {
 lean_dec_ref(x_174);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
default: 
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_41, 0);
lean_inc(x_232);
lean_dec(x_41);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_38);
x_233 = lean_ctor_get(x_40, 1);
lean_inc(x_233);
lean_dec(x_40);
if (lean_is_scalar(x_28)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_28;
}
lean_ctor_set(x_234, 0, x_35);
lean_ctor_set(x_234, 1, x_36);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_31);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_29);
lean_ctor_set(x_237, 1, x_236);
x_16 = x_237;
x_17 = x_233;
goto block_22;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
lean_dec(x_35);
x_238 = lean_ctor_get(x_40, 1);
lean_inc(x_238);
lean_dec(x_40);
x_239 = lean_ctor_get(x_232, 0);
lean_inc(x_239);
lean_dec(x_232);
x_276 = lean_mk_string_unchecked("Debug", 5, 5);
x_277 = lean_mk_string_unchecked("Meta", 4, 4);
x_278 = lean_mk_string_unchecked("Tactic", 6, 6);
x_279 = lean_mk_string_unchecked("simp", 4, 4);
x_280 = l_Lean_Name_mkStr4(x_276, x_277, x_278, x_279);
lean_inc(x_280);
x_281 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_280, x_13, x_238);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_unbox(x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; uint8_t x_285; 
lean_dec(x_280);
lean_dec(x_33);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
lean_dec(x_281);
x_285 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_251 = x_285;
x_252 = x_36;
x_253 = x_10;
x_254 = x_11;
x_255 = x_12;
x_256 = x_13;
x_257 = x_14;
x_258 = x_284;
goto block_275;
}
else
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_281);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_287 = lean_ctor_get(x_281, 1);
x_288 = lean_ctor_get(x_281, 0);
lean_dec(x_288);
x_289 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_290 = l_Lean_stringToMessageData(x_289);
lean_dec(x_289);
x_291 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_281, 7);
lean_ctor_set(x_281, 1, x_291);
lean_ctor_set(x_281, 0, x_290);
x_292 = lean_mk_string_unchecked(" => ", 4, 4);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_281);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_ctor_get(x_239, 0);
lean_inc(x_295);
x_296 = l_Lean_MessageData_ofExpr(x_295);
x_297 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_mk_string_unchecked("", 0, 0);
x_299 = l_Lean_stringToMessageData(x_298);
lean_dec(x_298);
x_300 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_280, x_300, x_11, x_12, x_13, x_14, x_287);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
x_303 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_251 = x_303;
x_252 = x_36;
x_253 = x_10;
x_254 = x_11;
x_255 = x_12;
x_256 = x_13;
x_257 = x_14;
x_258 = x_302;
goto block_275;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_304 = lean_ctor_get(x_281, 1);
lean_inc(x_304);
lean_dec(x_281);
x_305 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_306 = l_Lean_stringToMessageData(x_305);
lean_dec(x_305);
x_307 = l_Lean_MessageData_ofExpr(x_33);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_mk_string_unchecked(" => ", 4, 4);
x_310 = l_Lean_stringToMessageData(x_309);
lean_dec(x_309);
x_311 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_ctor_get(x_239, 0);
lean_inc(x_312);
x_313 = l_Lean_MessageData_ofExpr(x_312);
x_314 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_mk_string_unchecked("", 0, 0);
x_316 = l_Lean_stringToMessageData(x_315);
lean_dec(x_315);
x_317 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_280, x_317, x_11, x_12, x_13, x_14, x_304);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_251 = x_320;
x_252 = x_36;
x_253 = x_10;
x_254 = x_11;
x_255 = x_12;
x_256 = x_13;
x_257 = x_14;
x_258 = x_319;
goto block_275;
}
}
block_250:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_244 = lean_box(x_23);
if (lean_is_scalar(x_28)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_28;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_241);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_242);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_box(x_243);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_29);
lean_ctor_set(x_249, 1, x_248);
x_16 = x_249;
x_17 = x_240;
goto block_22;
}
block_275:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_259, 0, x_38);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_259, sizeof(void*)*1 + 1, x_3);
x_260 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_259, x_253, x_256, x_257, x_258);
lean_dec(x_253);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = lean_ctor_get(x_239, 1);
lean_inc(x_262);
x_263 = l_Lean_Meta_mkEqTrans_x3f(x_252, x_262, x_254, x_255, x_256, x_257, x_261);
if (lean_obj_tag(x_263) == 0)
{
if (x_251 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_ctor_get(x_239, 0);
lean_inc(x_266);
lean_dec(x_239);
x_240 = x_265;
x_241 = x_264;
x_242 = x_266;
x_243 = x_3;
goto block_250;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
lean_dec(x_263);
x_269 = lean_ctor_get(x_239, 0);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_239, sizeof(void*)*2);
lean_dec(x_239);
x_240 = x_268;
x_241 = x_267;
x_242 = x_269;
x_243 = x_270;
goto block_250;
}
}
else
{
uint8_t x_271; 
lean_dec(x_239);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_263);
if (x_271 == 0)
{
return x_263;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_263, 0);
x_273 = lean_ctor_get(x_263, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_263);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
}
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_321 = !lean_is_exclusive(x_40);
if (x_321 == 0)
{
return x_40;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_40, 0);
x_323 = lean_ctor_get(x_40, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_40);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_38);
lean_dec(x_27);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_28;
}
lean_ctor_set(x_325, 0, x_35);
lean_ctor_set(x_325, 1, x_36);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_33);
lean_ctor_set(x_326, 1, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_31);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_29);
lean_ctor_set(x_328, 1, x_327);
x_16 = x_328;
x_17 = x_15;
goto block_22;
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_16;
x_15 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_25 = lean_array_uget(x_4, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_26, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
lean_dec(x_37);
lean_inc(x_1);
x_39 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_1, x_38);
if (x_39 == 0)
{
lean_object* x_40; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_33);
x_40 = l_Lean_Meta_Simp_SimprocEntry_try(x_26, x_27, x_33, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; 
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
switch (lean_obj_tag(x_41)) {
case 0:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_95 = lean_mk_string_unchecked("Debug", 5, 5);
x_96 = lean_mk_string_unchecked("Meta", 4, 4);
x_97 = lean_mk_string_unchecked("Tactic", 6, 6);
x_98 = lean_mk_string_unchecked("simp", 4, 4);
x_99 = l_Lean_Name_mkStr4(x_95, x_96, x_97, x_98);
lean_inc(x_99);
x_100 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_99, x_13, x_42);
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; 
lean_dec(x_99);
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_45 = x_10;
x_46 = x_11;
x_47 = x_12;
x_48 = x_13;
x_49 = x_14;
x_50 = x_103;
goto block_94;
}
else
{
uint8_t x_104; 
x_104 = !lean_is_exclusive(x_100);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_105 = lean_ctor_get(x_100, 1);
x_106 = lean_ctor_get(x_100, 0);
lean_dec(x_106);
x_107 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
lean_inc(x_33);
x_109 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_100, 7);
lean_ctor_set(x_100, 1, x_109);
lean_ctor_set(x_100, 0, x_108);
x_110 = lean_mk_string_unchecked(" => ", 4, 4);
x_111 = l_Lean_stringToMessageData(x_110);
lean_dec(x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_100);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_ctor_get(x_43, 0);
lean_inc(x_113);
x_114 = l_Lean_MessageData_ofExpr(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = lean_mk_string_unchecked("", 0, 0);
x_117 = l_Lean_stringToMessageData(x_116);
lean_dec(x_116);
x_118 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_118, 0, x_115);
lean_ctor_set(x_118, 1, x_117);
x_119 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_99, x_118, x_11, x_12, x_13, x_14, x_105);
x_120 = lean_ctor_get(x_119, 1);
lean_inc(x_120);
lean_dec(x_119);
x_45 = x_10;
x_46 = x_11;
x_47 = x_12;
x_48 = x_13;
x_49 = x_14;
x_50 = x_120;
goto block_94;
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_121 = lean_ctor_get(x_100, 1);
lean_inc(x_121);
lean_dec(x_100);
x_122 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
lean_inc(x_33);
x_124 = l_Lean_MessageData_ofExpr(x_33);
x_125 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_mk_string_unchecked(" => ", 4, 4);
x_127 = l_Lean_stringToMessageData(x_126);
lean_dec(x_126);
x_128 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_127);
x_129 = lean_ctor_get(x_43, 0);
lean_inc(x_129);
x_130 = l_Lean_MessageData_ofExpr(x_129);
x_131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_131, 0, x_128);
lean_ctor_set(x_131, 1, x_130);
x_132 = lean_mk_string_unchecked("", 0, 0);
x_133 = l_Lean_stringToMessageData(x_132);
lean_dec(x_132);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_133);
x_135 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_99, x_134, x_11, x_12, x_13, x_14, x_121);
x_136 = lean_ctor_get(x_135, 1);
lean_inc(x_136);
lean_dec(x_135);
x_45 = x_10;
x_46 = x_11;
x_47 = x_12;
x_48 = x_13;
x_49 = x_14;
x_50 = x_136;
goto block_94;
}
}
block_94:
{
lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_51 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_51, 0, x_38);
lean_ctor_set_uint8(x_51, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_51, sizeof(void*)*1 + 1, x_3);
x_52 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_51, x_45, x_48, x_49, x_50);
lean_dec(x_45);
x_53 = !lean_is_exclusive(x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; uint8_t x_56; lean_object* x_57; 
x_54 = lean_ctor_get(x_52, 1);
x_55 = lean_ctor_get(x_52, 0);
lean_dec(x_55);
x_56 = lean_unbox(x_31);
lean_inc(x_36);
x_57 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_56, x_43, x_46, x_47, x_48, x_49, x_54);
if (lean_obj_tag(x_57) == 0)
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_57);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_57, 0);
if (lean_is_scalar(x_44)) {
 x_60 = lean_alloc_ctor(0, 1, 0);
} else {
 x_60 = x_44;
}
lean_ctor_set(x_60, 0, x_59);
x_61 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_52, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_28;
}
lean_ctor_set(x_62, 0, x_33);
lean_ctor_set(x_62, 1, x_52);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_31);
lean_ctor_set(x_63, 1, x_62);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_61);
lean_ctor_set(x_64, 1, x_63);
lean_ctor_set(x_57, 0, x_64);
return x_57;
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_65 = lean_ctor_get(x_57, 0);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_57);
if (lean_is_scalar(x_44)) {
 x_67 = lean_alloc_ctor(0, 1, 0);
} else {
 x_67 = x_44;
}
lean_ctor_set(x_67, 0, x_65);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_52, 1, x_36);
lean_ctor_set(x_52, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_69 = lean_alloc_ctor(0, 2, 0);
} else {
 x_69 = x_28;
}
lean_ctor_set(x_69, 0, x_33);
lean_ctor_set(x_69, 1, x_52);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_31);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
}
else
{
uint8_t x_73; 
lean_free_object(x_52);
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_73 = !lean_is_exclusive(x_57);
if (x_73 == 0)
{
return x_57;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_57, 0);
x_75 = lean_ctor_get(x_57, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_57);
x_76 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
return x_76;
}
}
}
else
{
lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_52, 1);
lean_inc(x_77);
lean_dec(x_52);
x_78 = lean_unbox(x_31);
lean_inc(x_36);
x_79 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_78, x_43, x_46, x_47, x_48, x_49, x_77);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_79, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_82 = x_79;
} else {
 lean_dec_ref(x_79);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_44)) {
 x_83 = lean_alloc_ctor(0, 1, 0);
} else {
 x_83 = x_44;
}
lean_ctor_set(x_83, 0, x_80);
x_84 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_84, 0, x_83);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_35);
lean_ctor_set(x_85, 1, x_36);
if (lean_is_scalar(x_28)) {
 x_86 = lean_alloc_ctor(0, 2, 0);
} else {
 x_86 = x_28;
}
lean_ctor_set(x_86, 0, x_33);
lean_ctor_set(x_86, 1, x_85);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_31);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_84);
lean_ctor_set(x_88, 1, x_87);
if (lean_is_scalar(x_82)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_82;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_81);
return x_89;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_44);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_90 = lean_ctor_get(x_79, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_79, 1);
lean_inc(x_91);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_92 = x_79;
} else {
 lean_dec_ref(x_79);
 x_92 = lean_box(0);
}
if (lean_is_scalar(x_92)) {
 x_93 = lean_alloc_ctor(1, 2, 0);
} else {
 x_93 = x_92;
}
lean_ctor_set(x_93, 0, x_90);
lean_ctor_set(x_93, 1, x_91);
return x_93;
}
}
}
}
case 1:
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_137 = lean_ctor_get(x_40, 1);
lean_inc(x_137);
lean_dec(x_40);
x_138 = lean_ctor_get(x_41, 0);
lean_inc(x_138);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 x_139 = x_41;
} else {
 lean_dec_ref(x_41);
 x_139 = lean_box(0);
}
x_190 = lean_mk_string_unchecked("Debug", 5, 5);
x_191 = lean_mk_string_unchecked("Meta", 4, 4);
x_192 = lean_mk_string_unchecked("Tactic", 6, 6);
x_193 = lean_mk_string_unchecked("simp", 4, 4);
x_194 = l_Lean_Name_mkStr4(x_190, x_191, x_192, x_193);
lean_inc(x_194);
x_195 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_194, x_13, x_137);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_unbox(x_196);
lean_dec(x_196);
if (x_197 == 0)
{
lean_object* x_198; 
lean_dec(x_194);
x_198 = lean_ctor_get(x_195, 1);
lean_inc(x_198);
lean_dec(x_195);
x_140 = x_10;
x_141 = x_11;
x_142 = x_12;
x_143 = x_13;
x_144 = x_14;
x_145 = x_198;
goto block_189;
}
else
{
uint8_t x_199; 
x_199 = !lean_is_exclusive(x_195);
if (x_199 == 0)
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_200 = lean_ctor_get(x_195, 1);
x_201 = lean_ctor_get(x_195, 0);
lean_dec(x_201);
x_202 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_203 = l_Lean_stringToMessageData(x_202);
lean_dec(x_202);
lean_inc(x_33);
x_204 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_195, 7);
lean_ctor_set(x_195, 1, x_204);
lean_ctor_set(x_195, 0, x_203);
x_205 = lean_mk_string_unchecked(" => ", 4, 4);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_195);
lean_ctor_set(x_207, 1, x_206);
x_208 = lean_ctor_get(x_138, 0);
lean_inc(x_208);
x_209 = l_Lean_MessageData_ofExpr(x_208);
x_210 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_210, 0, x_207);
lean_ctor_set(x_210, 1, x_209);
x_211 = lean_mk_string_unchecked("", 0, 0);
x_212 = l_Lean_stringToMessageData(x_211);
lean_dec(x_211);
x_213 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_212);
x_214 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_194, x_213, x_11, x_12, x_13, x_14, x_200);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
x_140 = x_10;
x_141 = x_11;
x_142 = x_12;
x_143 = x_13;
x_144 = x_14;
x_145 = x_215;
goto block_189;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_216 = lean_ctor_get(x_195, 1);
lean_inc(x_216);
lean_dec(x_195);
x_217 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_218 = l_Lean_stringToMessageData(x_217);
lean_dec(x_217);
lean_inc(x_33);
x_219 = l_Lean_MessageData_ofExpr(x_33);
x_220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_220, 0, x_218);
lean_ctor_set(x_220, 1, x_219);
x_221 = lean_mk_string_unchecked(" => ", 4, 4);
x_222 = l_Lean_stringToMessageData(x_221);
lean_dec(x_221);
x_223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_223, 0, x_220);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_ctor_get(x_138, 0);
lean_inc(x_224);
x_225 = l_Lean_MessageData_ofExpr(x_224);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_223);
lean_ctor_set(x_226, 1, x_225);
x_227 = lean_mk_string_unchecked("", 0, 0);
x_228 = l_Lean_stringToMessageData(x_227);
lean_dec(x_227);
x_229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_228);
x_230 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_194, x_229, x_11, x_12, x_13, x_14, x_216);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_140 = x_10;
x_141 = x_11;
x_142 = x_12;
x_143 = x_13;
x_144 = x_14;
x_145 = x_231;
goto block_189;
}
}
block_189:
{
lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_146 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_146, 0, x_38);
lean_ctor_set_uint8(x_146, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_146, sizeof(void*)*1 + 1, x_3);
x_147 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_146, x_140, x_143, x_144, x_145);
lean_dec(x_140);
x_148 = !lean_is_exclusive(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; lean_object* x_152; 
x_149 = lean_ctor_get(x_147, 1);
x_150 = lean_ctor_get(x_147, 0);
lean_dec(x_150);
x_151 = lean_unbox(x_31);
lean_inc(x_36);
x_152 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_151, x_138, x_141, x_142, x_143, x_144, x_149);
if (lean_obj_tag(x_152) == 0)
{
uint8_t x_153; 
x_153 = !lean_is_exclusive(x_152);
if (x_153 == 0)
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
x_154 = lean_ctor_get(x_152, 0);
if (lean_is_scalar(x_139)) {
 x_155 = lean_alloc_ctor(1, 1, 0);
} else {
 x_155 = x_139;
}
lean_ctor_set(x_155, 0, x_154);
x_156 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_156, 0, x_155);
lean_ctor_set(x_147, 1, x_36);
lean_ctor_set(x_147, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_28;
}
lean_ctor_set(x_157, 0, x_33);
lean_ctor_set(x_157, 1, x_147);
x_158 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_158, 0, x_31);
lean_ctor_set(x_158, 1, x_157);
x_159 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
lean_ctor_set(x_152, 0, x_159);
return x_152;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; 
x_160 = lean_ctor_get(x_152, 0);
x_161 = lean_ctor_get(x_152, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_152);
if (lean_is_scalar(x_139)) {
 x_162 = lean_alloc_ctor(1, 1, 0);
} else {
 x_162 = x_139;
}
lean_ctor_set(x_162, 0, x_160);
x_163 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_147, 1, x_36);
lean_ctor_set(x_147, 0, x_35);
if (lean_is_scalar(x_28)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_28;
}
lean_ctor_set(x_164, 0, x_33);
lean_ctor_set(x_164, 1, x_147);
x_165 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_165, 0, x_31);
lean_ctor_set(x_165, 1, x_164);
x_166 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_166, 0, x_163);
lean_ctor_set(x_166, 1, x_165);
x_167 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_167, 0, x_166);
lean_ctor_set(x_167, 1, x_161);
return x_167;
}
}
else
{
uint8_t x_168; 
lean_free_object(x_147);
lean_dec(x_139);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_168 = !lean_is_exclusive(x_152);
if (x_168 == 0)
{
return x_152;
}
else
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; 
x_169 = lean_ctor_get(x_152, 0);
x_170 = lean_ctor_get(x_152, 1);
lean_inc(x_170);
lean_inc(x_169);
lean_dec(x_152);
x_171 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_171, 0, x_169);
lean_ctor_set(x_171, 1, x_170);
return x_171;
}
}
}
else
{
lean_object* x_172; uint8_t x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_147, 1);
lean_inc(x_172);
lean_dec(x_147);
x_173 = lean_unbox(x_31);
lean_inc(x_36);
x_174 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_36, x_173, x_138, x_141, x_142, x_143, x_144, x_172);
if (lean_obj_tag(x_174) == 0)
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_175 = lean_ctor_get(x_174, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_174, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_177 = x_174;
} else {
 lean_dec_ref(x_174);
 x_177 = lean_box(0);
}
if (lean_is_scalar(x_139)) {
 x_178 = lean_alloc_ctor(1, 1, 0);
} else {
 x_178 = x_139;
}
lean_ctor_set(x_178, 0, x_175);
x_179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_179, 0, x_178);
x_180 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_180, 0, x_35);
lean_ctor_set(x_180, 1, x_36);
if (lean_is_scalar(x_28)) {
 x_181 = lean_alloc_ctor(0, 2, 0);
} else {
 x_181 = x_28;
}
lean_ctor_set(x_181, 0, x_33);
lean_ctor_set(x_181, 1, x_180);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_31);
lean_ctor_set(x_182, 1, x_181);
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_179);
lean_ctor_set(x_183, 1, x_182);
if (lean_is_scalar(x_177)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_177;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_176);
return x_184;
}
else
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
lean_dec(x_139);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
x_185 = lean_ctor_get(x_174, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_174, 1);
lean_inc(x_186);
if (lean_is_exclusive(x_174)) {
 lean_ctor_release(x_174, 0);
 lean_ctor_release(x_174, 1);
 x_187 = x_174;
} else {
 lean_dec_ref(x_174);
 x_187 = lean_box(0);
}
if (lean_is_scalar(x_187)) {
 x_188 = lean_alloc_ctor(1, 2, 0);
} else {
 x_188 = x_187;
}
lean_ctor_set(x_188, 0, x_185);
lean_ctor_set(x_188, 1, x_186);
return x_188;
}
}
}
}
default: 
{
lean_object* x_232; 
x_232 = lean_ctor_get(x_41, 0);
lean_inc(x_232);
lean_dec(x_41);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_38);
x_233 = lean_ctor_get(x_40, 1);
lean_inc(x_233);
lean_dec(x_40);
if (lean_is_scalar(x_28)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_28;
}
lean_ctor_set(x_234, 0, x_35);
lean_ctor_set(x_234, 1, x_36);
x_235 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_235, 0, x_33);
lean_ctor_set(x_235, 1, x_234);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_31);
lean_ctor_set(x_236, 1, x_235);
x_237 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_237, 0, x_29);
lean_ctor_set(x_237, 1, x_236);
x_16 = x_237;
x_17 = x_233;
goto block_22;
}
else
{
lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; uint8_t x_243; uint8_t x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; uint8_t x_283; 
lean_dec(x_35);
x_238 = lean_ctor_get(x_40, 1);
lean_inc(x_238);
lean_dec(x_40);
x_239 = lean_ctor_get(x_232, 0);
lean_inc(x_239);
lean_dec(x_232);
x_276 = lean_mk_string_unchecked("Debug", 5, 5);
x_277 = lean_mk_string_unchecked("Meta", 4, 4);
x_278 = lean_mk_string_unchecked("Tactic", 6, 6);
x_279 = lean_mk_string_unchecked("simp", 4, 4);
x_280 = l_Lean_Name_mkStr4(x_276, x_277, x_278, x_279);
lean_inc(x_280);
x_281 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_280, x_13, x_238);
x_282 = lean_ctor_get(x_281, 0);
lean_inc(x_282);
x_283 = lean_unbox(x_282);
lean_dec(x_282);
if (x_283 == 0)
{
lean_object* x_284; uint8_t x_285; 
lean_dec(x_280);
lean_dec(x_33);
x_284 = lean_ctor_get(x_281, 1);
lean_inc(x_284);
lean_dec(x_281);
x_285 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_251 = x_285;
x_252 = x_36;
x_253 = x_10;
x_254 = x_11;
x_255 = x_12;
x_256 = x_13;
x_257 = x_14;
x_258 = x_284;
goto block_275;
}
else
{
uint8_t x_286; 
x_286 = !lean_is_exclusive(x_281);
if (x_286 == 0)
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; uint8_t x_303; 
x_287 = lean_ctor_get(x_281, 1);
x_288 = lean_ctor_get(x_281, 0);
lean_dec(x_288);
x_289 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_290 = l_Lean_stringToMessageData(x_289);
lean_dec(x_289);
x_291 = l_Lean_MessageData_ofExpr(x_33);
lean_ctor_set_tag(x_281, 7);
lean_ctor_set(x_281, 1, x_291);
lean_ctor_set(x_281, 0, x_290);
x_292 = lean_mk_string_unchecked(" => ", 4, 4);
x_293 = l_Lean_stringToMessageData(x_292);
lean_dec(x_292);
x_294 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_294, 0, x_281);
lean_ctor_set(x_294, 1, x_293);
x_295 = lean_ctor_get(x_239, 0);
lean_inc(x_295);
x_296 = l_Lean_MessageData_ofExpr(x_295);
x_297 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_297, 0, x_294);
lean_ctor_set(x_297, 1, x_296);
x_298 = lean_mk_string_unchecked("", 0, 0);
x_299 = l_Lean_stringToMessageData(x_298);
lean_dec(x_298);
x_300 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_299);
x_301 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_280, x_300, x_11, x_12, x_13, x_14, x_287);
x_302 = lean_ctor_get(x_301, 1);
lean_inc(x_302);
lean_dec(x_301);
x_303 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_251 = x_303;
x_252 = x_36;
x_253 = x_10;
x_254 = x_11;
x_255 = x_12;
x_256 = x_13;
x_257 = x_14;
x_258 = x_302;
goto block_275;
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_304 = lean_ctor_get(x_281, 1);
lean_inc(x_304);
lean_dec(x_281);
x_305 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_306 = l_Lean_stringToMessageData(x_305);
lean_dec(x_305);
x_307 = l_Lean_MessageData_ofExpr(x_33);
x_308 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_308, 0, x_306);
lean_ctor_set(x_308, 1, x_307);
x_309 = lean_mk_string_unchecked(" => ", 4, 4);
x_310 = l_Lean_stringToMessageData(x_309);
lean_dec(x_309);
x_311 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_310);
x_312 = lean_ctor_get(x_239, 0);
lean_inc(x_312);
x_313 = l_Lean_MessageData_ofExpr(x_312);
x_314 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_314, 0, x_311);
lean_ctor_set(x_314, 1, x_313);
x_315 = lean_mk_string_unchecked("", 0, 0);
x_316 = l_Lean_stringToMessageData(x_315);
lean_dec(x_315);
x_317 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_317, 0, x_314);
lean_ctor_set(x_317, 1, x_316);
x_318 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_280, x_317, x_11, x_12, x_13, x_14, x_304);
x_319 = lean_ctor_get(x_318, 1);
lean_inc(x_319);
lean_dec(x_318);
x_320 = lean_unbox(x_31);
lean_dec(x_31);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_251 = x_320;
x_252 = x_36;
x_253 = x_10;
x_254 = x_11;
x_255 = x_12;
x_256 = x_13;
x_257 = x_14;
x_258 = x_319;
goto block_275;
}
}
block_250:
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_244 = lean_box(x_23);
if (lean_is_scalar(x_28)) {
 x_245 = lean_alloc_ctor(0, 2, 0);
} else {
 x_245 = x_28;
}
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_240);
x_246 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_246, 0, x_241);
lean_ctor_set(x_246, 1, x_245);
x_247 = lean_box(x_243);
x_248 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_248, 0, x_247);
lean_ctor_set(x_248, 1, x_246);
x_249 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_249, 0, x_29);
lean_ctor_set(x_249, 1, x_248);
x_16 = x_249;
x_17 = x_242;
goto block_22;
}
block_275:
{
lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; 
x_259 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_259, 0, x_38);
lean_ctor_set_uint8(x_259, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_259, sizeof(void*)*1 + 1, x_3);
x_260 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_259, x_253, x_256, x_257, x_258);
lean_dec(x_253);
x_261 = lean_ctor_get(x_260, 1);
lean_inc(x_261);
lean_dec(x_260);
x_262 = lean_ctor_get(x_239, 1);
lean_inc(x_262);
x_263 = l_Lean_Meta_mkEqTrans_x3f(x_252, x_262, x_254, x_255, x_256, x_257, x_261);
if (lean_obj_tag(x_263) == 0)
{
if (x_251 == 0)
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_ctor_get(x_239, 0);
lean_inc(x_266);
lean_dec(x_239);
x_240 = x_264;
x_241 = x_266;
x_242 = x_265;
x_243 = x_3;
goto block_250;
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; uint8_t x_270; 
x_267 = lean_ctor_get(x_263, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_263, 1);
lean_inc(x_268);
lean_dec(x_263);
x_269 = lean_ctor_get(x_239, 0);
lean_inc(x_269);
x_270 = lean_ctor_get_uint8(x_239, sizeof(void*)*2);
lean_dec(x_239);
x_240 = x_267;
x_241 = x_269;
x_242 = x_268;
x_243 = x_270;
goto block_250;
}
}
else
{
uint8_t x_271; 
lean_dec(x_239);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_271 = !lean_is_exclusive(x_263);
if (x_271 == 0)
{
return x_263;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
x_272 = lean_ctor_get(x_263, 0);
x_273 = lean_ctor_get(x_263, 1);
lean_inc(x_273);
lean_inc(x_272);
lean_dec(x_263);
x_274 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_274, 0, x_272);
lean_ctor_set(x_274, 1, x_273);
return x_274;
}
}
}
}
}
}
}
else
{
uint8_t x_321; 
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_321 = !lean_is_exclusive(x_40);
if (x_321 == 0)
{
return x_40;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_40, 0);
x_323 = lean_ctor_get(x_40, 1);
lean_inc(x_323);
lean_inc(x_322);
lean_dec(x_40);
x_324 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_324, 0, x_322);
lean_ctor_set(x_324, 1, x_323);
return x_324;
}
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_38);
lean_dec(x_27);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_325 = lean_alloc_ctor(0, 2, 0);
} else {
 x_325 = x_28;
}
lean_ctor_set(x_325, 0, x_35);
lean_ctor_set(x_325, 1, x_36);
x_326 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_326, 0, x_33);
lean_ctor_set(x_326, 1, x_325);
x_327 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_327, 0, x_31);
lean_ctor_set(x_327, 1, x_326);
x_328 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_328, 0, x_29);
lean_ctor_set(x_328, 1, x_327);
x_16 = x_328;
x_17 = x_15;
goto block_22;
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_6, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_20, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_61; lean_object* x_62; lean_object* x_122; lean_object* x_123; uint64_t x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; uint8_t x_133; lean_object* x_134; lean_object* x_135; 
x_122 = lean_ctor_get(x_6, 4);
lean_inc(x_122);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get_uint64(x_122, sizeof(void*)*1);
lean_dec(x_122);
x_125 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_126 = lean_ctor_get(x_8, 1);
lean_inc(x_126);
x_127 = lean_ctor_get(x_8, 2);
lean_inc(x_127);
x_128 = lean_ctor_get(x_8, 3);
lean_inc(x_128);
x_129 = lean_ctor_get(x_8, 4);
lean_inc(x_129);
x_130 = lean_ctor_get(x_8, 5);
lean_inc(x_130);
x_131 = lean_ctor_get(x_8, 6);
lean_inc(x_131);
x_132 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_133 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
x_134 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_134, 0, x_123);
lean_ctor_set(x_134, 1, x_126);
lean_ctor_set(x_134, 2, x_127);
lean_ctor_set(x_134, 3, x_128);
lean_ctor_set(x_134, 4, x_129);
lean_ctor_set(x_134, 5, x_130);
lean_ctor_set(x_134, 6, x_131);
lean_ctor_set_uint64(x_134, sizeof(void*)*7, x_124);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 8, x_125);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 9, x_132);
lean_ctor_set_uint8(x_134, sizeof(void*)*7 + 10, x_133);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_135 = l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_box(0), x_2, x_4, x_134, x_9, x_10, x_11, x_12);
lean_dec(x_134);
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_136; lean_object* x_137; 
x_136 = lean_ctor_get(x_135, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_135, 1);
lean_inc(x_137);
lean_dec(x_135);
x_61 = x_136;
x_62 = x_137;
goto block_121;
}
else
{
if (lean_obj_tag(x_135) == 0)
{
lean_object* x_138; lean_object* x_139; 
x_138 = lean_ctor_get(x_135, 0);
lean_inc(x_138);
x_139 = lean_ctor_get(x_135, 1);
lean_inc(x_139);
lean_dec(x_135);
x_61 = x_138;
x_62 = x_139;
goto block_121;
}
else
{
uint8_t x_140; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_140 = !lean_is_exclusive(x_135);
if (x_140 == 0)
{
return x_135;
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_135, 0);
x_142 = lean_ctor_get(x_135, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_135);
x_143 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_143, 0, x_141);
lean_ctor_set(x_143, 1, x_142);
return x_143;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_60:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_mk_string_unchecked("Debug", 5, 5);
x_21 = lean_mk_string_unchecked("Meta", 4, 4);
x_22 = lean_mk_string_unchecked("Tactic", 6, 6);
x_23 = lean_mk_string_unchecked("simp", 4, 4);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
lean_inc(x_24);
x_25 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_24, x_10, x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_13 = x_28;
goto block_17;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_mk_string_unchecked("no ", 3, 3);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = l_Lean_stringToMessageData(x_19);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_34);
lean_ctor_set(x_25, 0, x_33);
x_35 = lean_mk_string_unchecked("-simprocs found for ", 20, 20);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofExpr(x_4);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_24, x_42, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_13 = x_44;
goto block_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_mk_string_unchecked("no ", 3, 3);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = l_Lean_stringToMessageData(x_19);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("-simprocs found for ", 20, 20);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_MessageData_ofExpr(x_4);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("", 0, 0);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_24, x_57, x_8, x_9, x_10, x_11, x_45);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_13 = x_59;
goto block_17;
}
}
}
block_121:
{
uint8_t x_63; 
x_63 = l_Array_isEmpty___redArg(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; size_t x_72; lean_object* x_73; size_t x_74; lean_object* x_75; 
x_64 = lean_box(0);
x_65 = lean_box(1);
x_66 = lean_box(0);
x_67 = lean_box(x_63);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_64);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_4);
lean_ctor_set(x_69, 1, x_68);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_65);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_66);
lean_ctor_set(x_71, 1, x_70);
x_72 = lean_array_size(x_61);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_usize_of_nat(x_73);
x_75 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0(x_3, x_1, x_63, x_61, x_72, x_74, x_71, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
lean_dec(x_61);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_76, 1);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 1);
lean_inc(x_78);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_76, 0);
lean_inc(x_80);
lean_dec(x_76);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; uint8_t x_82; 
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_unbox(x_81);
lean_dec(x_81);
if (x_82 == 0)
{
uint8_t x_83; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_83 = !lean_is_exclusive(x_75);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_75, 0);
lean_dec(x_84);
x_85 = lean_box(0);
x_86 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_86, 0, x_85);
lean_ctor_set(x_75, 0, x_86);
return x_75;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
lean_dec(x_75);
x_88 = lean_box(0);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_87);
return x_90;
}
}
else
{
uint8_t x_91; 
x_91 = !lean_is_exclusive(x_75);
if (x_91 == 0)
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; uint8_t x_97; lean_object* x_98; lean_object* x_99; 
x_92 = lean_ctor_get(x_75, 0);
lean_dec(x_92);
x_93 = lean_ctor_get(x_77, 0);
lean_inc(x_93);
lean_dec(x_77);
x_94 = lean_ctor_get(x_78, 0);
lean_inc(x_94);
lean_dec(x_78);
x_95 = lean_ctor_get(x_79, 1);
lean_inc(x_95);
lean_dec(x_79);
x_96 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_96, 0, x_94);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_unbox(x_93);
lean_dec(x_93);
lean_ctor_set_uint8(x_96, sizeof(void*)*2, x_97);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_96);
x_99 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_75, 0, x_99);
return x_75;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_100 = lean_ctor_get(x_75, 1);
lean_inc(x_100);
lean_dec(x_75);
x_101 = lean_ctor_get(x_77, 0);
lean_inc(x_101);
lean_dec(x_77);
x_102 = lean_ctor_get(x_78, 0);
lean_inc(x_102);
lean_dec(x_78);
x_103 = lean_ctor_get(x_79, 1);
lean_inc(x_103);
lean_dec(x_79);
x_104 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
x_105 = lean_unbox(x_101);
lean_dec(x_101);
lean_ctor_set_uint8(x_104, sizeof(void*)*2, x_105);
x_106 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_106, 0, x_104);
x_107 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_107, 0, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_100);
return x_108;
}
}
}
else
{
uint8_t x_109; 
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
x_109 = !lean_is_exclusive(x_75);
if (x_109 == 0)
{
lean_object* x_110; lean_object* x_111; 
x_110 = lean_ctor_get(x_75, 0);
lean_dec(x_110);
x_111 = lean_ctor_get(x_80, 0);
lean_inc(x_111);
lean_dec(x_80);
lean_ctor_set(x_75, 0, x_111);
return x_75;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_112 = lean_ctor_get(x_75, 1);
lean_inc(x_112);
lean_dec(x_75);
x_113 = lean_ctor_get(x_80, 0);
lean_inc(x_113);
lean_dec(x_80);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_113);
lean_ctor_set(x_114, 1, x_112);
return x_114;
}
}
}
else
{
uint8_t x_115; 
x_115 = !lean_is_exclusive(x_75);
if (x_115 == 0)
{
return x_75;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_75, 0);
x_117 = lean_ctor_get(x_75, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_75);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (x_1 == 0)
{
lean_object* x_119; 
x_119 = lean_mk_string_unchecked("pre", 3, 3);
x_18 = x_62;
x_19 = x_119;
goto block_60;
}
else
{
lean_object* x_120; 
x_120 = lean_mk_string_unchecked("post", 4, 4);
x_18 = x_62;
x_19 = x_120;
goto block_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0_spec__0(x_1, x_16, x_17, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocCore_spec__0(x_1, x_16, x_17, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_simprocCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_array_uget(x_4, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_1);
x_35 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_31);
x_36 = l_Lean_Meta_Simp_SimprocEntry_tryD(x_26, x_27, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
switch (lean_obj_tag(x_37)) {
case 0:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_73 = lean_ctor_get(x_37, 0);
lean_inc(x_73);
x_74 = lean_mk_string_unchecked("Debug", 5, 5);
x_75 = lean_mk_string_unchecked("Meta", 4, 4);
x_76 = lean_mk_string_unchecked("Tactic", 6, 6);
x_77 = lean_mk_string_unchecked("simp", 4, 4);
x_78 = l_Lean_Name_mkStr4(x_74, x_75, x_76, x_77);
lean_inc(x_78);
x_79 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_78, x_13, x_38);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_11);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_39 = x_10;
x_40 = x_13;
x_41 = x_14;
x_42 = x_82;
goto block_55;
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_84 = lean_ctor_get(x_79, 1);
x_85 = lean_ctor_get(x_79, 0);
lean_dec(x_85);
x_86 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
lean_inc(x_31);
x_88 = l_Lean_MessageData_ofExpr(x_31);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_88);
lean_ctor_set(x_79, 0, x_87);
x_89 = lean_mk_string_unchecked(" => ", 4, 4);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_73);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_78, x_96, x_11, x_12, x_13, x_14, x_84);
lean_dec(x_12);
lean_dec(x_11);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_39 = x_10;
x_40 = x_13;
x_41 = x_14;
x_42 = x_98;
goto block_55;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_99 = lean_ctor_get(x_79, 1);
lean_inc(x_99);
lean_dec(x_79);
x_100 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_101 = l_Lean_stringToMessageData(x_100);
lean_dec(x_100);
lean_inc(x_31);
x_102 = l_Lean_MessageData_ofExpr(x_31);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked(" => ", 4, 4);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_MessageData_ofExpr(x_73);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("", 0, 0);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_78, x_111, x_11, x_12, x_13, x_14, x_99);
lean_dec(x_12);
lean_dec(x_11);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_39 = x_10;
x_40 = x_13;
x_41 = x_14;
x_42 = x_113;
goto block_55;
}
}
}
case 1:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_114 = lean_ctor_get(x_37, 0);
lean_inc(x_114);
x_115 = lean_mk_string_unchecked("Debug", 5, 5);
x_116 = lean_mk_string_unchecked("Meta", 4, 4);
x_117 = lean_mk_string_unchecked("Tactic", 6, 6);
x_118 = lean_mk_string_unchecked("simp", 4, 4);
x_119 = l_Lean_Name_mkStr4(x_115, x_116, x_117, x_118);
lean_inc(x_119);
x_120 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_119, x_13, x_38);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_119);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_11);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_56 = x_10;
x_57 = x_13;
x_58 = x_14;
x_59 = x_123;
goto block_72;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_120);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_ctor_get(x_120, 1);
x_126 = lean_ctor_get(x_120, 0);
lean_dec(x_126);
x_127 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_128 = l_Lean_stringToMessageData(x_127);
lean_dec(x_127);
lean_inc(x_31);
x_129 = l_Lean_MessageData_ofExpr(x_31);
lean_ctor_set_tag(x_120, 7);
lean_ctor_set(x_120, 1, x_129);
lean_ctor_set(x_120, 0, x_128);
x_130 = lean_mk_string_unchecked(" => ", 4, 4);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_120);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_MessageData_ofExpr(x_114);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("", 0, 0);
x_136 = l_Lean_stringToMessageData(x_135);
lean_dec(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_119, x_137, x_11, x_12, x_13, x_14, x_125);
lean_dec(x_12);
lean_dec(x_11);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_56 = x_10;
x_57 = x_13;
x_58 = x_14;
x_59 = x_139;
goto block_72;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_140 = lean_ctor_get(x_120, 1);
lean_inc(x_140);
lean_dec(x_120);
x_141 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
lean_inc(x_31);
x_143 = l_Lean_MessageData_ofExpr(x_31);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked(" => ", 4, 4);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_MessageData_ofExpr(x_114);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked("", 0, 0);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_119, x_152, x_11, x_12, x_13, x_14, x_140);
lean_dec(x_12);
lean_dec(x_11);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_56 = x_10;
x_57 = x_13;
x_58 = x_14;
x_59 = x_154;
goto block_72;
}
}
}
default: 
{
lean_object* x_155; 
lean_dec(x_28);
x_155 = lean_ctor_get(x_37, 0);
lean_inc(x_155);
lean_dec(x_37);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_34);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_31);
lean_ctor_set(x_156, 1, x_32);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_29);
lean_ctor_set(x_157, 1, x_156);
x_16 = x_157;
x_17 = x_38;
goto block_22;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_32);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
lean_dec(x_155);
x_175 = lean_mk_string_unchecked("Debug", 5, 5);
x_176 = lean_mk_string_unchecked("Meta", 4, 4);
x_177 = lean_mk_string_unchecked("Tactic", 6, 6);
x_178 = lean_mk_string_unchecked("simp", 4, 4);
x_179 = l_Lean_Name_mkStr4(x_175, x_176, x_177, x_178);
lean_inc(x_179);
x_180 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_179, x_13, x_38);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_179);
lean_dec(x_31);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
x_159 = x_10;
x_160 = x_13;
x_161 = x_14;
x_162 = x_183;
goto block_174;
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_180);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_185 = lean_ctor_get(x_180, 1);
x_186 = lean_ctor_get(x_180, 0);
lean_dec(x_186);
x_187 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = l_Lean_MessageData_ofExpr(x_31);
lean_ctor_set_tag(x_180, 7);
lean_ctor_set(x_180, 1, x_189);
lean_ctor_set(x_180, 0, x_188);
x_190 = lean_mk_string_unchecked(" => ", 4, 4);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_158);
x_193 = l_Lean_MessageData_ofExpr(x_158);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_mk_string_unchecked("", 0, 0);
x_196 = l_Lean_stringToMessageData(x_195);
lean_dec(x_195);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_179, x_197, x_11, x_12, x_13, x_14, x_185);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
x_159 = x_10;
x_160 = x_13;
x_161 = x_14;
x_162 = x_199;
goto block_174;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_200 = lean_ctor_get(x_180, 1);
lean_inc(x_200);
lean_dec(x_180);
x_201 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
x_203 = l_Lean_MessageData_ofExpr(x_31);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_mk_string_unchecked(" => ", 4, 4);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_206);
lean_inc(x_158);
x_208 = l_Lean_MessageData_ofExpr(x_158);
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_mk_string_unchecked("", 0, 0);
x_211 = l_Lean_stringToMessageData(x_210);
lean_dec(x_210);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_179, x_212, x_11, x_12, x_13, x_14, x_200);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
x_159 = x_10;
x_160 = x_13;
x_161 = x_14;
x_162 = x_214;
goto block_174;
}
}
block_174:
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_163, 0, x_34);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_163, sizeof(void*)*1 + 1, x_3);
x_164 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_163, x_159, x_160, x_161, x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_164, 1);
x_167 = lean_ctor_get(x_164, 0);
lean_dec(x_167);
x_168 = lean_box(x_23);
lean_ctor_set(x_164, 1, x_168);
lean_ctor_set(x_164, 0, x_158);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_29);
lean_ctor_set(x_169, 1, x_164);
x_16 = x_169;
x_17 = x_166;
goto block_22;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
lean_dec(x_164);
x_171 = lean_box(x_23);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_158);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_29);
lean_ctor_set(x_173, 1, x_172);
x_16 = x_173;
x_17 = x_170;
goto block_22;
}
}
}
}
}
block_55:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 1, x_3);
x_44 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_43, x_39, x_40, x_41, x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_37);
if (lean_is_scalar(x_28)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_28;
}
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_32);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_37);
if (lean_is_scalar(x_28)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_28;
}
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_32);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
}
block_72:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_60, 0, x_34);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 1, x_3);
x_61 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_60, x_56, x_57, x_58, x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_37);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_31);
lean_ctor_set(x_65, 1, x_32);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_37);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_31);
lean_ctor_set(x_69, 1, x_32);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_36);
if (x_215 == 0)
{
return x_36;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_36, 0);
x_217 = lean_ctor_get(x_36, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_36);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_28;
}
lean_ctor_set(x_219, 0, x_31);
lean_ctor_set(x_219, 1, x_32);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_29);
lean_ctor_set(x_220, 1, x_219);
x_16 = x_220;
x_17 = x_15;
goto block_22;
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_6, x_19);
x_6 = x_20;
x_7 = x_16;
x_15 = x_17;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0(lean_object* x_1, uint8_t x_2, uint8_t x_3, lean_object* x_4, size_t x_5, size_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; lean_object* x_17; uint8_t x_23; 
x_23 = lean_usize_dec_lt(x_6, x_5);
if (x_23 == 0)
{
lean_object* x_24; 
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_7);
lean_ctor_set(x_24, 1, x_15);
return x_24;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_array_uget(x_4, x_6);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_28 = x_25;
} else {
 lean_dec_ref(x_25);
 x_28 = lean_box(0);
}
x_29 = lean_box(0);
x_30 = lean_ctor_get(x_7, 1);
lean_inc(x_30);
lean_dec(x_7);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 1);
lean_inc(x_32);
lean_dec(x_30);
x_33 = lean_ctor_get(x_26, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
lean_dec(x_33);
lean_inc(x_1);
x_35 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_1, x_34);
if (x_35 == 0)
{
lean_object* x_36; 
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_31);
x_36 = l_Lean_Meta_Simp_SimprocEntry_tryD(x_26, x_27, x_31, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
switch (lean_obj_tag(x_37)) {
case 0:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_73 = lean_ctor_get(x_37, 0);
lean_inc(x_73);
x_74 = lean_mk_string_unchecked("Debug", 5, 5);
x_75 = lean_mk_string_unchecked("Meta", 4, 4);
x_76 = lean_mk_string_unchecked("Tactic", 6, 6);
x_77 = lean_mk_string_unchecked("simp", 4, 4);
x_78 = l_Lean_Name_mkStr4(x_74, x_75, x_76, x_77);
lean_inc(x_78);
x_79 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_78, x_13, x_38);
x_80 = lean_ctor_get(x_79, 0);
lean_inc(x_80);
x_81 = lean_unbox(x_80);
lean_dec(x_80);
if (x_81 == 0)
{
lean_object* x_82; 
lean_dec(x_78);
lean_dec(x_73);
lean_dec(x_12);
lean_dec(x_11);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
lean_dec(x_79);
x_39 = x_10;
x_40 = x_13;
x_41 = x_14;
x_42 = x_82;
goto block_55;
}
else
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_79);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_84 = lean_ctor_get(x_79, 1);
x_85 = lean_ctor_get(x_79, 0);
lean_dec(x_85);
x_86 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
lean_inc(x_31);
x_88 = l_Lean_MessageData_ofExpr(x_31);
lean_ctor_set_tag(x_79, 7);
lean_ctor_set(x_79, 1, x_88);
lean_ctor_set(x_79, 0, x_87);
x_89 = lean_mk_string_unchecked(" => ", 4, 4);
x_90 = l_Lean_stringToMessageData(x_89);
lean_dec(x_89);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_79);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_MessageData_ofExpr(x_73);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
x_94 = lean_mk_string_unchecked("", 0, 0);
x_95 = l_Lean_stringToMessageData(x_94);
lean_dec(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_78, x_96, x_11, x_12, x_13, x_14, x_84);
lean_dec(x_12);
lean_dec(x_11);
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_39 = x_10;
x_40 = x_13;
x_41 = x_14;
x_42 = x_98;
goto block_55;
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_99 = lean_ctor_get(x_79, 1);
lean_inc(x_99);
lean_dec(x_79);
x_100 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_101 = l_Lean_stringToMessageData(x_100);
lean_dec(x_100);
lean_inc(x_31);
x_102 = l_Lean_MessageData_ofExpr(x_31);
x_103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_103, 0, x_101);
lean_ctor_set(x_103, 1, x_102);
x_104 = lean_mk_string_unchecked(" => ", 4, 4);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_103);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_MessageData_ofExpr(x_73);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("", 0, 0);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
x_111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_111, 0, x_108);
lean_ctor_set(x_111, 1, x_110);
x_112 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_78, x_111, x_11, x_12, x_13, x_14, x_99);
lean_dec(x_12);
lean_dec(x_11);
x_113 = lean_ctor_get(x_112, 1);
lean_inc(x_113);
lean_dec(x_112);
x_39 = x_10;
x_40 = x_13;
x_41 = x_14;
x_42 = x_113;
goto block_55;
}
}
}
case 1:
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
lean_dec(x_28);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_114 = lean_ctor_get(x_37, 0);
lean_inc(x_114);
x_115 = lean_mk_string_unchecked("Debug", 5, 5);
x_116 = lean_mk_string_unchecked("Meta", 4, 4);
x_117 = lean_mk_string_unchecked("Tactic", 6, 6);
x_118 = lean_mk_string_unchecked("simp", 4, 4);
x_119 = l_Lean_Name_mkStr4(x_115, x_116, x_117, x_118);
lean_inc(x_119);
x_120 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_119, x_13, x_38);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
x_122 = lean_unbox(x_121);
lean_dec(x_121);
if (x_122 == 0)
{
lean_object* x_123; 
lean_dec(x_119);
lean_dec(x_114);
lean_dec(x_12);
lean_dec(x_11);
x_123 = lean_ctor_get(x_120, 1);
lean_inc(x_123);
lean_dec(x_120);
x_56 = x_10;
x_57 = x_13;
x_58 = x_14;
x_59 = x_123;
goto block_72;
}
else
{
uint8_t x_124; 
x_124 = !lean_is_exclusive(x_120);
if (x_124 == 0)
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_125 = lean_ctor_get(x_120, 1);
x_126 = lean_ctor_get(x_120, 0);
lean_dec(x_126);
x_127 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_128 = l_Lean_stringToMessageData(x_127);
lean_dec(x_127);
lean_inc(x_31);
x_129 = l_Lean_MessageData_ofExpr(x_31);
lean_ctor_set_tag(x_120, 7);
lean_ctor_set(x_120, 1, x_129);
lean_ctor_set(x_120, 0, x_128);
x_130 = lean_mk_string_unchecked(" => ", 4, 4);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_120);
lean_ctor_set(x_132, 1, x_131);
x_133 = l_Lean_MessageData_ofExpr(x_114);
x_134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_134, 0, x_132);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_mk_string_unchecked("", 0, 0);
x_136 = l_Lean_stringToMessageData(x_135);
lean_dec(x_135);
x_137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_137, 0, x_134);
lean_ctor_set(x_137, 1, x_136);
x_138 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_119, x_137, x_11, x_12, x_13, x_14, x_125);
lean_dec(x_12);
lean_dec(x_11);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_dec(x_138);
x_56 = x_10;
x_57 = x_13;
x_58 = x_14;
x_59 = x_139;
goto block_72;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
x_140 = lean_ctor_get(x_120, 1);
lean_inc(x_140);
lean_dec(x_120);
x_141 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_142 = l_Lean_stringToMessageData(x_141);
lean_dec(x_141);
lean_inc(x_31);
x_143 = l_Lean_MessageData_ofExpr(x_31);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked(" => ", 4, 4);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_MessageData_ofExpr(x_114);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked("", 0, 0);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_119, x_152, x_11, x_12, x_13, x_14, x_140);
lean_dec(x_12);
lean_dec(x_11);
x_154 = lean_ctor_get(x_153, 1);
lean_inc(x_154);
lean_dec(x_153);
x_56 = x_10;
x_57 = x_13;
x_58 = x_14;
x_59 = x_154;
goto block_72;
}
}
}
default: 
{
lean_object* x_155; 
lean_dec(x_28);
x_155 = lean_ctor_get(x_37, 0);
lean_inc(x_155);
lean_dec(x_37);
if (lean_obj_tag(x_155) == 0)
{
lean_object* x_156; lean_object* x_157; 
lean_dec(x_34);
x_156 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_156, 0, x_31);
lean_ctor_set(x_156, 1, x_32);
x_157 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_157, 0, x_29);
lean_ctor_set(x_157, 1, x_156);
x_16 = x_157;
x_17 = x_38;
goto block_22;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; uint8_t x_182; 
lean_dec(x_32);
x_158 = lean_ctor_get(x_155, 0);
lean_inc(x_158);
lean_dec(x_155);
x_175 = lean_mk_string_unchecked("Debug", 5, 5);
x_176 = lean_mk_string_unchecked("Meta", 4, 4);
x_177 = lean_mk_string_unchecked("Tactic", 6, 6);
x_178 = lean_mk_string_unchecked("simp", 4, 4);
x_179 = l_Lean_Name_mkStr4(x_175, x_176, x_177, x_178);
lean_inc(x_179);
x_180 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_179, x_13, x_38);
x_181 = lean_ctor_get(x_180, 0);
lean_inc(x_181);
x_182 = lean_unbox(x_181);
lean_dec(x_181);
if (x_182 == 0)
{
lean_object* x_183; 
lean_dec(x_179);
lean_dec(x_31);
x_183 = lean_ctor_get(x_180, 1);
lean_inc(x_183);
lean_dec(x_180);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
x_159 = x_10;
x_160 = x_13;
x_161 = x_14;
x_162 = x_183;
goto block_174;
}
else
{
uint8_t x_184; 
x_184 = !lean_is_exclusive(x_180);
if (x_184 == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; 
x_185 = lean_ctor_get(x_180, 1);
x_186 = lean_ctor_get(x_180, 0);
lean_dec(x_186);
x_187 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = l_Lean_MessageData_ofExpr(x_31);
lean_ctor_set_tag(x_180, 7);
lean_ctor_set(x_180, 1, x_189);
lean_ctor_set(x_180, 0, x_188);
x_190 = lean_mk_string_unchecked(" => ", 4, 4);
x_191 = l_Lean_stringToMessageData(x_190);
lean_dec(x_190);
x_192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_192, 0, x_180);
lean_ctor_set(x_192, 1, x_191);
lean_inc(x_158);
x_193 = l_Lean_MessageData_ofExpr(x_158);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
x_195 = lean_mk_string_unchecked("", 0, 0);
x_196 = l_Lean_stringToMessageData(x_195);
lean_dec(x_195);
x_197 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_197, 0, x_194);
lean_ctor_set(x_197, 1, x_196);
x_198 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_179, x_197, x_11, x_12, x_13, x_14, x_185);
x_199 = lean_ctor_get(x_198, 1);
lean_inc(x_199);
lean_dec(x_198);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
x_159 = x_10;
x_160 = x_13;
x_161 = x_14;
x_162 = x_199;
goto block_174;
}
else
{
lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_200 = lean_ctor_get(x_180, 1);
lean_inc(x_200);
lean_dec(x_180);
x_201 = lean_mk_string_unchecked("simproc result ", 15, 15);
x_202 = l_Lean_stringToMessageData(x_201);
lean_dec(x_201);
x_203 = l_Lean_MessageData_ofExpr(x_31);
x_204 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_204, 0, x_202);
lean_ctor_set(x_204, 1, x_203);
x_205 = lean_mk_string_unchecked(" => ", 4, 4);
x_206 = l_Lean_stringToMessageData(x_205);
lean_dec(x_205);
x_207 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_207, 0, x_204);
lean_ctor_set(x_207, 1, x_206);
lean_inc(x_158);
x_208 = l_Lean_MessageData_ofExpr(x_158);
x_209 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_209, 0, x_207);
lean_ctor_set(x_209, 1, x_208);
x_210 = lean_mk_string_unchecked("", 0, 0);
x_211 = l_Lean_stringToMessageData(x_210);
lean_dec(x_210);
x_212 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_212, 0, x_209);
lean_ctor_set(x_212, 1, x_211);
x_213 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_179, x_212, x_11, x_12, x_13, x_14, x_200);
x_214 = lean_ctor_get(x_213, 1);
lean_inc(x_214);
lean_dec(x_213);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_10);
x_159 = x_10;
x_160 = x_13;
x_161 = x_14;
x_162 = x_214;
goto block_174;
}
}
block_174:
{
lean_object* x_163; lean_object* x_164; uint8_t x_165; 
x_163 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_163, 0, x_34);
lean_ctor_set_uint8(x_163, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_163, sizeof(void*)*1 + 1, x_3);
x_164 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_163, x_159, x_160, x_161, x_162);
lean_dec(x_161);
lean_dec(x_160);
lean_dec(x_159);
x_165 = !lean_is_exclusive(x_164);
if (x_165 == 0)
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
x_166 = lean_ctor_get(x_164, 1);
x_167 = lean_ctor_get(x_164, 0);
lean_dec(x_167);
x_168 = lean_box(x_23);
lean_ctor_set(x_164, 1, x_168);
lean_ctor_set(x_164, 0, x_158);
x_169 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_169, 0, x_29);
lean_ctor_set(x_169, 1, x_164);
x_16 = x_169;
x_17 = x_166;
goto block_22;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_164, 1);
lean_inc(x_170);
lean_dec(x_164);
x_171 = lean_box(x_23);
x_172 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_172, 0, x_158);
lean_ctor_set(x_172, 1, x_171);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_29);
lean_ctor_set(x_173, 1, x_172);
x_16 = x_173;
x_17 = x_170;
goto block_22;
}
}
}
}
}
block_55:
{
lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_43 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_43, 0, x_34);
lean_ctor_set_uint8(x_43, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_43, sizeof(void*)*1 + 1, x_3);
x_44 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_43, x_39, x_40, x_41, x_42);
lean_dec(x_41);
lean_dec(x_40);
lean_dec(x_39);
x_45 = !lean_is_exclusive(x_44);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_44, 0);
lean_dec(x_46);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_37);
if (lean_is_scalar(x_28)) {
 x_48 = lean_alloc_ctor(0, 2, 0);
} else {
 x_48 = x_28;
}
lean_ctor_set(x_48, 0, x_31);
lean_ctor_set(x_48, 1, x_32);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
lean_ctor_set(x_44, 0, x_49);
return x_44;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_44, 1);
lean_inc(x_50);
lean_dec(x_44);
x_51 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_51, 0, x_37);
if (lean_is_scalar(x_28)) {
 x_52 = lean_alloc_ctor(0, 2, 0);
} else {
 x_52 = x_28;
}
lean_ctor_set(x_52, 0, x_31);
lean_ctor_set(x_52, 1, x_32);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_50);
return x_54;
}
}
block_72:
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_60 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_60, 0, x_34);
lean_ctor_set_uint8(x_60, sizeof(void*)*1, x_2);
lean_ctor_set_uint8(x_60, sizeof(void*)*1 + 1, x_3);
x_61 = l_Lean_Meta_Simp_recordSimpTheorem___redArg(x_60, x_56, x_57, x_58, x_59);
lean_dec(x_58);
lean_dec(x_57);
lean_dec(x_56);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_37);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_31);
lean_ctor_set(x_65, 1, x_32);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
lean_ctor_set(x_61, 0, x_66);
return x_61;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_67 = lean_ctor_get(x_61, 1);
lean_inc(x_67);
lean_dec(x_61);
x_68 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_68, 0, x_37);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_31);
lean_ctor_set(x_69, 1, x_32);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_68);
lean_ctor_set(x_70, 1, x_69);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_67);
return x_71;
}
}
}
else
{
uint8_t x_215; 
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_28);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_1);
x_215 = !lean_is_exclusive(x_36);
if (x_215 == 0)
{
return x_36;
}
else
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; 
x_216 = lean_ctor_get(x_36, 0);
x_217 = lean_ctor_get(x_36, 1);
lean_inc(x_217);
lean_inc(x_216);
lean_dec(x_36);
x_218 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_218, 0, x_216);
lean_ctor_set(x_218, 1, x_217);
return x_218;
}
}
}
else
{
lean_object* x_219; lean_object* x_220; 
lean_dec(x_34);
lean_dec(x_27);
lean_dec(x_26);
if (lean_is_scalar(x_28)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_28;
}
lean_ctor_set(x_219, 0, x_31);
lean_ctor_set(x_219, 1, x_32);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_29);
lean_ctor_set(x_220, 1, x_219);
x_16 = x_220;
x_17 = x_15;
goto block_22;
}
}
block_22:
{
lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_6, x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_20, x_16, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_17);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_18; lean_object* x_19; lean_object* x_61; lean_object* x_62; lean_object* x_108; lean_object* x_109; uint64_t x_110; uint8_t x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; uint8_t x_118; uint8_t x_119; lean_object* x_120; lean_object* x_121; 
x_108 = lean_ctor_get(x_6, 4);
lean_inc(x_108);
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get_uint64(x_108, sizeof(void*)*1);
lean_dec(x_108);
x_111 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 8);
x_112 = lean_ctor_get(x_8, 1);
lean_inc(x_112);
x_113 = lean_ctor_get(x_8, 2);
lean_inc(x_113);
x_114 = lean_ctor_get(x_8, 3);
lean_inc(x_114);
x_115 = lean_ctor_get(x_8, 4);
lean_inc(x_115);
x_116 = lean_ctor_get(x_8, 5);
lean_inc(x_116);
x_117 = lean_ctor_get(x_8, 6);
lean_inc(x_117);
x_118 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 9);
x_119 = lean_ctor_get_uint8(x_8, sizeof(void*)*7 + 10);
x_120 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_120, 0, x_109);
lean_ctor_set(x_120, 1, x_112);
lean_ctor_set(x_120, 2, x_113);
lean_ctor_set(x_120, 3, x_114);
lean_ctor_set(x_120, 4, x_115);
lean_ctor_set(x_120, 5, x_116);
lean_ctor_set(x_120, 6, x_117);
lean_ctor_set_uint64(x_120, sizeof(void*)*7, x_110);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 8, x_111);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 9, x_118);
lean_ctor_set_uint8(x_120, sizeof(void*)*7 + 10, x_119);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_4);
x_121 = l_Lean_Meta_DiscrTree_getMatchWithExtra(lean_box(0), x_2, x_4, x_120, x_9, x_10, x_11, x_12);
lean_dec(x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_121, 1);
lean_inc(x_123);
lean_dec(x_121);
x_61 = x_122;
x_62 = x_123;
goto block_107;
}
else
{
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_ctor_get(x_121, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_121, 1);
lean_inc(x_125);
lean_dec(x_121);
x_61 = x_124;
x_62 = x_125;
goto block_107;
}
else
{
uint8_t x_126; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_126 = !lean_is_exclusive(x_121);
if (x_126 == 0)
{
return x_121;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_121, 0);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_121);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
}
block_17:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_13);
return x_16;
}
block_60:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_20 = lean_mk_string_unchecked("Debug", 5, 5);
x_21 = lean_mk_string_unchecked("Meta", 4, 4);
x_22 = lean_mk_string_unchecked("Tactic", 6, 6);
x_23 = lean_mk_string_unchecked("simp", 4, 4);
x_24 = l_Lean_Name_mkStr4(x_20, x_21, x_22, x_23);
lean_inc(x_24);
x_25 = l_Lean_isTracingEnabledFor___at___Lean_Meta_Simp_congrArgs_spec__0___redArg(x_24, x_10, x_18);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_unbox(x_26);
lean_dec(x_26);
if (x_27 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_4);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
lean_dec(x_25);
x_13 = x_28;
goto block_17;
}
else
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_25);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_30 = lean_ctor_get(x_25, 1);
x_31 = lean_ctor_get(x_25, 0);
lean_dec(x_31);
x_32 = lean_mk_string_unchecked("no ", 3, 3);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = l_Lean_stringToMessageData(x_19);
lean_ctor_set_tag(x_25, 7);
lean_ctor_set(x_25, 1, x_34);
lean_ctor_set(x_25, 0, x_33);
x_35 = lean_mk_string_unchecked("-simprocs found for ", 20, 20);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_25);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_MessageData_ofExpr(x_4);
x_39 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_mk_string_unchecked("", 0, 0);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_39);
lean_ctor_set(x_42, 1, x_41);
x_43 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_24, x_42, x_8, x_9, x_10, x_11, x_30);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_13 = x_44;
goto block_17;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_45 = lean_ctor_get(x_25, 1);
lean_inc(x_45);
lean_dec(x_25);
x_46 = lean_mk_string_unchecked("no ", 3, 3);
x_47 = l_Lean_stringToMessageData(x_46);
lean_dec(x_46);
x_48 = l_Lean_stringToMessageData(x_19);
x_49 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_mk_string_unchecked("-simprocs found for ", 20, 20);
x_51 = l_Lean_stringToMessageData(x_50);
lean_dec(x_50);
x_52 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_52, 0, x_49);
lean_ctor_set(x_52, 1, x_51);
x_53 = l_Lean_MessageData_ofExpr(x_4);
x_54 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
x_55 = lean_mk_string_unchecked("", 0, 0);
x_56 = l_Lean_stringToMessageData(x_55);
lean_dec(x_55);
x_57 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_57, 0, x_54);
lean_ctor_set(x_57, 1, x_56);
x_58 = l_Lean_addTrace___at___Lean_Meta_Simp_congrArgs_spec__1___redArg(x_24, x_57, x_8, x_9, x_10, x_11, x_45);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_13 = x_59;
goto block_17;
}
}
}
block_107:
{
uint8_t x_63; 
x_63 = l_Array_isEmpty___redArg(x_61);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; size_t x_68; lean_object* x_69; size_t x_70; lean_object* x_71; 
x_64 = lean_box(0);
x_65 = lean_box(x_63);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_4);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_64);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_array_size(x_61);
x_69 = lean_unsigned_to_nat(0u);
x_70 = lean_usize_of_nat(x_69);
x_71 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0(x_3, x_1, x_63, x_61, x_68, x_70, x_67, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_62);
lean_dec(x_61);
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
lean_object* x_75; uint8_t x_76; 
x_75 = lean_ctor_get(x_73, 1);
lean_inc(x_75);
x_76 = lean_unbox(x_75);
lean_dec(x_75);
if (x_76 == 0)
{
uint8_t x_77; 
lean_dec(x_73);
x_77 = !lean_is_exclusive(x_71);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_71, 0);
lean_dec(x_78);
x_79 = lean_box(0);
x_80 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_80, 0, x_79);
lean_ctor_set(x_71, 0, x_80);
return x_71;
}
else
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_81 = lean_ctor_get(x_71, 1);
lean_inc(x_81);
lean_dec(x_71);
x_82 = lean_box(0);
x_83 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_83, 0, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
return x_84;
}
}
else
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_71);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_71, 0);
lean_dec(x_86);
x_87 = lean_ctor_get(x_73, 0);
lean_inc(x_87);
lean_dec(x_73);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_71, 0, x_89);
return x_71;
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_90 = lean_ctor_get(x_71, 1);
lean_inc(x_90);
lean_dec(x_71);
x_91 = lean_ctor_get(x_73, 0);
lean_inc(x_91);
lean_dec(x_73);
x_92 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_93, 0, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_93);
lean_ctor_set(x_94, 1, x_90);
return x_94;
}
}
}
else
{
uint8_t x_95; 
lean_dec(x_73);
x_95 = !lean_is_exclusive(x_71);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = lean_ctor_get(x_71, 0);
lean_dec(x_96);
x_97 = lean_ctor_get(x_74, 0);
lean_inc(x_97);
lean_dec(x_74);
lean_ctor_set(x_71, 0, x_97);
return x_71;
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_98 = lean_ctor_get(x_71, 1);
lean_inc(x_98);
lean_dec(x_71);
x_99 = lean_ctor_get(x_74, 0);
lean_inc(x_99);
lean_dec(x_74);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_98);
return x_100;
}
}
}
else
{
uint8_t x_101; 
x_101 = !lean_is_exclusive(x_71);
if (x_101 == 0)
{
return x_71;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_102 = lean_ctor_get(x_71, 0);
x_103 = lean_ctor_get(x_71, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_71);
x_104 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
return x_104;
}
}
}
else
{
lean_dec(x_61);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
if (x_1 == 0)
{
lean_object* x_105; 
x_105 = lean_mk_string_unchecked("pre", 3, 3);
x_18 = x_62;
x_19 = x_105;
goto block_60;
}
else
{
lean_object* x_106; 
x_106 = lean_mk_string_unchecked("post", 4, 4);
x_18 = x_62;
x_19 = x_106;
goto block_60;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0_spec__0(x_1, x_16, x_17, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
uint8_t x_16; uint8_t x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox(x_3);
lean_dec(x_3);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = lean_unbox_usize(x_6);
lean_dec(x_6);
x_20 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocCore_spec__0(x_1, x_16, x_17, x_4, x_18, x_19, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_4);
return x_20;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_1);
lean_dec(x_1);
x_14 = l_Lean_Meta_Simp_dsimprocCore(x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Array_isEmpty___redArg(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_array_get_size(x_1);
x_10 = lean_nat_dec_lt(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_2);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_1);
lean_ctor_set(x_11, 1, x_6);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_1, x_8);
x_13 = l_Lean_Meta_Simp_Simprocs_add(x_12, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = lean_box(0);
x_17 = lean_array_fset(x_1, x_8, x_16);
x_18 = lean_array_fset(x_17, x_8, x_15);
lean_ctor_set(x_13, 0, x_18);
return x_13;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_19 = lean_ctor_get(x_13, 0);
x_20 = lean_ctor_get(x_13, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_13);
x_21 = lean_box(0);
x_22 = lean_array_fset(x_1, x_8, x_21);
x_23 = lean_array_fset(x_22, x_8, x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_1);
x_25 = !lean_is_exclusive(x_13);
if (x_25 == 0)
{
return x_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_13, 0);
x_27 = lean_ctor_get(x_13, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_13);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_29 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_30 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
lean_inc(x_30);
lean_inc(x_29);
x_31 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_31, 2, x_30);
lean_ctor_set(x_31, 3, x_30);
x_32 = l_Lean_Meta_Simp_Simprocs_add(x_31, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_32) == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_32);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_32, 0);
x_35 = lean_unsigned_to_nat(1u);
x_36 = lean_mk_empty_array_with_capacity(x_35);
x_37 = lean_array_push(x_36, x_34);
lean_ctor_set(x_32, 0, x_37);
return x_32;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_38 = lean_ctor_get(x_32, 0);
x_39 = lean_ctor_get(x_32, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_32);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_mk_empty_array_with_capacity(x_40);
x_42 = lean_array_push(x_41, x_38);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_39);
return x_43;
}
}
else
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_32);
if (x_44 == 0)
{
return x_32;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_45 = lean_ctor_get(x_32, 0);
x_46 = lean_ctor_get(x_32, 1);
lean_inc(x_46);
lean_inc(x_45);
lean_dec(x_32);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
return x_47;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_add___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_3);
lean_dec(x_3);
x_8 = l_Lean_Meta_Simp_SimprocsArray_add(x_1, x_2, x_7, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_SimprocsArray_erase_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
x_9 = l_Lean_Meta_Simp_Simprocs_erase(x_6, x_1);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_erase(lean_object* x_1, lean_object* x_2) {
_start:
{
size_t x_3; lean_object* x_4; size_t x_5; lean_object* x_6; 
x_3 = lean_array_size(x_1);
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_usize_of_nat(x_4);
x_6 = l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_SimprocsArray_erase_spec__0(x_2, x_3, x_5, x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_SimprocsArray_erase_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_mapMUnsafe_map___at___Lean_Meta_Simp_SimprocsArray_erase_spec__0(x_1, x_5, x_6, x_4);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_SimprocsArray_isErased_spec__0(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_2, x_3);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = l_Lean_PersistentHashMap_contains___at___Lean_SMap_contains___at___Lean_Environment_addExtraName_spec__0_spec__0(lean_box(0), x_7, x_1);
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
LEAN_EXPORT uint8_t l_Lean_Meta_Simp_SimprocsArray_isErased(lean_object* x_1, lean_object* x_2) {
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
x_8 = l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_SimprocsArray_isErased_spec__0(x_2, x_1, x_6, x_7);
return x_8;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_SimprocsArray_isErased_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; uint8_t x_7; lean_object* x_8; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_7 = l_Array_anyMUnsafe_any___at___Lean_Meta_Simp_SimprocsArray_isErased_spec__0(x_1, x_2, x_5, x_6);
lean_dec(x_2);
lean_dec(x_1);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocsArray_isErased___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_SimprocsArray_isErased(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocArrayCore_spec__0(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
lean_object* x_15; lean_object* x_16; uint8_t x_22; 
x_22 = lean_usize_dec_lt(x_5, x_4);
if (x_22 == 0)
{
lean_object* x_23; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_6);
lean_ctor_set(x_23, 1, x_14);
return x_23;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_24 = lean_box(0);
x_36 = lean_box(0);
x_37 = lean_array_uget(x_3, x_5);
x_38 = lean_ctor_get(x_6, 1);
lean_inc(x_38);
lean_dec(x_6);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 1);
lean_inc(x_42);
lean_dec(x_40);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
if (x_2 == 0)
{
lean_object* x_159; 
x_159 = lean_ctor_get(x_37, 0);
lean_inc(x_159);
x_45 = x_159;
goto block_158;
}
else
{
lean_object* x_160; 
x_160 = lean_ctor_get(x_37, 1);
lean_inc(x_160);
x_45 = x_160;
goto block_158;
}
block_35:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_29 = lean_box(x_22);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_27);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_25);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_box(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_24);
lean_ctor_set(x_34, 1, x_33);
x_15 = x_34;
x_16 = x_26;
goto block_21;
}
block_158:
{
lean_object* x_46; lean_object* x_47; 
x_46 = lean_ctor_get(x_37, 3);
lean_inc(x_46);
lean_dec(x_37);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_41);
x_47 = l_Lean_Meta_Simp_simprocCore(x_1, x_45, x_46, x_41, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
switch (lean_obj_tag(x_48)) {
case 0:
{
lean_object* x_49; uint8_t x_50; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_49 = lean_ctor_get(x_47, 1);
lean_inc(x_49);
lean_dec(x_47);
x_50 = !lean_is_exclusive(x_48);
if (x_50 == 0)
{
lean_object* x_51; uint8_t x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_48, 0);
x_52 = lean_unbox(x_39);
lean_inc(x_44);
x_53 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_44, x_52, x_51, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_53) == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_48, 0, x_55);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_48);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_43);
lean_ctor_set(x_57, 1, x_44);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_41);
lean_ctor_set(x_58, 1, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_39);
lean_ctor_set(x_59, 1, x_58);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_56);
lean_ctor_set(x_60, 1, x_59);
lean_ctor_set(x_53, 0, x_60);
return x_53;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_61 = lean_ctor_get(x_53, 0);
x_62 = lean_ctor_get(x_53, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_53);
lean_ctor_set(x_48, 0, x_61);
x_63 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_63, 0, x_48);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_43);
lean_ctor_set(x_64, 1, x_44);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_41);
lean_ctor_set(x_65, 1, x_64);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_39);
lean_ctor_set(x_66, 1, x_65);
x_67 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_67, 0, x_63);
lean_ctor_set(x_67, 1, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_62);
return x_68;
}
}
else
{
uint8_t x_69; 
lean_free_object(x_48);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
x_69 = !lean_is_exclusive(x_53);
if (x_69 == 0)
{
return x_53;
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_53, 0);
x_71 = lean_ctor_get(x_53, 1);
lean_inc(x_71);
lean_inc(x_70);
lean_dec(x_53);
x_72 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_71);
return x_72;
}
}
}
else
{
lean_object* x_73; uint8_t x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_48, 0);
lean_inc(x_73);
lean_dec(x_48);
x_74 = lean_unbox(x_39);
lean_inc(x_44);
x_75 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_44, x_74, x_73, x_10, x_11, x_12, x_13, x_49);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_78 = x_75;
} else {
 lean_dec_ref(x_75);
 x_78 = lean_box(0);
}
x_79 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_79, 0, x_76);
x_80 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_80, 0, x_79);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_43);
lean_ctor_set(x_81, 1, x_44);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_41);
lean_ctor_set(x_82, 1, x_81);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_39);
lean_ctor_set(x_83, 1, x_82);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_80);
lean_ctor_set(x_84, 1, x_83);
if (lean_is_scalar(x_78)) {
 x_85 = lean_alloc_ctor(0, 2, 0);
} else {
 x_85 = x_78;
}
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_77);
return x_85;
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
x_86 = lean_ctor_get(x_75, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_75, 1);
lean_inc(x_87);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_88 = x_75;
} else {
 lean_dec_ref(x_75);
 x_88 = lean_box(0);
}
if (lean_is_scalar(x_88)) {
 x_89 = lean_alloc_ctor(1, 2, 0);
} else {
 x_89 = x_88;
}
lean_ctor_set(x_89, 0, x_86);
lean_ctor_set(x_89, 1, x_87);
return x_89;
}
}
}
case 1:
{
lean_object* x_90; uint8_t x_91; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_90 = lean_ctor_get(x_47, 1);
lean_inc(x_90);
lean_dec(x_47);
x_91 = !lean_is_exclusive(x_48);
if (x_91 == 0)
{
lean_object* x_92; uint8_t x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_48, 0);
x_93 = lean_unbox(x_39);
lean_inc(x_44);
x_94 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_44, x_93, x_92, x_10, x_11, x_12, x_13, x_90);
if (lean_obj_tag(x_94) == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_96 = lean_ctor_get(x_94, 0);
lean_ctor_set(x_48, 0, x_96);
x_97 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_97, 0, x_48);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_43);
lean_ctor_set(x_98, 1, x_44);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_41);
lean_ctor_set(x_99, 1, x_98);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_39);
lean_ctor_set(x_100, 1, x_99);
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_97);
lean_ctor_set(x_101, 1, x_100);
lean_ctor_set(x_94, 0, x_101);
return x_94;
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_102 = lean_ctor_get(x_94, 0);
x_103 = lean_ctor_get(x_94, 1);
lean_inc(x_103);
lean_inc(x_102);
lean_dec(x_94);
lean_ctor_set(x_48, 0, x_102);
x_104 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_104, 0, x_48);
x_105 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_105, 0, x_43);
lean_ctor_set(x_105, 1, x_44);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_41);
lean_ctor_set(x_106, 1, x_105);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_39);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_108, 0, x_104);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_103);
return x_109;
}
}
else
{
uint8_t x_110; 
lean_free_object(x_48);
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
x_110 = !lean_is_exclusive(x_94);
if (x_110 == 0)
{
return x_94;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_94, 0);
x_112 = lean_ctor_get(x_94, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_94);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
lean_object* x_114; uint8_t x_115; lean_object* x_116; 
x_114 = lean_ctor_get(x_48, 0);
lean_inc(x_114);
lean_dec(x_48);
x_115 = lean_unbox(x_39);
lean_inc(x_44);
x_116 = l_Lean_Meta_Simp_mkEqTransOptProofResult(x_44, x_115, x_114, x_10, x_11, x_12, x_13, x_90);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_119 = x_116;
} else {
 lean_dec_ref(x_116);
 x_119 = lean_box(0);
}
x_120 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_120, 0, x_117);
x_121 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_122, 0, x_43);
lean_ctor_set(x_122, 1, x_44);
x_123 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_123, 0, x_41);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_39);
lean_ctor_set(x_124, 1, x_123);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_121);
lean_ctor_set(x_125, 1, x_124);
if (lean_is_scalar(x_119)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_119;
}
lean_ctor_set(x_126, 0, x_125);
lean_ctor_set(x_126, 1, x_118);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
x_127 = lean_ctor_get(x_116, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_116, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_129 = x_116;
} else {
 lean_dec_ref(x_116);
 x_129 = lean_box(0);
}
if (lean_is_scalar(x_129)) {
 x_130 = lean_alloc_ctor(1, 2, 0);
} else {
 x_130 = x_129;
}
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_128);
return x_130;
}
}
}
default: 
{
lean_object* x_131; 
x_131 = lean_ctor_get(x_48, 0);
lean_inc(x_131);
lean_dec(x_48);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_132 = lean_ctor_get(x_47, 1);
lean_inc(x_132);
lean_dec(x_47);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_43);
lean_ctor_set(x_133, 1, x_44);
x_134 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_134, 0, x_41);
lean_ctor_set(x_134, 1, x_133);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_39);
lean_ctor_set(x_135, 1, x_134);
x_136 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_136, 0, x_24);
lean_ctor_set(x_136, 1, x_135);
x_15 = x_136;
x_16 = x_132;
goto block_21;
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_43);
lean_dec(x_41);
x_137 = lean_ctor_get(x_47, 1);
lean_inc(x_137);
lean_dec(x_47);
x_138 = lean_ctor_get(x_131, 0);
lean_inc(x_138);
lean_dec(x_131);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_140 = l_Lean_Meta_mkEqTrans_x3f(x_44, x_139, x_10, x_11, x_12, x_13, x_137);
if (lean_obj_tag(x_140) == 0)
{
uint8_t x_141; 
x_141 = lean_unbox(x_39);
lean_dec(x_39);
if (x_141 == 0)
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; uint8_t x_145; 
x_142 = lean_ctor_get(x_140, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_ctor_get(x_138, 0);
lean_inc(x_144);
lean_dec(x_138);
x_145 = lean_unbox(x_36);
x_25 = x_144;
x_26 = x_143;
x_27 = x_142;
x_28 = x_145;
goto block_35;
}
else
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; uint8_t x_149; 
x_146 = lean_ctor_get(x_140, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_140, 1);
lean_inc(x_147);
lean_dec(x_140);
x_148 = lean_ctor_get(x_138, 0);
lean_inc(x_148);
x_149 = lean_ctor_get_uint8(x_138, sizeof(void*)*2);
lean_dec(x_138);
x_25 = x_148;
x_26 = x_147;
x_27 = x_146;
x_28 = x_149;
goto block_35;
}
}
else
{
uint8_t x_150; 
lean_dec(x_138);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_150 = !lean_is_exclusive(x_140);
if (x_150 == 0)
{
return x_140;
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; 
x_151 = lean_ctor_get(x_140, 0);
x_152 = lean_ctor_get(x_140, 1);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_140);
x_153 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
return x_153;
}
}
}
}
}
}
else
{
uint8_t x_154; 
lean_dec(x_44);
lean_dec(x_43);
lean_dec(x_41);
lean_dec(x_39);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
x_154 = !lean_is_exclusive(x_47);
if (x_154 == 0)
{
return x_47;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_47, 0);
x_156 = lean_ctor_get(x_47, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_47);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
}
}
block_21:
{
lean_object* x_17; size_t x_18; size_t x_19; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_5, x_18);
x_5 = x_19;
x_6 = x_15;
x_14 = x_16;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; lean_object* x_21; size_t x_22; lean_object* x_23; 
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_box(1);
x_15 = lean_box(0);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_13);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_3);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_array_size(x_2);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_usize_of_nat(x_21);
x_23 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocArrayCore_spec__0(x_1, x_1, x_2, x_20, x_22, x_19, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
x_28 = lean_ctor_get(x_24, 0);
lean_inc(x_28);
lean_dec(x_24);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; uint8_t x_30; 
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_unbox(x_29);
lean_dec(x_29);
if (x_30 == 0)
{
uint8_t x_31; 
lean_dec(x_27);
lean_dec(x_26);
x_31 = !lean_is_exclusive(x_23);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_23, 0);
lean_dec(x_32);
x_33 = lean_box(0);
x_34 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_23, 0, x_34);
return x_23;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_35 = lean_ctor_get(x_23, 1);
lean_inc(x_35);
lean_dec(x_23);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
else
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_23);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; 
x_40 = lean_ctor_get(x_23, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_26, 0);
lean_inc(x_41);
lean_dec(x_26);
x_42 = lean_ctor_get(x_27, 1);
lean_inc(x_42);
lean_dec(x_27);
x_43 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_unbox(x_14);
lean_ctor_set_uint8(x_43, sizeof(void*)*2, x_44);
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_23, 0, x_46);
return x_23;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_47 = lean_ctor_get(x_23, 1);
lean_inc(x_47);
lean_dec(x_23);
x_48 = lean_ctor_get(x_26, 0);
lean_inc(x_48);
lean_dec(x_26);
x_49 = lean_ctor_get(x_27, 1);
lean_inc(x_49);
lean_dec(x_27);
x_50 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_unbox(x_14);
lean_ctor_set_uint8(x_50, sizeof(void*)*2, x_51);
x_52 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_52, 0, x_50);
x_53 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_47);
return x_54;
}
}
}
else
{
uint8_t x_55; 
lean_dec(x_27);
lean_dec(x_26);
x_55 = !lean_is_exclusive(x_23);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_23, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_28, 0);
lean_inc(x_57);
lean_dec(x_28);
lean_ctor_set(x_23, 0, x_57);
return x_23;
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_58 = lean_ctor_get(x_23, 1);
lean_inc(x_58);
lean_dec(x_23);
x_59 = lean_ctor_get(x_28, 0);
lean_inc(x_59);
lean_dec(x_28);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set(x_60, 1, x_58);
return x_60;
}
}
}
else
{
uint8_t x_61; 
x_61 = !lean_is_exclusive(x_23);
if (x_61 == 0)
{
return x_23;
}
else
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_62 = lean_ctor_get(x_23, 0);
x_63 = lean_ctor_get(x_23, 1);
lean_inc(x_63);
lean_inc(x_62);
lean_dec(x_23);
x_64 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
return x_64;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocArrayCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; uint8_t x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_15 = lean_unbox(x_1);
lean_dec(x_1);
x_16 = lean_unbox(x_2);
lean_dec(x_2);
x_17 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_18 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_simprocArrayCore_spec__0(x_15, x_16, x_3, x_17, x_18, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14);
lean_dec(x_3);
return x_19;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simprocArrayCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_simprocArrayCore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocArrayCore_spec__0(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_15; uint8_t x_21; 
x_21 = lean_usize_dec_lt(x_4, x_3);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = lean_box(0);
x_24 = lean_array_uget(x_2, x_4);
x_25 = lean_ctor_get(x_5, 1);
lean_inc(x_25);
lean_dec(x_5);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
if (x_1 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_24, 0);
lean_inc(x_56);
x_28 = x_56;
goto block_55;
}
else
{
lean_object* x_57; 
x_57 = lean_ctor_get(x_24, 1);
lean_inc(x_57);
x_28 = x_57;
goto block_55;
}
block_55:
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_24, 3);
lean_inc(x_29);
lean_dec(x_24);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_26);
x_30 = l_Lean_Meta_Simp_dsimprocCore(x_1, x_28, x_29, x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
if (lean_obj_tag(x_31) == 2)
{
lean_object* x_32; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_26);
lean_ctor_set(x_34, 1, x_27);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_23);
lean_ctor_set(x_35, 1, x_34);
x_14 = x_35;
x_15 = x_33;
goto block_20;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_27);
lean_dec(x_26);
x_36 = lean_ctor_get(x_30, 1);
lean_inc(x_36);
lean_dec(x_30);
x_37 = lean_ctor_get(x_32, 0);
lean_inc(x_37);
lean_dec(x_32);
x_38 = lean_box(x_21);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_23);
lean_ctor_set(x_40, 1, x_39);
x_14 = x_40;
x_15 = x_36;
goto block_20;
}
}
else
{
uint8_t x_41; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_41 = !lean_is_exclusive(x_30);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_30, 0);
lean_dec(x_42);
x_43 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_43, 0, x_31);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_26);
lean_ctor_set(x_44, 1, x_27);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_30, 0, x_45);
return x_30;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_46 = lean_ctor_get(x_30, 1);
lean_inc(x_46);
lean_dec(x_30);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_31);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_26);
lean_ctor_set(x_48, 1, x_27);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
return x_50;
}
}
}
else
{
uint8_t x_51; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_51 = !lean_is_exclusive(x_30);
if (x_51 == 0)
{
return x_30;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_52 = lean_ctor_get(x_30, 0);
x_53 = lean_ctor_get(x_30, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_30);
x_54 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_54, 0, x_52);
lean_ctor_set(x_54, 1, x_53);
return x_54;
}
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_4 = x_18;
x_5 = x_14;
x_13 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; lean_object* x_17; size_t x_18; lean_object* x_19; 
x_12 = lean_box(0);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_3);
lean_ctor_set(x_14, 1, x_12);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_array_size(x_2);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_usize_of_nat(x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocArrayCore_spec__0(x_1, x_2, x_16, x_18, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 0);
lean_inc(x_22);
lean_dec(x_20);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_dec(x_21);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_19, 1);
lean_inc(x_29);
lean_dec(x_19);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
else
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_19);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_34 = lean_ctor_get(x_19, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_21, 0);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_35);
x_37 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_19, 0, x_37);
return x_19;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_19, 1);
lean_inc(x_38);
lean_dec(x_19);
x_39 = lean_ctor_get(x_21, 0);
lean_inc(x_39);
lean_dec(x_21);
x_40 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_40, 0, x_39);
x_41 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_38);
return x_42;
}
}
}
else
{
uint8_t x_43; 
lean_dec(x_21);
x_43 = !lean_is_exclusive(x_19);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_19, 0);
lean_dec(x_44);
x_45 = lean_ctor_get(x_22, 0);
lean_inc(x_45);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_45);
return x_19;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_19, 1);
lean_inc(x_46);
lean_dec(x_19);
x_47 = lean_ctor_get(x_22, 0);
lean_inc(x_47);
lean_dec(x_22);
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
x_49 = !lean_is_exclusive(x_19);
if (x_49 == 0)
{
return x_19;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_19, 0);
x_51 = lean_ctor_get(x_19, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_19);
x_52 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_52, 0, x_50);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocArrayCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; size_t x_15; size_t x_16; lean_object* x_17; 
x_14 = lean_unbox(x_1);
lean_dec(x_1);
x_15 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_16 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_17 = l_Array_forIn_x27Unsafe_loop___at___Lean_Meta_Simp_dsimprocArrayCore_spec__0(x_14, x_2, x_15, x_16, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_dsimprocArrayCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l_Lean_Meta_Simp_dsimprocArrayCore(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5382_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("simprocs", 8, 8);
lean_inc(x_2);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_box(1);
x_5 = lean_mk_string_unchecked("backward compatibility", 22, 22);
x_6 = lean_mk_string_unchecked("Enable/disable `simproc`s (simplification procedures).", 54, 54);
x_7 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_5);
lean_ctor_set(x_7, 2, x_6);
x_8 = lean_mk_string_unchecked("Lean", 4, 4);
x_9 = lean_mk_string_unchecked("Meta", 4, 4);
x_10 = lean_mk_string_unchecked("Simp", 4, 4);
x_11 = l_Lean_Name_mkStr4(x_8, x_9, x_10, x_2);
x_12 = l_Lean_Option_register___at___Lean_Elab_initFn____x40_Lean_Elab_AutoBound___hyg_6__spec__0(x_3, x_7, x_11, x_1);
lean_dec(x_7);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_simprocs;
x_13 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_Simp_simprocArrayCore(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPreSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_simprocs;
x_13 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Simp_simprocArrayCore(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPostSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_simprocs;
x_13 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_box(0);
x_18 = lean_unbox(x_17);
x_19 = l_Lean_Meta_Simp_dsimprocArrayCore(x_18, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPreDSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPreDSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_8, 2);
lean_inc(x_11);
x_12 = l_Lean_Meta_Simp_simprocs;
x_13 = l_Lean_Option_get___at_____private_Lean_Util_Profile_0__Lean_get__profiler_spec__0(x_11, x_12);
lean_dec(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_box(0);
x_15 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_15, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_10);
return x_16;
}
else
{
lean_object* x_17; 
x_17 = l_Lean_Meta_Simp_dsimprocArrayCore(x_13, x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_userPostDSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Meta_Simp_userPostDSimprocs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_1);
return x_11;
}
}
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5717_() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_3, 1);
lean_inc(x_4);
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get_uint8(x_3, sizeof(void*)*2);
lean_dec(x_3);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_8 = l_Lean_Meta_Simp_Simprocs_addCore(x_1, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__1(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_toSimprocEntry(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = l_Lean_Meta_DiscrTree_empty(lean_box(0));
x_4 = l_Lean_PersistentHashMap_empty___at___Lean_KeyedDeclsAttribute_mkStateOfTable_spec__1(lean_box(0));
lean_inc(x_4);
lean_inc(x_3);
x_5 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_3);
lean_ctor_set(x_5, 2, x_4);
lean_ctor_set(x_5, 3, x_4);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = lean_ctor_get(x_1, 0);
x_8 = lean_st_ref_get(x_7, x_2);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
return x_8;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_8, 0);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4(lean_object* x_1) {
_start:
{
lean_inc(x_1);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lam__0), 2, 0);
x_5 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lam__1___boxed), 1, 0);
x_6 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lam__2___boxed), 4, 0);
x_7 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lam__3___boxed), 2, 1);
lean_closure_set(x_7, 0, x_2);
x_8 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed), 1, 0);
x_9 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 2, x_6);
lean_ctor_set(x_9, 3, x_5);
lean_ctor_set(x_9, 4, x_4);
lean_ctor_set(x_9, 5, x_8);
x_10 = l_Lean_registerScopedEnvExtensionUnsafe___redArg(x_9, x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_mkSimprocExt___lam__1(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_mkSimprocExt___lam__2(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__3___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_mkSimprocExt___lam__3(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocExt___lam__4___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Meta_Simp_mkSimprocExt___lam__4(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, uint8_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = l_Lean_Syntax_getArg(x_3, x_50);
x_52 = l_Lean_Syntax_isNone(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_53 = lean_unsigned_to_nat(0u);
x_54 = l_Lean_Syntax_getArg(x_51, x_53);
lean_dec(x_51);
x_55 = l_Lean_Syntax_getKind(x_54);
x_56 = lean_mk_string_unchecked("Lean", 4, 4);
x_57 = lean_mk_string_unchecked("Parser", 6, 6);
x_58 = lean_mk_string_unchecked("Tactic", 6, 6);
x_59 = lean_mk_string_unchecked("simpPost", 8, 8);
x_60 = l_Lean_Name_mkStr4(x_56, x_57, x_58, x_59);
x_61 = lean_name_eq(x_55, x_60);
lean_dec(x_60);
lean_dec(x_55);
x_8 = x_61;
goto block_49;
}
else
{
lean_dec(x_51);
x_8 = x_52;
goto block_49;
}
block_49:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; lean_object* x_13; lean_object* x_14; size_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(2u);
x_11 = lean_unsigned_to_nat(5u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_to_nat(x_12);
x_14 = lean_nat_pow(x_10, x_13);
lean_dec(x_13);
x_15 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_16 = lean_usize_to_nat(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_18);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
lean_inc(x_18);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_18);
lean_inc(x_18);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_18);
lean_inc(x_18);
x_22 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_22, 0, x_18);
lean_inc(x_18);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_18);
lean_inc(x_18);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_18);
lean_inc(x_19);
x_25 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_25, 0, x_17);
lean_ctor_set(x_25, 1, x_17);
lean_ctor_set(x_25, 2, x_17);
lean_ctor_set(x_25, 3, x_19);
lean_ctor_set(x_25, 4, x_20);
lean_ctor_set(x_25, 5, x_21);
lean_ctor_set(x_25, 6, x_22);
lean_ctor_set(x_25, 7, x_23);
lean_ctor_set(x_25, 8, x_24);
lean_inc(x_18);
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_18);
lean_inc(x_18);
x_27 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_27, 0, x_18);
lean_inc(x_18);
x_28 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_28, 0, x_18);
lean_inc(x_18);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_18);
lean_inc(x_29);
lean_inc(x_26);
x_30 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_30, 0, x_26);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_29);
lean_ctor_set(x_30, 5, x_29);
x_31 = lean_mk_empty_array_with_capacity(x_16);
lean_dec(x_16);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_31);
lean_ctor_set(x_33, 2, x_17);
lean_ctor_set(x_33, 3, x_17);
lean_ctor_set_usize(x_33, 4, x_12);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_18);
lean_inc_n(x_19, 2);
x_35 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_35, 0, x_19);
lean_ctor_set(x_35, 1, x_19);
lean_ctor_set(x_35, 2, x_19);
lean_ctor_set(x_35, 3, x_34);
x_36 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_36, 0, x_25);
lean_ctor_set(x_36, 1, x_30);
lean_ctor_set(x_36, 2, x_9);
lean_ctor_set(x_36, 3, x_33);
lean_ctor_set(x_36, 4, x_35);
x_37 = lean_st_mk_ref(x_36, x_7);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = l_Lean_Meta_Simp_addSimprocAttrCore(x_1, x_2, x_4, x_8, x_5, x_6, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_st_ref_get(x_38, x_41);
lean_dec(x_38);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_42, 0, x_45);
return x_42;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
lean_dec(x_42);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
lean_dec(x_38);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_addSimprocAttr___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; lean_object* x_9; 
x_8 = lean_unbox(x_4);
lean_dec(x_4);
x_9 = l_Lean_Meta_Simp_addSimprocAttr(x_1, x_2, x_3, x_8, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_mkSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_1);
lean_ctor_set(x_7, 2, x_2);
x_8 = lean_unbox(x_6);
lean_ctor_set_uint8(x_7, sizeof(void*)*3, x_8);
lean_inc(x_3);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_addSimprocAttr___boxed), 7, 1);
lean_closure_set(x_9, 0, x_3);
x_10 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_eraseSimprocAttr___boxed), 5, 1);
lean_closure_set(x_10, 0, x_3);
x_11 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_9);
lean_ctor_set(x_11, 2, x_10);
x_12 = l_Lean_registerBuiltinAttribute(x_11, x_5);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6000_(lean_object* x_1) {
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
static lean_object* _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6044_() {
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_registerSimprocAttr(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
lean_inc(x_4);
x_6 = l_Lean_Meta_Simp_mkSimprocExt(x_4, x_3, x_5);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
lean_inc(x_7);
lean_inc(x_1);
x_9 = l_Lean_Meta_Simp_mkSimprocAttr(x_1, x_2, x_7, x_4, x_8);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_22; 
x_10 = lean_ctor_get(x_9, 1);
lean_inc(x_10);
lean_dec(x_9);
x_11 = l_Lean_Meta_Simp_simprocExtensionMapRef;
x_12 = lean_st_ref_take(x_11, x_10);
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_22 = !lean_is_exclusive(x_13);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; uint8_t x_42; 
x_23 = lean_ctor_get(x_13, 0);
x_24 = lean_ctor_get(x_13, 1);
x_25 = lean_array_get_size(x_24);
x_26 = l_Lean_Name_hash___override(x_1);
x_27 = lean_unsigned_to_nat(32u);
x_28 = lean_uint64_of_nat(x_27);
x_29 = lean_uint64_shift_right(x_26, x_28);
x_30 = lean_uint64_xor(x_26, x_29);
x_31 = lean_unsigned_to_nat(16u);
x_32 = lean_uint64_of_nat(x_31);
x_33 = lean_uint64_shift_right(x_30, x_32);
x_34 = lean_uint64_xor(x_30, x_33);
x_35 = lean_uint64_to_usize(x_34);
x_36 = lean_usize_of_nat(x_25);
lean_dec(x_25);
x_37 = lean_unsigned_to_nat(1u);
x_38 = lean_usize_of_nat(x_37);
x_39 = lean_usize_sub(x_36, x_38);
x_40 = lean_usize_land(x_35, x_39);
x_41 = lean_array_uget(x_24, x_40);
x_42 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_41);
if (x_42 == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_43 = lean_nat_add(x_23, x_37);
lean_dec(x_23);
lean_inc(x_7);
x_44 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_44, 0, x_1);
lean_ctor_set(x_44, 1, x_7);
lean_ctor_set(x_44, 2, x_41);
x_45 = lean_array_uset(x_24, x_40, x_44);
x_46 = lean_unsigned_to_nat(2u);
x_47 = lean_nat_shiftl(x_43, x_46);
x_48 = lean_unsigned_to_nat(3u);
x_49 = lean_nat_div(x_47, x_48);
lean_dec(x_47);
x_50 = lean_array_get_size(x_45);
x_51 = lean_nat_dec_le(x_49, x_50);
lean_dec(x_50);
lean_dec(x_49);
if (x_51 == 0)
{
lean_object* x_52; 
x_52 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_45);
lean_ctor_set(x_13, 1, x_52);
lean_ctor_set(x_13, 0, x_43);
x_15 = x_13;
goto block_21;
}
else
{
lean_ctor_set(x_13, 1, x_45);
lean_ctor_set(x_13, 0, x_43);
x_15 = x_13;
goto block_21;
}
}
else
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
x_53 = lean_box(0);
x_54 = lean_array_uset(x_24, x_40, x_53);
lean_inc(x_7);
x_55 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_7, x_41);
x_56 = lean_array_uset(x_54, x_40, x_55);
lean_ctor_set(x_13, 1, x_56);
x_15 = x_13;
goto block_21;
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; uint64_t x_60; lean_object* x_61; uint64_t x_62; uint64_t x_63; uint64_t x_64; lean_object* x_65; uint64_t x_66; uint64_t x_67; uint64_t x_68; size_t x_69; size_t x_70; lean_object* x_71; size_t x_72; size_t x_73; size_t x_74; lean_object* x_75; uint8_t x_76; 
x_57 = lean_ctor_get(x_13, 0);
x_58 = lean_ctor_get(x_13, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_13);
x_59 = lean_array_get_size(x_58);
x_60 = l_Lean_Name_hash___override(x_1);
x_61 = lean_unsigned_to_nat(32u);
x_62 = lean_uint64_of_nat(x_61);
x_63 = lean_uint64_shift_right(x_60, x_62);
x_64 = lean_uint64_xor(x_60, x_63);
x_65 = lean_unsigned_to_nat(16u);
x_66 = lean_uint64_of_nat(x_65);
x_67 = lean_uint64_shift_right(x_64, x_66);
x_68 = lean_uint64_xor(x_64, x_67);
x_69 = lean_uint64_to_usize(x_68);
x_70 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_71 = lean_unsigned_to_nat(1u);
x_72 = lean_usize_of_nat(x_71);
x_73 = lean_usize_sub(x_70, x_72);
x_74 = lean_usize_land(x_69, x_73);
x_75 = lean_array_uget(x_58, x_74);
x_76 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_NameHashSet_insert_spec__0___redArg(x_1, x_75);
if (x_76 == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; uint8_t x_85; 
x_77 = lean_nat_add(x_57, x_71);
lean_dec(x_57);
lean_inc(x_7);
x_78 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_78, 0, x_1);
lean_ctor_set(x_78, 1, x_7);
lean_ctor_set(x_78, 2, x_75);
x_79 = lean_array_uset(x_58, x_74, x_78);
x_80 = lean_unsigned_to_nat(2u);
x_81 = lean_nat_shiftl(x_77, x_80);
x_82 = lean_unsigned_to_nat(3u);
x_83 = lean_nat_div(x_81, x_82);
lean_dec(x_81);
x_84 = lean_array_get_size(x_79);
x_85 = lean_nat_dec_le(x_83, x_84);
lean_dec(x_84);
lean_dec(x_83);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; 
x_86 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_NameHashSet_insert_spec__1___redArg(x_79);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_77);
lean_ctor_set(x_87, 1, x_86);
x_15 = x_87;
goto block_21;
}
else
{
lean_object* x_88; 
x_88 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_88, 0, x_77);
lean_ctor_set(x_88, 1, x_79);
x_15 = x_88;
goto block_21;
}
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_89 = lean_box(0);
x_90 = lean_array_uset(x_58, x_74, x_89);
lean_inc(x_7);
x_91 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__1___redArg(x_1, x_7, x_75);
x_92 = lean_array_uset(x_90, x_74, x_91);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_57);
lean_ctor_set(x_93, 1, x_92);
x_15 = x_93;
goto block_21;
}
}
block_21:
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_st_ref_set(x_11, x_15, x_14);
x_17 = !lean_is_exclusive(x_16);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_16, 0);
lean_dec(x_18);
lean_ctor_set(x_16, 0, x_7);
return x_16;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_7);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
uint8_t x_94; 
lean_dec(x_7);
lean_dec(x_1);
x_94 = !lean_is_exclusive(x_9);
if (x_94 == 0)
{
return x_9;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; 
x_95 = lean_ctor_get(x_9, 0);
x_96 = lean_ctor_get(x_9, 1);
lean_inc(x_96);
lean_inc(x_95);
lean_dec(x_9);
x_97 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_97, 0, x_95);
lean_ctor_set(x_97, 1, x_96);
return x_97;
}
}
}
else
{
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6114_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("simprocAttr", 11, 11);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Simplification procedure", 24, 24);
x_5 = l_Lean_Meta_Simp_builtinSimprocsRef;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("Simp", 4, 4);
x_10 = lean_mk_string_unchecked("simprocExtension", 16, 16);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = l_Lean_Meta_Simp_registerSimprocAttr(x_3, x_4, x_6, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6144_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_2 = lean_mk_string_unchecked("sevalprocAttr", 13, 13);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_mk_string_unchecked("Symbolic evaluator procedure", 28, 28);
x_5 = l_Lean_Meta_Simp_builtinSEvalprocsRef;
x_6 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_6, 0, x_5);
x_7 = lean_mk_string_unchecked("Lean", 4, 4);
x_8 = lean_mk_string_unchecked("Meta", 4, 4);
x_9 = lean_mk_string_unchecked("Simp", 4, 4);
x_10 = lean_mk_string_unchecked("simprocSEvalExtension", 21, 21);
x_11 = l_Lean_Name_mkStr4(x_7, x_8, x_9, x_10);
x_12 = l_Lean_Meta_Simp_registerSimprocAttr(x_3, x_4, x_6, x_11, x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_box(0);
x_11 = l_Lean_Expr_const___override(x_1, x_10);
lean_inc(x_2);
x_12 = l___private_Lean_ToExpr_0__Lean_Name_toExprAux(x_2);
if (x_3 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_mk_string_unchecked("Bool", 4, 4);
x_29 = lean_mk_string_unchecked("false", 5, 5);
x_30 = l_Lean_Name_mkStr2(x_28, x_29);
x_31 = l_Lean_Expr_const___override(x_30, x_10);
x_13 = x_31;
goto block_27;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_32 = lean_mk_string_unchecked("Bool", 4, 4);
x_33 = lean_mk_string_unchecked("true", 4, 4);
x_34 = l_Lean_Name_mkStr2(x_32, x_33);
x_35 = l_Lean_Expr_const___override(x_34, x_10);
x_13 = x_35;
goto block_27;
}
block_27:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_mk_string_unchecked("declare", 7, 7);
x_16 = l_Lean_Name_mkStr1(x_15);
x_17 = l_Lean_Name_append(x_2, x_16);
x_18 = l___private_Lean_CoreM_0__Lean_Core_mkFreshNameImp(x_17, x_7, x_8, x_9);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = lean_mk_empty_array_with_capacity(x_14);
x_22 = lean_array_push(x_21, x_12);
x_23 = lean_array_push(x_22, x_13);
x_24 = lean_array_push(x_23, x_4);
x_25 = l_Lean_mkAppN(x_11, x_24);
lean_dec(x_24);
x_26 = l_Lean_declareBuiltin(x_19, x_25, x_7, x_8, x_20);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_7 = lean_mk_string_unchecked("unexpected type at simproc", 26, 26);
x_8 = l_Lean_stringToMessageData(x_7);
lean_dec(x_7);
x_9 = l_Lean_throwError___at___Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0_spec__0___redArg(x_8, x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
return x_9;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_9);
x_13 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_20; uint8_t x_21; 
x_17 = lean_unsigned_to_nat(1u);
x_18 = l_Lean_Syntax_getArg(x_2, x_17);
x_19 = l_Lean_Syntax_isNone(x_18);
x_20 = lean_box(1);
if (x_19 == 0)
{
lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; lean_object* x_516; lean_object* x_517; uint8_t x_518; 
x_510 = lean_unsigned_to_nat(0u);
x_511 = l_Lean_Syntax_getArg(x_18, x_510);
lean_dec(x_18);
x_512 = l_Lean_Syntax_getKind(x_511);
x_513 = lean_mk_string_unchecked("Lean", 4, 4);
x_514 = lean_mk_string_unchecked("Parser", 6, 6);
x_515 = lean_mk_string_unchecked("Tactic", 6, 6);
x_516 = lean_mk_string_unchecked("simpPost", 8, 8);
x_517 = l_Lean_Name_mkStr4(x_513, x_514, x_515, x_516);
x_518 = lean_name_eq(x_512, x_517);
lean_dec(x_517);
lean_dec(x_512);
x_21 = x_518;
goto block_509;
}
else
{
uint8_t x_519; 
lean_dec(x_18);
x_519 = lean_unbox(x_20);
x_21 = x_519;
goto block_509;
}
block_16:
{
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_st_ref_get(x_7, x_10);
lean_dec(x_7);
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
lean_dec(x_7);
return x_8;
}
}
block_509:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; size_t x_26; lean_object* x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_22 = lean_box(0);
x_23 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_24 = lean_unsigned_to_nat(2u);
x_25 = lean_unsigned_to_nat(5u);
x_26 = lean_usize_of_nat(x_25);
x_27 = lean_usize_to_nat(x_26);
x_28 = lean_nat_pow(x_24, x_27);
lean_dec(x_27);
x_29 = lean_usize_of_nat(x_28);
lean_dec(x_28);
x_30 = lean_usize_to_nat(x_29);
x_31 = lean_mk_empty_array_with_capacity(x_30);
lean_dec(x_30);
lean_inc(x_31);
x_32 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_32, 0, x_31);
x_33 = lean_unsigned_to_nat(0u);
lean_inc(x_23);
x_34 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_34, 0, x_23);
lean_inc(x_23);
x_35 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_35, 0, x_23);
lean_inc(x_23);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_23);
lean_inc(x_23);
x_37 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_37, 0, x_23);
lean_inc(x_23);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_23);
lean_inc(x_23);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_23);
lean_inc(x_34);
x_40 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_40, 0, x_33);
lean_ctor_set(x_40, 1, x_33);
lean_ctor_set(x_40, 2, x_33);
lean_ctor_set(x_40, 3, x_34);
lean_ctor_set(x_40, 4, x_35);
lean_ctor_set(x_40, 5, x_36);
lean_ctor_set(x_40, 6, x_37);
lean_ctor_set(x_40, 7, x_38);
lean_ctor_set(x_40, 8, x_39);
lean_inc(x_23);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_23);
lean_inc(x_23);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_23);
lean_inc(x_23);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_23);
lean_inc(x_23);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_23);
lean_inc(x_44);
lean_inc(x_41);
x_45 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_45, 0, x_41);
lean_ctor_set(x_45, 1, x_42);
lean_ctor_set(x_45, 2, x_43);
lean_ctor_set(x_45, 3, x_41);
lean_ctor_set(x_45, 4, x_44);
lean_ctor_set(x_45, 5, x_44);
lean_inc(x_31);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_31);
lean_inc(x_31);
x_47 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_31);
lean_ctor_set(x_47, 2, x_33);
lean_ctor_set(x_47, 3, x_33);
lean_ctor_set_usize(x_47, 4, x_26);
lean_inc(x_23);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_23);
lean_inc_n(x_34, 2);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_34);
lean_ctor_set(x_49, 1, x_34);
lean_ctor_set(x_49, 2, x_34);
lean_ctor_set(x_49, 3, x_48);
x_50 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_50, 0, x_40);
lean_ctor_set(x_50, 1, x_45);
lean_ctor_set(x_50, 2, x_22);
lean_ctor_set(x_50, 3, x_47);
lean_ctor_set(x_50, 4, x_49);
x_51 = lean_st_mk_ref(x_50, x_6);
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; uint8_t x_63; uint8_t x_64; uint8_t x_65; uint8_t x_66; uint8_t x_67; uint8_t x_68; uint8_t x_69; uint8_t x_70; uint8_t x_71; uint8_t x_72; uint8_t x_73; uint8_t x_74; uint8_t x_75; uint8_t x_76; uint8_t x_77; uint8_t x_78; uint8_t x_79; uint64_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; uint8_t x_87; uint8_t x_88; lean_object* x_89; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = lean_ctor_get(x_51, 1);
x_55 = lean_box(1);
x_56 = lean_box(0);
x_57 = lean_box(2);
x_58 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_58, 0, x_23);
x_59 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_59, 0, x_32);
lean_ctor_set(x_59, 1, x_31);
lean_ctor_set(x_59, 2, x_33);
lean_ctor_set(x_59, 3, x_33);
lean_ctor_set_usize(x_59, 4, x_26);
x_60 = lean_box(0);
x_61 = lean_alloc_ctor(0, 0, 18);
x_62 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, 0, x_62);
x_63 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, 1, x_63);
x_64 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, 2, x_64);
x_65 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, 3, x_65);
x_66 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, 4, x_66);
x_67 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 5, x_67);
x_68 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 6, x_68);
x_69 = lean_unbox(x_60);
lean_ctor_set_uint8(x_61, 7, x_69);
x_70 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 8, x_70);
x_71 = lean_unbox(x_55);
lean_ctor_set_uint8(x_61, 9, x_71);
x_72 = lean_unbox(x_56);
lean_ctor_set_uint8(x_61, 10, x_72);
x_73 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 11, x_73);
x_74 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 12, x_74);
x_75 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 13, x_75);
x_76 = lean_unbox(x_57);
lean_ctor_set_uint8(x_61, 14, x_76);
x_77 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 15, x_77);
x_78 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 16, x_78);
x_79 = lean_unbox(x_20);
lean_ctor_set_uint8(x_61, 17, x_79);
x_80 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_61);
x_81 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_81, 0, x_58);
lean_ctor_set(x_81, 1, x_59);
lean_ctor_set(x_81, 2, x_22);
x_82 = lean_mk_empty_array_with_capacity(x_33);
x_83 = lean_box(0);
x_84 = lean_box(0);
x_85 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_85, 0, x_61);
lean_ctor_set(x_85, 1, x_22);
lean_ctor_set(x_85, 2, x_81);
lean_ctor_set(x_85, 3, x_82);
lean_ctor_set(x_85, 4, x_83);
lean_ctor_set(x_85, 5, x_33);
lean_ctor_set(x_85, 6, x_84);
lean_ctor_set_uint64(x_85, sizeof(void*)*7, x_80);
x_86 = lean_unbox(x_60);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 8, x_86);
x_87 = lean_unbox(x_60);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 9, x_87);
x_88 = lean_unbox(x_60);
lean_ctor_set_uint8(x_85, sizeof(void*)*7 + 10, x_88);
lean_inc(x_1);
x_89 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_85, x_53, x_4, x_5, x_54);
if (lean_obj_tag(x_89) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_90 = lean_ctor_get(x_89, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_89, 1);
lean_inc(x_91);
lean_dec(x_89);
x_92 = l_Lean_ConstantInfo_type(x_90);
lean_dec(x_90);
switch (lean_obj_tag(x_92)) {
case 0:
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_93 = lean_ctor_get(x_92, 0);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Expr_bvar___override(x_93);
x_95 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_94, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_94);
x_7 = x_53;
x_8 = x_95;
goto block_16;
}
case 1:
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_96 = lean_ctor_get(x_92, 0);
lean_inc(x_96);
lean_dec(x_92);
x_97 = l_Lean_Expr_fvar___override(x_96);
x_98 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_97, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_97);
x_7 = x_53;
x_8 = x_98;
goto block_16;
}
case 2:
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_99 = lean_ctor_get(x_92, 0);
lean_inc(x_99);
lean_dec(x_92);
x_100 = l_Lean_Expr_mvar___override(x_99);
x_101 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_100, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_100);
x_7 = x_53;
x_8 = x_101;
goto block_16;
}
case 3:
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_102 = lean_ctor_get(x_92, 0);
lean_inc(x_102);
lean_dec(x_92);
x_103 = l_Lean_Expr_sort___override(x_102);
x_104 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_103, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_103);
x_7 = x_53;
x_8 = x_104;
goto block_16;
}
case 4:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_92, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_92, 1);
lean_inc(x_106);
lean_dec(x_92);
x_107 = lean_box(0);
switch (lean_obj_tag(x_105)) {
case 0:
{
lean_object* x_108; lean_object* x_109; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_108 = l_Lean_Expr_const___override(x_107, x_106);
x_109 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_108, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_108);
x_7 = x_53;
x_8 = x_109;
goto block_16;
}
case 1:
{
lean_object* x_110; 
x_110 = lean_ctor_get(x_105, 0);
lean_inc(x_110);
switch (lean_obj_tag(x_110)) {
case 0:
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_111 = lean_ctor_get(x_105, 1);
lean_inc(x_111);
lean_dec(x_105);
x_112 = l_Lean_Name_str___override(x_107, x_111);
x_113 = l_Lean_Expr_const___override(x_112, x_106);
x_114 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_113, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_113);
x_7 = x_53;
x_8 = x_114;
goto block_16;
}
case 1:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_115 = lean_ctor_get(x_105, 1);
lean_inc(x_115);
lean_dec(x_105);
x_116 = lean_ctor_get(x_110, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_110, 1);
lean_inc(x_117);
lean_dec(x_110);
lean_inc(x_117);
x_118 = l_Lean_Name_str___override(x_107, x_117);
switch (lean_obj_tag(x_116)) {
case 0:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_117);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_119 = l_Lean_Name_str___override(x_118, x_115);
x_120 = l_Lean_Expr_const___override(x_119, x_106);
x_121 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_120, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_120);
x_7 = x_53;
x_8 = x_121;
goto block_16;
}
case 1:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_118);
x_122 = lean_ctor_get(x_116, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_116, 1);
lean_inc(x_123);
lean_dec(x_116);
lean_inc(x_123);
x_124 = l_Lean_Name_str___override(x_107, x_123);
lean_inc(x_117);
x_125 = l_Lean_Name_str___override(x_124, x_117);
switch (lean_obj_tag(x_122)) {
case 0:
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; 
lean_dec(x_123);
lean_dec(x_117);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_126 = l_Lean_Name_str___override(x_125, x_115);
x_127 = l_Lean_Expr_const___override(x_126, x_106);
x_128 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_127, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_127);
x_7 = x_53;
x_8 = x_128;
goto block_16;
}
case 1:
{
lean_object* x_129; 
lean_dec(x_125);
x_129 = lean_ctor_get(x_122, 0);
lean_inc(x_129);
switch (lean_obj_tag(x_129)) {
case 0:
{
lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_130 = lean_ctor_get(x_122, 1);
lean_inc(x_130);
lean_dec(x_122);
x_131 = lean_mk_string_unchecked("Lean", 4, 4);
x_132 = lean_string_dec_eq(x_130, x_131);
if (x_132 == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_131);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_133 = l_Lean_Name_str___override(x_107, x_130);
x_134 = l_Lean_Name_str___override(x_133, x_123);
x_135 = l_Lean_Name_str___override(x_134, x_117);
x_136 = l_Lean_Name_str___override(x_135, x_115);
x_137 = l_Lean_Expr_const___override(x_136, x_106);
x_138 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_137, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_137);
x_7 = x_53;
x_8 = x_138;
goto block_16;
}
else
{
lean_object* x_139; uint8_t x_140; 
lean_dec(x_130);
x_139 = lean_mk_string_unchecked("Meta", 4, 4);
x_140 = lean_string_dec_eq(x_123, x_139);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; 
lean_dec(x_139);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_141 = l_Lean_Name_str___override(x_107, x_131);
x_142 = l_Lean_Name_str___override(x_141, x_123);
x_143 = l_Lean_Name_str___override(x_142, x_117);
x_144 = l_Lean_Name_str___override(x_143, x_115);
x_145 = l_Lean_Expr_const___override(x_144, x_106);
x_146 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_145, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_145);
x_7 = x_53;
x_8 = x_146;
goto block_16;
}
else
{
lean_object* x_147; uint8_t x_148; 
lean_dec(x_123);
x_147 = lean_mk_string_unchecked("Simp", 4, 4);
x_148 = lean_string_dec_eq(x_117, x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; 
lean_dec(x_147);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_149 = l_Lean_Name_str___override(x_107, x_131);
x_150 = l_Lean_Name_str___override(x_149, x_139);
x_151 = l_Lean_Name_str___override(x_150, x_117);
x_152 = l_Lean_Name_str___override(x_151, x_115);
x_153 = l_Lean_Expr_const___override(x_152, x_106);
x_154 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_153, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_153);
x_7 = x_53;
x_8 = x_154;
goto block_16;
}
else
{
lean_object* x_155; uint8_t x_156; 
lean_dec(x_117);
x_155 = lean_mk_string_unchecked("Simproc", 7, 7);
x_156 = lean_string_dec_eq(x_115, x_155);
if (x_156 == 0)
{
lean_object* x_157; uint8_t x_158; 
x_157 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_158 = lean_string_dec_eq(x_115, x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_157);
lean_dec(x_155);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_159 = l_Lean_Name_str___override(x_107, x_131);
x_160 = l_Lean_Name_str___override(x_159, x_139);
x_161 = l_Lean_Name_str___override(x_160, x_147);
x_162 = l_Lean_Name_str___override(x_161, x_115);
x_163 = l_Lean_Expr_const___override(x_162, x_106);
x_164 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_163, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_163);
x_7 = x_53;
x_8 = x_164;
goto block_16;
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_115);
lean_dec(x_106);
x_165 = lean_mk_string_unchecked("Sum", 3, 3);
x_166 = lean_mk_string_unchecked("inr", 3, 3);
x_167 = l_Lean_Name_mkStr2(x_165, x_166);
x_168 = l_Lean_Level_ofNat(x_33);
x_169 = lean_box(0);
lean_inc(x_168);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_169);
lean_ctor_set(x_51, 0, x_168);
x_170 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_170, 0, x_168);
lean_ctor_set(x_170, 1, x_51);
x_171 = l_Lean_Expr_const___override(x_167, x_170);
lean_inc(x_147);
lean_inc(x_139);
lean_inc(x_131);
x_172 = l_Lean_Name_mkStr4(x_131, x_139, x_147, x_155);
x_173 = l_Lean_Expr_const___override(x_172, x_169);
x_174 = l_Lean_Name_mkStr4(x_131, x_139, x_147, x_157);
x_175 = l_Lean_Expr_const___override(x_174, x_169);
lean_inc(x_1);
x_176 = l_Lean_Expr_const___override(x_1, x_169);
x_177 = l_Lean_mkApp3(x_171, x_173, x_175, x_176);
x_178 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(x_3, x_1, x_21, x_177, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_85);
x_7 = x_53;
x_8 = x_178;
goto block_16;
}
}
else
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
lean_dec(x_115);
lean_dec(x_106);
x_179 = lean_mk_string_unchecked("Sum", 3, 3);
x_180 = lean_mk_string_unchecked("inl", 3, 3);
x_181 = l_Lean_Name_mkStr2(x_179, x_180);
x_182 = l_Lean_Level_ofNat(x_33);
x_183 = lean_box(0);
lean_inc(x_182);
lean_ctor_set_tag(x_51, 1);
lean_ctor_set(x_51, 1, x_183);
lean_ctor_set(x_51, 0, x_182);
x_184 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_51);
x_185 = l_Lean_Expr_const___override(x_181, x_184);
lean_inc(x_147);
lean_inc(x_139);
lean_inc(x_131);
x_186 = l_Lean_Name_mkStr4(x_131, x_139, x_147, x_155);
x_187 = l_Lean_Expr_const___override(x_186, x_183);
x_188 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_189 = l_Lean_Name_mkStr4(x_131, x_139, x_147, x_188);
x_190 = l_Lean_Expr_const___override(x_189, x_183);
lean_inc(x_1);
x_191 = l_Lean_Expr_const___override(x_1, x_183);
x_192 = l_Lean_mkApp3(x_185, x_187, x_190, x_191);
x_193 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(x_3, x_1, x_21, x_192, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_85);
x_7 = x_53;
x_8 = x_193;
goto block_16;
}
}
}
}
}
case 1:
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_194 = lean_ctor_get(x_122, 1);
lean_inc(x_194);
lean_dec(x_122);
x_195 = lean_ctor_get(x_129, 0);
lean_inc(x_195);
x_196 = lean_ctor_get(x_129, 1);
lean_inc(x_196);
lean_dec(x_129);
x_197 = l_Lean_Name_str___override(x_195, x_196);
x_198 = l_Lean_Name_str___override(x_197, x_194);
x_199 = l_Lean_Name_str___override(x_198, x_123);
x_200 = l_Lean_Name_str___override(x_199, x_117);
x_201 = l_Lean_Name_str___override(x_200, x_115);
x_202 = l_Lean_Expr_const___override(x_201, x_106);
x_203 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_202, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_202);
x_7 = x_53;
x_8 = x_203;
goto block_16;
}
default: 
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_204 = lean_ctor_get(x_122, 1);
lean_inc(x_204);
lean_dec(x_122);
x_205 = lean_ctor_get(x_129, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_129, 1);
lean_inc(x_206);
lean_dec(x_129);
x_207 = l_Lean_Name_num___override(x_205, x_206);
x_208 = l_Lean_Name_str___override(x_207, x_204);
x_209 = l_Lean_Name_str___override(x_208, x_123);
x_210 = l_Lean_Name_str___override(x_209, x_117);
x_211 = l_Lean_Name_str___override(x_210, x_115);
x_212 = l_Lean_Expr_const___override(x_211, x_106);
x_213 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_212, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_212);
x_7 = x_53;
x_8 = x_213;
goto block_16;
}
}
}
default: 
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
lean_dec(x_125);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_214 = lean_ctor_get(x_122, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_122, 1);
lean_inc(x_215);
lean_dec(x_122);
x_216 = l_Lean_Name_num___override(x_214, x_215);
x_217 = l_Lean_Name_str___override(x_216, x_123);
x_218 = l_Lean_Name_str___override(x_217, x_117);
x_219 = l_Lean_Name_str___override(x_218, x_115);
x_220 = l_Lean_Expr_const___override(x_219, x_106);
x_221 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_220, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_220);
x_7 = x_53;
x_8 = x_221;
goto block_16;
}
}
}
default: 
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; 
lean_dec(x_118);
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_222 = lean_ctor_get(x_116, 0);
lean_inc(x_222);
x_223 = lean_ctor_get(x_116, 1);
lean_inc(x_223);
lean_dec(x_116);
x_224 = l_Lean_Name_num___override(x_222, x_223);
x_225 = l_Lean_Name_str___override(x_224, x_117);
x_226 = l_Lean_Name_str___override(x_225, x_115);
x_227 = l_Lean_Expr_const___override(x_226, x_106);
x_228 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_227, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_227);
x_7 = x_53;
x_8 = x_228;
goto block_16;
}
}
}
default: 
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_229 = lean_ctor_get(x_105, 1);
lean_inc(x_229);
lean_dec(x_105);
x_230 = lean_ctor_get(x_110, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_110, 1);
lean_inc(x_231);
lean_dec(x_110);
x_232 = l_Lean_Name_num___override(x_230, x_231);
x_233 = l_Lean_Name_str___override(x_232, x_229);
x_234 = l_Lean_Expr_const___override(x_233, x_106);
x_235 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_234, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_234);
x_7 = x_53;
x_8 = x_235;
goto block_16;
}
}
}
default: 
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_236 = lean_ctor_get(x_105, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_105, 1);
lean_inc(x_237);
lean_dec(x_105);
x_238 = l_Lean_Name_num___override(x_236, x_237);
x_239 = l_Lean_Expr_const___override(x_238, x_106);
x_240 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_239, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_239);
x_7 = x_53;
x_8 = x_240;
goto block_16;
}
}
}
case 5:
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_241 = lean_ctor_get(x_92, 0);
lean_inc(x_241);
x_242 = lean_ctor_get(x_92, 1);
lean_inc(x_242);
lean_dec(x_92);
x_243 = l_Lean_Expr_app___override(x_241, x_242);
x_244 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_243, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_243);
x_7 = x_53;
x_8 = x_244;
goto block_16;
}
case 6:
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; uint8_t x_248; lean_object* x_249; lean_object* x_250; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_245 = lean_ctor_get(x_92, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_92, 1);
lean_inc(x_246);
x_247 = lean_ctor_get(x_92, 2);
lean_inc(x_247);
x_248 = lean_ctor_get_uint8(x_92, sizeof(void*)*3 + 8);
lean_dec(x_92);
x_249 = l_Lean_Expr_lam___override(x_245, x_246, x_247, x_248);
x_250 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_249, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_249);
x_7 = x_53;
x_8 = x_250;
goto block_16;
}
case 7:
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; uint8_t x_254; lean_object* x_255; lean_object* x_256; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_251 = lean_ctor_get(x_92, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_92, 1);
lean_inc(x_252);
x_253 = lean_ctor_get(x_92, 2);
lean_inc(x_253);
x_254 = lean_ctor_get_uint8(x_92, sizeof(void*)*3 + 8);
lean_dec(x_92);
x_255 = l_Lean_Expr_forallE___override(x_251, x_252, x_253, x_254);
x_256 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_255, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_255);
x_7 = x_53;
x_8 = x_256;
goto block_16;
}
case 8:
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_257 = lean_ctor_get(x_92, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_92, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_92, 2);
lean_inc(x_259);
x_260 = lean_ctor_get(x_92, 3);
lean_inc(x_260);
x_261 = lean_ctor_get_uint8(x_92, sizeof(void*)*4 + 8);
lean_dec(x_92);
x_262 = l_Lean_Expr_letE___override(x_257, x_258, x_259, x_260, x_261);
x_263 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_262, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_262);
x_7 = x_53;
x_8 = x_263;
goto block_16;
}
case 9:
{
lean_object* x_264; lean_object* x_265; lean_object* x_266; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_264 = lean_ctor_get(x_92, 0);
lean_inc(x_264);
lean_dec(x_92);
x_265 = l_Lean_Expr_lit___override(x_264);
x_266 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_265, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_265);
x_7 = x_53;
x_8 = x_266;
goto block_16;
}
case 10:
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_267 = lean_ctor_get(x_92, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_92, 1);
lean_inc(x_268);
lean_dec(x_92);
x_269 = l_Lean_Expr_mdata___override(x_267, x_268);
x_270 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_269, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_269);
x_7 = x_53;
x_8 = x_270;
goto block_16;
}
default: 
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
lean_free_object(x_51);
lean_dec(x_3);
lean_dec(x_1);
x_271 = lean_ctor_get(x_92, 0);
lean_inc(x_271);
x_272 = lean_ctor_get(x_92, 1);
lean_inc(x_272);
x_273 = lean_ctor_get(x_92, 2);
lean_inc(x_273);
lean_dec(x_92);
x_274 = l_Lean_Expr_proj___override(x_271, x_272, x_273);
x_275 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_274, x_85, x_53, x_4, x_5, x_91);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_85);
lean_dec(x_274);
x_7 = x_53;
x_8 = x_275;
goto block_16;
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_85);
lean_free_object(x_51);
lean_dec(x_53);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_89);
if (x_276 == 0)
{
return x_89;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_89, 0);
x_278 = lean_ctor_get(x_89, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_89);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
else
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; uint8_t x_290; uint8_t x_291; uint8_t x_292; uint8_t x_293; uint8_t x_294; uint8_t x_295; uint8_t x_296; uint8_t x_297; uint8_t x_298; uint8_t x_299; uint8_t x_300; uint8_t x_301; uint8_t x_302; uint8_t x_303; uint8_t x_304; uint8_t x_305; uint8_t x_306; uint64_t x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; uint8_t x_314; uint8_t x_315; lean_object* x_316; 
x_280 = lean_ctor_get(x_51, 0);
x_281 = lean_ctor_get(x_51, 1);
lean_inc(x_281);
lean_inc(x_280);
lean_dec(x_51);
x_282 = lean_box(1);
x_283 = lean_box(0);
x_284 = lean_box(2);
x_285 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_285, 0, x_23);
x_286 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_286, 0, x_32);
lean_ctor_set(x_286, 1, x_31);
lean_ctor_set(x_286, 2, x_33);
lean_ctor_set(x_286, 3, x_33);
lean_ctor_set_usize(x_286, 4, x_26);
x_287 = lean_box(0);
x_288 = lean_alloc_ctor(0, 0, 18);
x_289 = lean_unbox(x_287);
lean_ctor_set_uint8(x_288, 0, x_289);
x_290 = lean_unbox(x_287);
lean_ctor_set_uint8(x_288, 1, x_290);
x_291 = lean_unbox(x_287);
lean_ctor_set_uint8(x_288, 2, x_291);
x_292 = lean_unbox(x_287);
lean_ctor_set_uint8(x_288, 3, x_292);
x_293 = lean_unbox(x_287);
lean_ctor_set_uint8(x_288, 4, x_293);
x_294 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 5, x_294);
x_295 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 6, x_295);
x_296 = lean_unbox(x_287);
lean_ctor_set_uint8(x_288, 7, x_296);
x_297 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 8, x_297);
x_298 = lean_unbox(x_282);
lean_ctor_set_uint8(x_288, 9, x_298);
x_299 = lean_unbox(x_283);
lean_ctor_set_uint8(x_288, 10, x_299);
x_300 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 11, x_300);
x_301 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 12, x_301);
x_302 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 13, x_302);
x_303 = lean_unbox(x_284);
lean_ctor_set_uint8(x_288, 14, x_303);
x_304 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 15, x_304);
x_305 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 16, x_305);
x_306 = lean_unbox(x_20);
lean_ctor_set_uint8(x_288, 17, x_306);
x_307 = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(x_288);
x_308 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_308, 0, x_285);
lean_ctor_set(x_308, 1, x_286);
lean_ctor_set(x_308, 2, x_22);
x_309 = lean_mk_empty_array_with_capacity(x_33);
x_310 = lean_box(0);
x_311 = lean_box(0);
x_312 = lean_alloc_ctor(0, 7, 11);
lean_ctor_set(x_312, 0, x_288);
lean_ctor_set(x_312, 1, x_22);
lean_ctor_set(x_312, 2, x_308);
lean_ctor_set(x_312, 3, x_309);
lean_ctor_set(x_312, 4, x_310);
lean_ctor_set(x_312, 5, x_33);
lean_ctor_set(x_312, 6, x_311);
lean_ctor_set_uint64(x_312, sizeof(void*)*7, x_307);
x_313 = lean_unbox(x_287);
lean_ctor_set_uint8(x_312, sizeof(void*)*7 + 8, x_313);
x_314 = lean_unbox(x_287);
lean_ctor_set_uint8(x_312, sizeof(void*)*7 + 9, x_314);
x_315 = lean_unbox(x_287);
lean_ctor_set_uint8(x_312, sizeof(void*)*7 + 10, x_315);
lean_inc(x_1);
x_316 = l_Lean_getConstInfo___at___Lean_Meta_mkConstWithFreshMVarLevels_spec__0(x_1, x_312, x_280, x_4, x_5, x_281);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_317 = lean_ctor_get(x_316, 0);
lean_inc(x_317);
x_318 = lean_ctor_get(x_316, 1);
lean_inc(x_318);
lean_dec(x_316);
x_319 = l_Lean_ConstantInfo_type(x_317);
lean_dec(x_317);
switch (lean_obj_tag(x_319)) {
case 0:
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; 
lean_dec(x_3);
lean_dec(x_1);
x_320 = lean_ctor_get(x_319, 0);
lean_inc(x_320);
lean_dec(x_319);
x_321 = l_Lean_Expr_bvar___override(x_320);
x_322 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_321, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_321);
x_7 = x_280;
x_8 = x_322;
goto block_16;
}
case 1:
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; 
lean_dec(x_3);
lean_dec(x_1);
x_323 = lean_ctor_get(x_319, 0);
lean_inc(x_323);
lean_dec(x_319);
x_324 = l_Lean_Expr_fvar___override(x_323);
x_325 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_324, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_324);
x_7 = x_280;
x_8 = x_325;
goto block_16;
}
case 2:
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
lean_dec(x_3);
lean_dec(x_1);
x_326 = lean_ctor_get(x_319, 0);
lean_inc(x_326);
lean_dec(x_319);
x_327 = l_Lean_Expr_mvar___override(x_326);
x_328 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_327, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_327);
x_7 = x_280;
x_8 = x_328;
goto block_16;
}
case 3:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_3);
lean_dec(x_1);
x_329 = lean_ctor_get(x_319, 0);
lean_inc(x_329);
lean_dec(x_319);
x_330 = l_Lean_Expr_sort___override(x_329);
x_331 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_330, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_330);
x_7 = x_280;
x_8 = x_331;
goto block_16;
}
case 4:
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; 
x_332 = lean_ctor_get(x_319, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_319, 1);
lean_inc(x_333);
lean_dec(x_319);
x_334 = lean_box(0);
switch (lean_obj_tag(x_332)) {
case 0:
{
lean_object* x_335; lean_object* x_336; 
lean_dec(x_3);
lean_dec(x_1);
x_335 = l_Lean_Expr_const___override(x_334, x_333);
x_336 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_335, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_335);
x_7 = x_280;
x_8 = x_336;
goto block_16;
}
case 1:
{
lean_object* x_337; 
x_337 = lean_ctor_get(x_332, 0);
lean_inc(x_337);
switch (lean_obj_tag(x_337)) {
case 0:
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
lean_dec(x_3);
lean_dec(x_1);
x_338 = lean_ctor_get(x_332, 1);
lean_inc(x_338);
lean_dec(x_332);
x_339 = l_Lean_Name_str___override(x_334, x_338);
x_340 = l_Lean_Expr_const___override(x_339, x_333);
x_341 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_340, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_340);
x_7 = x_280;
x_8 = x_341;
goto block_16;
}
case 1:
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; 
x_342 = lean_ctor_get(x_332, 1);
lean_inc(x_342);
lean_dec(x_332);
x_343 = lean_ctor_get(x_337, 0);
lean_inc(x_343);
x_344 = lean_ctor_get(x_337, 1);
lean_inc(x_344);
lean_dec(x_337);
lean_inc(x_344);
x_345 = l_Lean_Name_str___override(x_334, x_344);
switch (lean_obj_tag(x_343)) {
case 0:
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; 
lean_dec(x_344);
lean_dec(x_3);
lean_dec(x_1);
x_346 = l_Lean_Name_str___override(x_345, x_342);
x_347 = l_Lean_Expr_const___override(x_346, x_333);
x_348 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_347, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_347);
x_7 = x_280;
x_8 = x_348;
goto block_16;
}
case 1:
{
lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_345);
x_349 = lean_ctor_get(x_343, 0);
lean_inc(x_349);
x_350 = lean_ctor_get(x_343, 1);
lean_inc(x_350);
lean_dec(x_343);
lean_inc(x_350);
x_351 = l_Lean_Name_str___override(x_334, x_350);
lean_inc(x_344);
x_352 = l_Lean_Name_str___override(x_351, x_344);
switch (lean_obj_tag(x_349)) {
case 0:
{
lean_object* x_353; lean_object* x_354; lean_object* x_355; 
lean_dec(x_350);
lean_dec(x_344);
lean_dec(x_3);
lean_dec(x_1);
x_353 = l_Lean_Name_str___override(x_352, x_342);
x_354 = l_Lean_Expr_const___override(x_353, x_333);
x_355 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_354, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_354);
x_7 = x_280;
x_8 = x_355;
goto block_16;
}
case 1:
{
lean_object* x_356; 
lean_dec(x_352);
x_356 = lean_ctor_get(x_349, 0);
lean_inc(x_356);
switch (lean_obj_tag(x_356)) {
case 0:
{
lean_object* x_357; lean_object* x_358; uint8_t x_359; 
x_357 = lean_ctor_get(x_349, 1);
lean_inc(x_357);
lean_dec(x_349);
x_358 = lean_mk_string_unchecked("Lean", 4, 4);
x_359 = lean_string_dec_eq(x_357, x_358);
if (x_359 == 0)
{
lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; 
lean_dec(x_358);
lean_dec(x_3);
lean_dec(x_1);
x_360 = l_Lean_Name_str___override(x_334, x_357);
x_361 = l_Lean_Name_str___override(x_360, x_350);
x_362 = l_Lean_Name_str___override(x_361, x_344);
x_363 = l_Lean_Name_str___override(x_362, x_342);
x_364 = l_Lean_Expr_const___override(x_363, x_333);
x_365 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_364, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_364);
x_7 = x_280;
x_8 = x_365;
goto block_16;
}
else
{
lean_object* x_366; uint8_t x_367; 
lean_dec(x_357);
x_366 = lean_mk_string_unchecked("Meta", 4, 4);
x_367 = lean_string_dec_eq(x_350, x_366);
if (x_367 == 0)
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; 
lean_dec(x_366);
lean_dec(x_3);
lean_dec(x_1);
x_368 = l_Lean_Name_str___override(x_334, x_358);
x_369 = l_Lean_Name_str___override(x_368, x_350);
x_370 = l_Lean_Name_str___override(x_369, x_344);
x_371 = l_Lean_Name_str___override(x_370, x_342);
x_372 = l_Lean_Expr_const___override(x_371, x_333);
x_373 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_372, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_372);
x_7 = x_280;
x_8 = x_373;
goto block_16;
}
else
{
lean_object* x_374; uint8_t x_375; 
lean_dec(x_350);
x_374 = lean_mk_string_unchecked("Simp", 4, 4);
x_375 = lean_string_dec_eq(x_344, x_374);
if (x_375 == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_374);
lean_dec(x_3);
lean_dec(x_1);
x_376 = l_Lean_Name_str___override(x_334, x_358);
x_377 = l_Lean_Name_str___override(x_376, x_366);
x_378 = l_Lean_Name_str___override(x_377, x_344);
x_379 = l_Lean_Name_str___override(x_378, x_342);
x_380 = l_Lean_Expr_const___override(x_379, x_333);
x_381 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_380, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_380);
x_7 = x_280;
x_8 = x_381;
goto block_16;
}
else
{
lean_object* x_382; uint8_t x_383; 
lean_dec(x_344);
x_382 = lean_mk_string_unchecked("Simproc", 7, 7);
x_383 = lean_string_dec_eq(x_342, x_382);
if (x_383 == 0)
{
lean_object* x_384; uint8_t x_385; 
x_384 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_385 = lean_string_dec_eq(x_342, x_384);
if (x_385 == 0)
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
lean_dec(x_384);
lean_dec(x_382);
lean_dec(x_3);
lean_dec(x_1);
x_386 = l_Lean_Name_str___override(x_334, x_358);
x_387 = l_Lean_Name_str___override(x_386, x_366);
x_388 = l_Lean_Name_str___override(x_387, x_374);
x_389 = l_Lean_Name_str___override(x_388, x_342);
x_390 = l_Lean_Expr_const___override(x_389, x_333);
x_391 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_390, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_390);
x_7 = x_280;
x_8 = x_391;
goto block_16;
}
else
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
lean_dec(x_342);
lean_dec(x_333);
x_392 = lean_mk_string_unchecked("Sum", 3, 3);
x_393 = lean_mk_string_unchecked("inr", 3, 3);
x_394 = l_Lean_Name_mkStr2(x_392, x_393);
x_395 = l_Lean_Level_ofNat(x_33);
x_396 = lean_box(0);
lean_inc(x_395);
x_397 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_397, 0, x_395);
lean_ctor_set(x_397, 1, x_396);
x_398 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_398, 0, x_395);
lean_ctor_set(x_398, 1, x_397);
x_399 = l_Lean_Expr_const___override(x_394, x_398);
lean_inc(x_374);
lean_inc(x_366);
lean_inc(x_358);
x_400 = l_Lean_Name_mkStr4(x_358, x_366, x_374, x_382);
x_401 = l_Lean_Expr_const___override(x_400, x_396);
x_402 = l_Lean_Name_mkStr4(x_358, x_366, x_374, x_384);
x_403 = l_Lean_Expr_const___override(x_402, x_396);
lean_inc(x_1);
x_404 = l_Lean_Expr_const___override(x_1, x_396);
x_405 = l_Lean_mkApp3(x_399, x_401, x_403, x_404);
x_406 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(x_3, x_1, x_21, x_405, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_312);
x_7 = x_280;
x_8 = x_406;
goto block_16;
}
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_342);
lean_dec(x_333);
x_407 = lean_mk_string_unchecked("Sum", 3, 3);
x_408 = lean_mk_string_unchecked("inl", 3, 3);
x_409 = l_Lean_Name_mkStr2(x_407, x_408);
x_410 = l_Lean_Level_ofNat(x_33);
x_411 = lean_box(0);
lean_inc(x_410);
x_412 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_413, 0, x_410);
lean_ctor_set(x_413, 1, x_412);
x_414 = l_Lean_Expr_const___override(x_409, x_413);
lean_inc(x_374);
lean_inc(x_366);
lean_inc(x_358);
x_415 = l_Lean_Name_mkStr4(x_358, x_366, x_374, x_382);
x_416 = l_Lean_Expr_const___override(x_415, x_411);
x_417 = lean_mk_string_unchecked("DSimproc", 8, 8);
x_418 = l_Lean_Name_mkStr4(x_358, x_366, x_374, x_417);
x_419 = l_Lean_Expr_const___override(x_418, x_411);
lean_inc(x_1);
x_420 = l_Lean_Expr_const___override(x_1, x_411);
x_421 = l_Lean_mkApp3(x_414, x_416, x_419, x_420);
x_422 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(x_3, x_1, x_21, x_421, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_312);
x_7 = x_280;
x_8 = x_422;
goto block_16;
}
}
}
}
}
case 1:
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_3);
lean_dec(x_1);
x_423 = lean_ctor_get(x_349, 1);
lean_inc(x_423);
lean_dec(x_349);
x_424 = lean_ctor_get(x_356, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_356, 1);
lean_inc(x_425);
lean_dec(x_356);
x_426 = l_Lean_Name_str___override(x_424, x_425);
x_427 = l_Lean_Name_str___override(x_426, x_423);
x_428 = l_Lean_Name_str___override(x_427, x_350);
x_429 = l_Lean_Name_str___override(x_428, x_344);
x_430 = l_Lean_Name_str___override(x_429, x_342);
x_431 = l_Lean_Expr_const___override(x_430, x_333);
x_432 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_431, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_431);
x_7 = x_280;
x_8 = x_432;
goto block_16;
}
default: 
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; 
lean_dec(x_3);
lean_dec(x_1);
x_433 = lean_ctor_get(x_349, 1);
lean_inc(x_433);
lean_dec(x_349);
x_434 = lean_ctor_get(x_356, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_356, 1);
lean_inc(x_435);
lean_dec(x_356);
x_436 = l_Lean_Name_num___override(x_434, x_435);
x_437 = l_Lean_Name_str___override(x_436, x_433);
x_438 = l_Lean_Name_str___override(x_437, x_350);
x_439 = l_Lean_Name_str___override(x_438, x_344);
x_440 = l_Lean_Name_str___override(x_439, x_342);
x_441 = l_Lean_Expr_const___override(x_440, x_333);
x_442 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_441, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_441);
x_7 = x_280;
x_8 = x_442;
goto block_16;
}
}
}
default: 
{
lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_352);
lean_dec(x_3);
lean_dec(x_1);
x_443 = lean_ctor_get(x_349, 0);
lean_inc(x_443);
x_444 = lean_ctor_get(x_349, 1);
lean_inc(x_444);
lean_dec(x_349);
x_445 = l_Lean_Name_num___override(x_443, x_444);
x_446 = l_Lean_Name_str___override(x_445, x_350);
x_447 = l_Lean_Name_str___override(x_446, x_344);
x_448 = l_Lean_Name_str___override(x_447, x_342);
x_449 = l_Lean_Expr_const___override(x_448, x_333);
x_450 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_449, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_449);
x_7 = x_280;
x_8 = x_450;
goto block_16;
}
}
}
default: 
{
lean_object* x_451; lean_object* x_452; lean_object* x_453; lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; 
lean_dec(x_345);
lean_dec(x_3);
lean_dec(x_1);
x_451 = lean_ctor_get(x_343, 0);
lean_inc(x_451);
x_452 = lean_ctor_get(x_343, 1);
lean_inc(x_452);
lean_dec(x_343);
x_453 = l_Lean_Name_num___override(x_451, x_452);
x_454 = l_Lean_Name_str___override(x_453, x_344);
x_455 = l_Lean_Name_str___override(x_454, x_342);
x_456 = l_Lean_Expr_const___override(x_455, x_333);
x_457 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_456, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_456);
x_7 = x_280;
x_8 = x_457;
goto block_16;
}
}
}
default: 
{
lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
lean_dec(x_3);
lean_dec(x_1);
x_458 = lean_ctor_get(x_332, 1);
lean_inc(x_458);
lean_dec(x_332);
x_459 = lean_ctor_get(x_337, 0);
lean_inc(x_459);
x_460 = lean_ctor_get(x_337, 1);
lean_inc(x_460);
lean_dec(x_337);
x_461 = l_Lean_Name_num___override(x_459, x_460);
x_462 = l_Lean_Name_str___override(x_461, x_458);
x_463 = l_Lean_Expr_const___override(x_462, x_333);
x_464 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_463, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_463);
x_7 = x_280;
x_8 = x_464;
goto block_16;
}
}
}
default: 
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; lean_object* x_469; 
lean_dec(x_3);
lean_dec(x_1);
x_465 = lean_ctor_get(x_332, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_332, 1);
lean_inc(x_466);
lean_dec(x_332);
x_467 = l_Lean_Name_num___override(x_465, x_466);
x_468 = l_Lean_Expr_const___override(x_467, x_333);
x_469 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_468, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_468);
x_7 = x_280;
x_8 = x_469;
goto block_16;
}
}
}
case 5:
{
lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; 
lean_dec(x_3);
lean_dec(x_1);
x_470 = lean_ctor_get(x_319, 0);
lean_inc(x_470);
x_471 = lean_ctor_get(x_319, 1);
lean_inc(x_471);
lean_dec(x_319);
x_472 = l_Lean_Expr_app___override(x_470, x_471);
x_473 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_472, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_472);
x_7 = x_280;
x_8 = x_473;
goto block_16;
}
case 6:
{
lean_object* x_474; lean_object* x_475; lean_object* x_476; uint8_t x_477; lean_object* x_478; lean_object* x_479; 
lean_dec(x_3);
lean_dec(x_1);
x_474 = lean_ctor_get(x_319, 0);
lean_inc(x_474);
x_475 = lean_ctor_get(x_319, 1);
lean_inc(x_475);
x_476 = lean_ctor_get(x_319, 2);
lean_inc(x_476);
x_477 = lean_ctor_get_uint8(x_319, sizeof(void*)*3 + 8);
lean_dec(x_319);
x_478 = l_Lean_Expr_lam___override(x_474, x_475, x_476, x_477);
x_479 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_478, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_478);
x_7 = x_280;
x_8 = x_479;
goto block_16;
}
case 7:
{
lean_object* x_480; lean_object* x_481; lean_object* x_482; uint8_t x_483; lean_object* x_484; lean_object* x_485; 
lean_dec(x_3);
lean_dec(x_1);
x_480 = lean_ctor_get(x_319, 0);
lean_inc(x_480);
x_481 = lean_ctor_get(x_319, 1);
lean_inc(x_481);
x_482 = lean_ctor_get(x_319, 2);
lean_inc(x_482);
x_483 = lean_ctor_get_uint8(x_319, sizeof(void*)*3 + 8);
lean_dec(x_319);
x_484 = l_Lean_Expr_forallE___override(x_480, x_481, x_482, x_483);
x_485 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_484, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_484);
x_7 = x_280;
x_8 = x_485;
goto block_16;
}
case 8:
{
lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; uint8_t x_490; lean_object* x_491; lean_object* x_492; 
lean_dec(x_3);
lean_dec(x_1);
x_486 = lean_ctor_get(x_319, 0);
lean_inc(x_486);
x_487 = lean_ctor_get(x_319, 1);
lean_inc(x_487);
x_488 = lean_ctor_get(x_319, 2);
lean_inc(x_488);
x_489 = lean_ctor_get(x_319, 3);
lean_inc(x_489);
x_490 = lean_ctor_get_uint8(x_319, sizeof(void*)*4 + 8);
lean_dec(x_319);
x_491 = l_Lean_Expr_letE___override(x_486, x_487, x_488, x_489, x_490);
x_492 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_491, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_491);
x_7 = x_280;
x_8 = x_492;
goto block_16;
}
case 9:
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; 
lean_dec(x_3);
lean_dec(x_1);
x_493 = lean_ctor_get(x_319, 0);
lean_inc(x_493);
lean_dec(x_319);
x_494 = l_Lean_Expr_lit___override(x_493);
x_495 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_494, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_494);
x_7 = x_280;
x_8 = x_495;
goto block_16;
}
case 10:
{
lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; 
lean_dec(x_3);
lean_dec(x_1);
x_496 = lean_ctor_get(x_319, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_319, 1);
lean_inc(x_497);
lean_dec(x_319);
x_498 = l_Lean_Expr_mdata___override(x_496, x_497);
x_499 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_498, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_498);
x_7 = x_280;
x_8 = x_499;
goto block_16;
}
default: 
{
lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; lean_object* x_504; 
lean_dec(x_3);
lean_dec(x_1);
x_500 = lean_ctor_get(x_319, 0);
lean_inc(x_500);
x_501 = lean_ctor_get(x_319, 1);
lean_inc(x_501);
x_502 = lean_ctor_get(x_319, 2);
lean_inc(x_502);
lean_dec(x_319);
x_503 = l_Lean_Expr_proj___override(x_500, x_501, x_502);
x_504 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_503, x_312, x_280, x_4, x_5, x_318);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_312);
lean_dec(x_503);
x_7 = x_280;
x_8 = x_504;
goto block_16;
}
}
}
else
{
lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; 
lean_dec(x_312);
lean_dec(x_280);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_505 = lean_ctor_get(x_316, 0);
lean_inc(x_505);
x_506 = lean_ctor_get(x_316, 1);
lean_inc(x_506);
if (lean_is_exclusive(x_316)) {
 lean_ctor_release(x_316, 0);
 lean_ctor_release(x_316, 1);
 x_507 = x_316;
} else {
 lean_dec_ref(x_316);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_3);
lean_dec(x_3);
x_11 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__0(x_1, x_2, x_10, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_6);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___lam__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("Not implemented yet, [-builtin_simproc]", 39, 39);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_mk_string_unchecked("addSimprocBuiltinAttr", 21, 21);
x_11 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_10);
x_12 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(x_4, x_5, x_11, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618____boxed), 4, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_str___override(x_3, x_4);
x_6 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("Simp", 4, 4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618____boxed), 9, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
lean_inc(x_8);
x_10 = l_Lean_Name_str___override(x_7, x_8);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_4);
x_16 = l_Lean_Name_str___override(x_15, x_6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = l_Lean_Name_str___override(x_18, x_8);
x_20 = lean_mk_string_unchecked("Simproc", 7, 7);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("_hyg", 4, 4);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_unsigned_to_nat(6618u);
x_25 = l_Lean_Name_num___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("simprocBuiltinAttr", 18, 18);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("Builtin simplification procedure", 32, 32);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_2);
x_33 = l_Lean_registerBuiltinAttribute(x_32, x_1);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_mk_string_unchecked("Not implemented yet, [-builtin_sevalproc]", 41, 41);
x_6 = l_Lean_stringToMessageData(x_5);
lean_dec(x_5);
x_7 = l_Lean_throwError___at___Lean_throwUnknownIdentifier___at___Lean_throwUnknownConstant___at___Lean_filterFieldList___at___Lean_realizeGlobalConstCore_spec__0_spec__2_spec__2_spec__2___redArg(x_6, x_2, x_3, x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, uint8_t x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_mk_string_unchecked("addSEvalprocBuiltinAttr", 23, 23);
x_11 = l_Lean_Name_mkStr4(x_1, x_2, x_3, x_10);
x_12 = l___private_Lean_Meta_Tactic_Simp_Simproc_0__Lean_Meta_Simp_addBuiltin(x_4, x_5, x_11, x_7, x_8, x_9);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; lean_object* x_32; lean_object* x_33; 
x_2 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693____boxed), 4, 0);
x_3 = lean_box(0);
x_4 = lean_mk_string_unchecked("Lean", 4, 4);
lean_inc(x_4);
x_5 = l_Lean_Name_str___override(x_3, x_4);
x_6 = lean_mk_string_unchecked("Meta", 4, 4);
lean_inc(x_6);
x_7 = l_Lean_Name_str___override(x_5, x_6);
x_8 = lean_mk_string_unchecked("Simp", 4, 4);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_4);
x_9 = lean_alloc_closure((void*)(l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693____boxed), 9, 3);
lean_closure_set(x_9, 0, x_4);
lean_closure_set(x_9, 1, x_6);
lean_closure_set(x_9, 2, x_8);
lean_inc(x_8);
x_10 = l_Lean_Name_str___override(x_7, x_8);
x_11 = lean_mk_string_unchecked("initFn", 6, 6);
x_12 = l_Lean_Name_str___override(x_10, x_11);
x_13 = lean_mk_string_unchecked("_@", 2, 2);
x_14 = l_Lean_Name_str___override(x_12, x_13);
x_15 = l_Lean_Name_str___override(x_14, x_4);
x_16 = l_Lean_Name_str___override(x_15, x_6);
x_17 = lean_mk_string_unchecked("Tactic", 6, 6);
x_18 = l_Lean_Name_str___override(x_16, x_17);
x_19 = l_Lean_Name_str___override(x_18, x_8);
x_20 = lean_mk_string_unchecked("Simproc", 7, 7);
x_21 = l_Lean_Name_str___override(x_19, x_20);
x_22 = lean_mk_string_unchecked("_hyg", 4, 4);
x_23 = l_Lean_Name_str___override(x_21, x_22);
x_24 = lean_unsigned_to_nat(6693u);
x_25 = l_Lean_Name_num___override(x_23, x_24);
x_26 = lean_mk_string_unchecked("sevalprocBuiltinAttr", 20, 20);
x_27 = l_Lean_Name_mkStr1(x_26);
x_28 = lean_mk_string_unchecked("Builtin symbolic evaluation procedure", 37, 37);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(x_30, 0, x_25);
lean_ctor_set(x_30, 1, x_27);
lean_ctor_set(x_30, 2, x_28);
x_31 = lean_unbox(x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*3, x_31);
x_32 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_2);
x_33 = l_Lean_registerBuiltinAttribute(x_32, x_1);
return x_33;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_initFn___lam__0____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693____boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_6);
lean_dec(x_6);
x_11 = l_Lean_Meta_Simp_initFn___lam__1____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(x_1, x_2, x_3, x_4, x_5, x_10, x_7, x_8, x_9);
lean_dec(x_5);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_Simp_simprocExtension;
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
x_15 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_Simp_simprocExtension;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_getSimprocs___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimprocs___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_getSimprocs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_st_ref_get(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_7 = lean_ctor_get(x_5, 0);
lean_inc(x_7);
lean_dec(x_5);
x_8 = l_Lean_Meta_Simp_simprocSEvalExtension;
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
x_15 = l_Lean_Meta_Simp_instInhabitedSimprocs;
x_16 = lean_ctor_get(x_13, 0);
lean_inc(x_16);
lean_dec(x_13);
x_17 = l_Lean_Meta_Simp_simprocSEvalExtension;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSEvalSimprocs___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSEvalSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_getSEvalSimprocs(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = l_Lean_Meta_Simp_simprocExtensionMapRef;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtensionCore_x3f___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; uint8_t x_4; 
x_2 = lean_mk_string_unchecked("simp", 4, 4);
x_3 = l_Lean_Name_mkStr1(x_2);
x_4 = lean_name_eq(x_1, x_3);
lean_dec(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_mk_string_unchecked("seval", 5, 5);
x_6 = l_Lean_Name_mkStr1(x_5);
x_7 = lean_name_eq(x_1, x_6);
lean_dec(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_mk_string_unchecked("_proc", 5, 5);
x_9 = lean_name_append_after(x_1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_1);
x_10 = lean_mk_string_unchecked("sevalprocAttr", 13, 13);
x_11 = l_Lean_Name_mkStr1(x_10);
return x_11;
}
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("simprocAttr", 11, 11);
x_13 = l_Lean_Name_mkStr1(x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_getSimprocExtension_x3f(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(x_1, x_2);
x_4 = lean_ctor_get(x_3, 0);
lean_inc(x_4);
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 1);
lean_inc(x_5);
lean_dec(x_3);
x_6 = l_Lean_Meta_Simp_simpAttrNameToSimprocAttrName(x_1);
x_7 = l_Lean_Meta_Simp_getSimprocExtensionCore_x3f(x_6, x_5);
lean_dec(x_6);
return x_7;
}
else
{
lean_dec(x_4);
lean_dec(x_1);
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = l_Lean_Meta_Simp_instInhabitedSimprocs;
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
x_15 = l_Lean_Meta_Simp_instInhabitedSimprocs;
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
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_1, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs___redArg(x_1, x_2, x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Simp_SimprocExtension_getSimprocs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Meta_Simp_SimprocExtension_getSimprocs(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_InitAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_DiscrTree(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Meta_Tactic_Simp_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Simp_Simproc(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ScopedEnvExtension(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_InitAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_DiscrTree(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Simp_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs = _init_l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedBuiltinSimprocs);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_59_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSimprocDeclsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSimprocDeclsRef);
lean_dec_ref(res);
}l_Lean_Meta_Simp_instInhabitedSimprocDecl = _init_l_Lean_Meta_Simp_instInhabitedSimprocDecl();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDecl);
l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState = _init_l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState();
lean_mark_persistent(l_Lean_Meta_Simp_instInhabitedSimprocDeclExtState);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_187_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocDeclExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocDeclExt);
lean_dec_ref(res);
}l_Lean_Meta_Simp_instBEqSimprocEntry = _init_l_Lean_Meta_Simp_instBEqSimprocEntry();
lean_mark_persistent(l_Lean_Meta_Simp_instBEqSimprocEntry);
l_Lean_Meta_Simp_instToFormatSimprocEntry = _init_l_Lean_Meta_Simp_instToFormatSimprocEntry();
lean_mark_persistent(l_Lean_Meta_Simp_instToFormatSimprocEntry);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1143_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSimprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSimprocsRef);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_1178_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_builtinSEvalprocsRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_builtinSEvalprocsRef);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5382_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocs = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocs);
lean_dec_ref(res);
}l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5717_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5717_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_5717_);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6000_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocExtensionMapRef = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocExtensionMapRef);
lean_dec_ref(res);
}l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6044_ = _init_l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6044_();
lean_mark_persistent(l___auto____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6044_);
if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6114_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocExtension);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6144_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Simp_simprocSEvalExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Simp_simprocSEvalExtension);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6618_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Meta_Simp_initFn____x40_Lean_Meta_Tactic_Simp_Simproc___hyg_6693_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
