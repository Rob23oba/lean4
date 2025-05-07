// Lean compiler output
// Module: Lean.Compiler.LCNF.FloatLetIn
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.FVarUtil Lean.Compiler.LCNF.PassManager Lean.Compiler.LCNF.Types
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_mix_hash(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision;
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161____boxed(lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg___boxed(lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63____boxed(lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16____boxed(lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2271_(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_attachCodeDecls(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_Name_hash___override(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Repr_addAppParen(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_CodeDecl_fvarId(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision;
lean_object* l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__11(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Compiler_LCNF_getType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_instInhabitedList(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint64_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; lean_object* x_3; uint64_t x_4; uint64_t x_5; uint64_t x_6; 
x_2 = lean_ctor_get(x_1, 0);
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_uint64_of_nat(x_3);
x_5 = l_Lean_Name_hash___override(x_2);
x_6 = lean_uint64_mix_hash(x_4, x_5);
return x_6;
}
case 1:
{
lean_object* x_7; uint64_t x_8; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_uint64_of_nat(x_7);
return x_8;
}
case 2:
{
lean_object* x_9; uint64_t x_10; 
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_uint64_of_nat(x_9);
return x_10;
}
default: 
{
lean_object* x_11; uint64_t x_12; 
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_uint64_of_nat(x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16____boxed(lean_object* x_1) {
_start:
{
uint64_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_1);
lean_dec(x_1);
x_3 = lean_box_uint64(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16____boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(lean_object* x_1, lean_object* x_2) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_name_eq(x_3, x_4);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_box(0);
x_7 = lean_unbox(x_6);
return x_7;
}
}
case 1:
{
if (lean_obj_tag(x_2) == 1)
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_box(1);
x_9 = lean_unbox(x_8);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_box(0);
x_11 = lean_unbox(x_10);
return x_11;
}
}
case 2:
{
if (lean_obj_tag(x_2) == 2)
{
lean_object* x_12; uint8_t x_13; 
x_12 = lean_box(1);
x_13 = lean_unbox(x_12);
return x_13;
}
else
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_box(0);
x_15 = lean_unbox(x_14);
return x_15;
}
}
default: 
{
if (lean_obj_tag(x_2) == 3)
{
lean_object* x_16; uint8_t x_17; 
x_16 = lean_box(1);
x_17 = lean_unbox(x_16);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
x_18 = lean_box(0);
x_19 = lean_unbox(x_18);
return x_19;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63____boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(0);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161_(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_12; lean_object* x_21; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_46; uint8_t x_47; 
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_31 = x_1;
} else {
 lean_dec_ref(x_1);
 x_31 = lean_box(0);
}
x_46 = lean_unsigned_to_nat(1024u);
x_47 = lean_nat_dec_le(x_46, x_2);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_unsigned_to_nat(2u);
x_49 = lean_nat_to_int(x_48);
x_32 = x_49;
goto block_45;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = lean_nat_to_int(x_50);
x_32 = x_51;
goto block_45;
}
block_45:
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; lean_object* x_44; 
x_33 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.arm", 42, 42);
if (lean_is_scalar(x_31)) {
 x_34 = lean_alloc_ctor(3, 1, 0);
} else {
 x_34 = x_31;
 lean_ctor_set_tag(x_34, 3);
}
lean_ctor_set(x_34, 0, x_33);
x_35 = lean_box(1);
x_36 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_36, 0, x_34);
lean_ctor_set(x_36, 1, x_35);
x_37 = lean_unsigned_to_nat(1024u);
x_38 = l_Lean_Name_reprPrec(x_30, x_37);
x_39 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_39, 0, x_36);
lean_ctor_set(x_39, 1, x_38);
x_40 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_40, 0, x_32);
lean_ctor_set(x_40, 1, x_39);
x_41 = lean_box(0);
x_42 = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(x_42, 0, x_40);
x_43 = lean_unbox(x_41);
lean_ctor_set_uint8(x_42, sizeof(void*)*1, x_43);
x_44 = l_Repr_addAppParen(x_42, x_2);
return x_44;
}
}
case 1:
{
lean_object* x_52; uint8_t x_53; 
x_52 = lean_unsigned_to_nat(1024u);
x_53 = lean_nat_dec_le(x_52, x_2);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_unsigned_to_nat(2u);
x_55 = lean_nat_to_int(x_54);
x_3 = x_55;
goto block_11;
}
else
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_unsigned_to_nat(1u);
x_57 = lean_nat_to_int(x_56);
x_3 = x_57;
goto block_11;
}
}
case 2:
{
lean_object* x_58; uint8_t x_59; 
x_58 = lean_unsigned_to_nat(1024u);
x_59 = lean_nat_dec_le(x_58, x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_unsigned_to_nat(2u);
x_61 = lean_nat_to_int(x_60);
x_12 = x_61;
goto block_20;
}
else
{
lean_object* x_62; lean_object* x_63; 
x_62 = lean_unsigned_to_nat(1u);
x_63 = lean_nat_to_int(x_62);
x_12 = x_63;
goto block_20;
}
}
default: 
{
lean_object* x_64; uint8_t x_65; 
x_64 = lean_unsigned_to_nat(1024u);
x_65 = lean_nat_dec_le(x_64, x_2);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; 
x_66 = lean_unsigned_to_nat(2u);
x_67 = lean_nat_to_int(x_66);
x_21 = x_67;
goto block_29;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_nat_to_int(x_68);
x_21 = x_69;
goto block_29;
}
}
}
block_11:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.default", 46, 46);
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
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.dont", 43, 43);
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
x_22 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FloatLetIn.Decision.unknown", 46, 46);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161____boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161_(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161____boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_ctor_get(x_1, 0);
lean_inc(x_2);
x_3 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
else
{
lean_object* x_4; 
x_4 = lean_box(1);
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_9, 0, x_1);
lean_ctor_set(x_9, 1, x_3);
x_10 = lean_apply_6(x_2, x_9, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_box(0);
x_8 = lean_apply_6(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_1, 2);
lean_inc(x_7);
x_8 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_7, x_5, x_6);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_8);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_8, 1);
x_12 = lean_ctor_get(x_8, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
lean_dec(x_1);
if (lean_obj_tag(x_14) == 2)
{
lean_object* x_15; lean_object* x_16; 
lean_free_object(x_8);
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_16 = l_Lean_Compiler_LCNF_getType(x_15, x_2, x_3, x_4, x_5, x_11);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_17, x_5, x_18);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_19, 0);
lean_dec(x_22);
lean_ctor_set(x_19, 0, x_13);
return x_19;
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_19, 1);
lean_inc(x_23);
lean_dec(x_19);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_13);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_20);
x_25 = !lean_is_exclusive(x_19);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_19, 0);
lean_dec(x_26);
x_27 = lean_box(1);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_dec(x_19);
x_29 = lean_box(1);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_29);
lean_ctor_set(x_30, 1, x_28);
return x_30;
}
}
}
else
{
uint8_t x_31; 
x_31 = !lean_is_exclusive(x_16);
if (x_31 == 0)
{
return x_16;
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_32 = lean_ctor_get(x_16, 0);
x_33 = lean_ctor_get(x_16, 1);
lean_inc(x_33);
lean_inc(x_32);
lean_dec(x_16);
x_34 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_33);
return x_34;
}
}
}
else
{
lean_dec(x_14);
lean_ctor_set(x_8, 0, x_13);
return x_8;
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_8, 1);
lean_inc(x_35);
lean_dec(x_8);
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_1, 3);
lean_inc(x_37);
lean_dec(x_1);
if (lean_obj_tag(x_37) == 2)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_ctor_get(x_37, 2);
lean_inc(x_38);
lean_dec(x_37);
x_39 = l_Lean_Compiler_LCNF_getType(x_38, x_2, x_3, x_4, x_5, x_35);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_isArrowClass_x3f___redArg(x_40, x_5, x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; 
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
if (lean_is_scalar(x_45)) {
 x_46 = lean_alloc_ctor(0, 2, 0);
} else {
 x_46 = x_45;
}
lean_ctor_set(x_46, 0, x_36);
lean_ctor_set(x_46, 1, x_44);
return x_46;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_43);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_48 = x_42;
} else {
 lean_dec_ref(x_42);
 x_48 = lean_box(0);
}
x_49 = lean_box(1);
if (lean_is_scalar(x_48)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_48;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_47);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_39, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_39, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_53 = x_39;
} else {
 lean_dec_ref(x_39);
 x_53 = lean_box(0);
}
if (lean_is_scalar(x_53)) {
 x_54 = lean_alloc_ctor(1, 2, 0);
} else {
 x_54 = x_53;
}
lean_ctor_set(x_54, 0, x_51);
lean_ctor_set(x_54, 1, x_52);
return x_54;
}
}
else
{
lean_object* x_55; 
lean_dec(x_37);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_35);
return x_55;
}
}
}
else
{
uint8_t x_56; 
lean_dec(x_9);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_8);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_8, 0);
lean_dec(x_57);
x_58 = lean_box(1);
lean_ctor_set(x_8, 0, x_58);
return x_8;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_8, 1);
lean_inc(x_59);
lean_dec(x_8);
x_60 = lean_box(1);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_59);
return x_61;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(x_1, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_14; uint8_t x_15; 
x_14 = lean_st_ref_get(x_3, x_4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_98; lean_object* x_99; uint64_t x_100; lean_object* x_101; uint64_t x_102; uint64_t x_103; uint64_t x_104; lean_object* x_105; uint64_t x_106; uint64_t x_107; uint64_t x_108; size_t x_109; size_t x_110; lean_object* x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; lean_object* x_116; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_98 = lean_ctor_get(x_16, 1);
lean_inc(x_98);
lean_dec(x_16);
x_99 = lean_array_get_size(x_98);
x_100 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
x_101 = lean_unsigned_to_nat(32u);
x_102 = lean_uint64_of_nat(x_101);
x_103 = lean_uint64_shift_right(x_100, x_102);
x_104 = lean_uint64_xor(x_100, x_103);
x_105 = lean_unsigned_to_nat(16u);
x_106 = lean_uint64_of_nat(x_105);
x_107 = lean_uint64_shift_right(x_104, x_106);
x_108 = lean_uint64_xor(x_104, x_107);
x_109 = lean_uint64_to_usize(x_108);
x_110 = lean_usize_of_nat(x_99);
lean_dec(x_99);
x_111 = lean_unsigned_to_nat(1u);
x_112 = lean_usize_of_nat(x_111);
x_113 = lean_usize_sub(x_110, x_112);
x_114 = lean_usize_land(x_109, x_113);
x_115 = lean_array_uget(x_98, x_114);
lean_dec(x_98);
x_116 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_2, x_115);
lean_dec(x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
lean_dec(x_2);
lean_dec(x_1);
x_117 = lean_box(0);
lean_ctor_set(x_14, 0, x_117);
return x_14;
}
else
{
lean_object* x_118; lean_object* x_119; uint8_t x_120; 
x_118 = lean_ctor_get(x_116, 0);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_box(3);
x_120 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_118, x_119);
if (x_120 == 0)
{
uint8_t x_121; 
x_121 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_118, x_1);
lean_dec(x_1);
lean_dec(x_118);
if (x_121 == 0)
{
lean_free_object(x_14);
goto block_97;
}
else
{
if (x_120 == 0)
{
lean_object* x_122; 
lean_dec(x_2);
x_122 = lean_box(0);
lean_ctor_set(x_14, 0, x_122);
return x_14;
}
else
{
lean_free_object(x_14);
goto block_97;
}
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_118);
lean_free_object(x_14);
x_123 = lean_st_ref_take(x_3, x_17);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
x_126 = !lean_is_exclusive(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_137; size_t x_138; size_t x_139; size_t x_140; lean_object* x_141; uint8_t x_142; 
x_127 = lean_ctor_get(x_124, 0);
x_128 = lean_ctor_get(x_124, 1);
x_129 = lean_box(0);
x_137 = lean_array_get_size(x_128);
x_138 = lean_usize_of_nat(x_137);
lean_dec(x_137);
x_139 = lean_usize_sub(x_138, x_112);
x_140 = lean_usize_land(x_109, x_139);
x_141 = lean_array_uget(x_128, x_140);
x_142 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_143 = lean_nat_add(x_127, x_111);
lean_dec(x_127);
x_144 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_144, 0, x_2);
lean_ctor_set(x_144, 1, x_1);
lean_ctor_set(x_144, 2, x_141);
x_145 = lean_array_uset(x_128, x_140, x_144);
x_146 = lean_unsigned_to_nat(2u);
x_147 = lean_nat_shiftl(x_143, x_146);
x_148 = lean_unsigned_to_nat(3u);
x_149 = lean_nat_div(x_147, x_148);
lean_dec(x_147);
x_150 = lean_array_get_size(x_145);
x_151 = lean_nat_dec_le(x_149, x_150);
lean_dec(x_150);
lean_dec(x_149);
if (x_151 == 0)
{
lean_object* x_152; 
x_152 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_145);
lean_ctor_set(x_124, 1, x_152);
lean_ctor_set(x_124, 0, x_143);
x_130 = x_124;
goto block_136;
}
else
{
lean_ctor_set(x_124, 1, x_145);
lean_ctor_set(x_124, 0, x_143);
x_130 = x_124;
goto block_136;
}
}
else
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_153 = lean_box(0);
x_154 = lean_array_uset(x_128, x_140, x_153);
x_155 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_1, x_141);
x_156 = lean_array_uset(x_154, x_140, x_155);
lean_ctor_set(x_124, 1, x_156);
x_130 = x_124;
goto block_136;
}
block_136:
{
lean_object* x_131; uint8_t x_132; 
x_131 = lean_st_ref_set(x_3, x_130, x_125);
x_132 = !lean_is_exclusive(x_131);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = lean_ctor_get(x_131, 0);
lean_dec(x_133);
lean_ctor_set(x_131, 0, x_129);
return x_131;
}
else
{
lean_object* x_134; lean_object* x_135; 
x_134 = lean_ctor_get(x_131, 1);
lean_inc(x_134);
lean_dec(x_131);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_134);
return x_135;
}
}
}
else
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_166; size_t x_167; size_t x_168; size_t x_169; lean_object* x_170; uint8_t x_171; 
x_157 = lean_ctor_get(x_124, 0);
x_158 = lean_ctor_get(x_124, 1);
lean_inc(x_158);
lean_inc(x_157);
lean_dec(x_124);
x_159 = lean_box(0);
x_166 = lean_array_get_size(x_158);
x_167 = lean_usize_of_nat(x_166);
lean_dec(x_166);
x_168 = lean_usize_sub(x_167, x_112);
x_169 = lean_usize_land(x_109, x_168);
x_170 = lean_array_uget(x_158, x_169);
x_171 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_170);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
x_172 = lean_nat_add(x_157, x_111);
lean_dec(x_157);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_2);
lean_ctor_set(x_173, 1, x_1);
lean_ctor_set(x_173, 2, x_170);
x_174 = lean_array_uset(x_158, x_169, x_173);
x_175 = lean_unsigned_to_nat(2u);
x_176 = lean_nat_shiftl(x_172, x_175);
x_177 = lean_unsigned_to_nat(3u);
x_178 = lean_nat_div(x_176, x_177);
lean_dec(x_176);
x_179 = lean_array_get_size(x_174);
x_180 = lean_nat_dec_le(x_178, x_179);
lean_dec(x_179);
lean_dec(x_178);
if (x_180 == 0)
{
lean_object* x_181; lean_object* x_182; 
x_181 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_174);
x_182 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_181);
x_160 = x_182;
goto block_165;
}
else
{
lean_object* x_183; 
x_183 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_183, 0, x_172);
lean_ctor_set(x_183, 1, x_174);
x_160 = x_183;
goto block_165;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; 
x_184 = lean_box(0);
x_185 = lean_array_uset(x_158, x_169, x_184);
x_186 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_1, x_170);
x_187 = lean_array_uset(x_185, x_169, x_186);
x_188 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_188, 0, x_157);
lean_ctor_set(x_188, 1, x_187);
x_160 = x_188;
goto block_165;
}
block_165:
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_161 = lean_st_ref_set(x_3, x_160, x_125);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_161)) {
 lean_ctor_release(x_161, 0);
 lean_ctor_release(x_161, 1);
 x_163 = x_161;
} else {
 lean_dec_ref(x_161);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_159);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
}
block_97:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_18 = lean_st_ref_take(x_3, x_17);
x_19 = lean_ctor_get(x_18, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_18, 1);
lean_inc(x_20);
lean_dec(x_18);
x_21 = !lean_is_exclusive(x_19);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; lean_object* x_32; uint64_t x_33; uint64_t x_34; uint64_t x_35; size_t x_36; size_t x_37; lean_object* x_38; size_t x_39; size_t x_40; size_t x_41; lean_object* x_42; uint8_t x_43; 
x_22 = lean_ctor_get(x_19, 0);
x_23 = lean_ctor_get(x_19, 1);
x_24 = lean_box(0);
x_25 = lean_box(2);
x_26 = lean_array_get_size(x_23);
x_27 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
x_28 = lean_unsigned_to_nat(32u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_unsigned_to_nat(16u);
x_33 = lean_uint64_of_nat(x_32);
x_34 = lean_uint64_shift_right(x_31, x_33);
x_35 = lean_uint64_xor(x_31, x_34);
x_36 = lean_uint64_to_usize(x_35);
x_37 = lean_usize_of_nat(x_26);
lean_dec(x_26);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_usize_of_nat(x_38);
x_40 = lean_usize_sub(x_37, x_39);
x_41 = lean_usize_land(x_36, x_40);
x_42 = lean_array_uget(x_23, x_41);
x_43 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_44 = lean_nat_add(x_22, x_38);
lean_dec(x_22);
x_45 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_45, 0, x_2);
lean_ctor_set(x_45, 1, x_25);
lean_ctor_set(x_45, 2, x_42);
x_46 = lean_array_uset(x_23, x_41, x_45);
x_47 = lean_unsigned_to_nat(2u);
x_48 = lean_nat_shiftl(x_44, x_47);
x_49 = lean_unsigned_to_nat(3u);
x_50 = lean_nat_div(x_48, x_49);
lean_dec(x_48);
x_51 = lean_array_get_size(x_46);
x_52 = lean_nat_dec_le(x_50, x_51);
lean_dec(x_51);
lean_dec(x_50);
if (x_52 == 0)
{
lean_object* x_53; 
x_53 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_46);
lean_ctor_set(x_19, 1, x_53);
lean_ctor_set(x_19, 0, x_44);
x_5 = x_20;
x_6 = x_24;
x_7 = x_19;
goto block_13;
}
else
{
lean_ctor_set(x_19, 1, x_46);
lean_ctor_set(x_19, 0, x_44);
x_5 = x_20;
x_6 = x_24;
x_7 = x_19;
goto block_13;
}
}
else
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_54 = lean_box(0);
x_55 = lean_array_uset(x_23, x_41, x_54);
x_56 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_25, x_42);
x_57 = lean_array_uset(x_55, x_41, x_56);
lean_ctor_set(x_19, 1, x_57);
x_5 = x_20;
x_6 = x_24;
x_7 = x_19;
goto block_13;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint64_t x_63; lean_object* x_64; uint64_t x_65; uint64_t x_66; uint64_t x_67; lean_object* x_68; uint64_t x_69; uint64_t x_70; uint64_t x_71; size_t x_72; size_t x_73; lean_object* x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; uint8_t x_79; 
x_58 = lean_ctor_get(x_19, 0);
x_59 = lean_ctor_get(x_19, 1);
lean_inc(x_59);
lean_inc(x_58);
lean_dec(x_19);
x_60 = lean_box(0);
x_61 = lean_box(2);
x_62 = lean_array_get_size(x_59);
x_63 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
x_64 = lean_unsigned_to_nat(32u);
x_65 = lean_uint64_of_nat(x_64);
x_66 = lean_uint64_shift_right(x_63, x_65);
x_67 = lean_uint64_xor(x_63, x_66);
x_68 = lean_unsigned_to_nat(16u);
x_69 = lean_uint64_of_nat(x_68);
x_70 = lean_uint64_shift_right(x_67, x_69);
x_71 = lean_uint64_xor(x_67, x_70);
x_72 = lean_uint64_to_usize(x_71);
x_73 = lean_usize_of_nat(x_62);
lean_dec(x_62);
x_74 = lean_unsigned_to_nat(1u);
x_75 = lean_usize_of_nat(x_74);
x_76 = lean_usize_sub(x_73, x_75);
x_77 = lean_usize_land(x_72, x_76);
x_78 = lean_array_uget(x_59, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_80 = lean_nat_add(x_58, x_74);
lean_dec(x_58);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_2);
lean_ctor_set(x_81, 1, x_61);
lean_ctor_set(x_81, 2, x_78);
x_82 = lean_array_uset(x_59, x_77, x_81);
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_nat_shiftl(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_82);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_80);
lean_ctor_set(x_90, 1, x_89);
x_5 = x_20;
x_6 = x_60;
x_7 = x_90;
goto block_13;
}
else
{
lean_object* x_91; 
x_91 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_91, 0, x_80);
lean_ctor_set(x_91, 1, x_82);
x_5 = x_20;
x_6 = x_60;
x_7 = x_91;
goto block_13;
}
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_92 = lean_box(0);
x_93 = lean_array_uset(x_59, x_77, x_92);
x_94 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_61, x_78);
x_95 = lean_array_uset(x_93, x_77, x_94);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_58);
lean_ctor_set(x_96, 1, x_95);
x_5 = x_20;
x_6 = x_60;
x_7 = x_96;
goto block_13;
}
}
}
}
else
{
lean_object* x_189; lean_object* x_190; lean_object* x_235; lean_object* x_236; uint64_t x_237; lean_object* x_238; uint64_t x_239; uint64_t x_240; uint64_t x_241; lean_object* x_242; uint64_t x_243; uint64_t x_244; uint64_t x_245; size_t x_246; size_t x_247; lean_object* x_248; size_t x_249; size_t x_250; size_t x_251; lean_object* x_252; lean_object* x_253; 
x_189 = lean_ctor_get(x_14, 0);
x_190 = lean_ctor_get(x_14, 1);
lean_inc(x_190);
lean_inc(x_189);
lean_dec(x_14);
x_235 = lean_ctor_get(x_189, 1);
lean_inc(x_235);
lean_dec(x_189);
x_236 = lean_array_get_size(x_235);
x_237 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
x_238 = lean_unsigned_to_nat(32u);
x_239 = lean_uint64_of_nat(x_238);
x_240 = lean_uint64_shift_right(x_237, x_239);
x_241 = lean_uint64_xor(x_237, x_240);
x_242 = lean_unsigned_to_nat(16u);
x_243 = lean_uint64_of_nat(x_242);
x_244 = lean_uint64_shift_right(x_241, x_243);
x_245 = lean_uint64_xor(x_241, x_244);
x_246 = lean_uint64_to_usize(x_245);
x_247 = lean_usize_of_nat(x_236);
lean_dec(x_236);
x_248 = lean_unsigned_to_nat(1u);
x_249 = lean_usize_of_nat(x_248);
x_250 = lean_usize_sub(x_247, x_249);
x_251 = lean_usize_land(x_246, x_250);
x_252 = lean_array_uget(x_235, x_251);
lean_dec(x_235);
x_253 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_2, x_252);
lean_dec(x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; 
lean_dec(x_2);
lean_dec(x_1);
x_254 = lean_box(0);
x_255 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_190);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; uint8_t x_258; 
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
lean_dec(x_253);
x_257 = lean_box(3);
x_258 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_256, x_257);
if (x_258 == 0)
{
uint8_t x_259; 
x_259 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_256, x_1);
lean_dec(x_1);
lean_dec(x_256);
if (x_259 == 0)
{
goto block_234;
}
else
{
if (x_258 == 0)
{
lean_object* x_260; lean_object* x_261; 
lean_dec(x_2);
x_260 = lean_box(0);
x_261 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_261, 0, x_260);
lean_ctor_set(x_261, 1, x_190);
return x_261;
}
else
{
goto block_234;
}
}
}
else
{
lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_275; size_t x_276; size_t x_277; size_t x_278; lean_object* x_279; uint8_t x_280; 
lean_dec(x_256);
x_262 = lean_st_ref_take(x_3, x_190);
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_263, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_263, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_267 = x_263;
} else {
 lean_dec_ref(x_263);
 x_267 = lean_box(0);
}
x_268 = lean_box(0);
x_275 = lean_array_get_size(x_266);
x_276 = lean_usize_of_nat(x_275);
lean_dec(x_275);
x_277 = lean_usize_sub(x_276, x_249);
x_278 = lean_usize_land(x_246, x_277);
x_279 = lean_array_uget(x_266, x_278);
x_280 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_279);
if (x_280 == 0)
{
lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; uint8_t x_289; 
x_281 = lean_nat_add(x_265, x_248);
lean_dec(x_265);
x_282 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_282, 0, x_2);
lean_ctor_set(x_282, 1, x_1);
lean_ctor_set(x_282, 2, x_279);
x_283 = lean_array_uset(x_266, x_278, x_282);
x_284 = lean_unsigned_to_nat(2u);
x_285 = lean_nat_shiftl(x_281, x_284);
x_286 = lean_unsigned_to_nat(3u);
x_287 = lean_nat_div(x_285, x_286);
lean_dec(x_285);
x_288 = lean_array_get_size(x_283);
x_289 = lean_nat_dec_le(x_287, x_288);
lean_dec(x_288);
lean_dec(x_287);
if (x_289 == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_283);
if (lean_is_scalar(x_267)) {
 x_291 = lean_alloc_ctor(0, 2, 0);
} else {
 x_291 = x_267;
}
lean_ctor_set(x_291, 0, x_281);
lean_ctor_set(x_291, 1, x_290);
x_269 = x_291;
goto block_274;
}
else
{
lean_object* x_292; 
if (lean_is_scalar(x_267)) {
 x_292 = lean_alloc_ctor(0, 2, 0);
} else {
 x_292 = x_267;
}
lean_ctor_set(x_292, 0, x_281);
lean_ctor_set(x_292, 1, x_283);
x_269 = x_292;
goto block_274;
}
}
else
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_box(0);
x_294 = lean_array_uset(x_266, x_278, x_293);
x_295 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_1, x_279);
x_296 = lean_array_uset(x_294, x_278, x_295);
if (lean_is_scalar(x_267)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_267;
}
lean_ctor_set(x_297, 0, x_265);
lean_ctor_set(x_297, 1, x_296);
x_269 = x_297;
goto block_274;
}
block_274:
{
lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_270 = lean_st_ref_set(x_3, x_269, x_264);
x_271 = lean_ctor_get(x_270, 1);
lean_inc(x_271);
if (lean_is_exclusive(x_270)) {
 lean_ctor_release(x_270, 0);
 lean_ctor_release(x_270, 1);
 x_272 = x_270;
} else {
 lean_dec_ref(x_270);
 x_272 = lean_box(0);
}
if (lean_is_scalar(x_272)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_272;
}
lean_ctor_set(x_273, 0, x_268);
lean_ctor_set(x_273, 1, x_271);
return x_273;
}
}
}
block_234:
{
lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint64_t x_200; lean_object* x_201; uint64_t x_202; uint64_t x_203; uint64_t x_204; lean_object* x_205; uint64_t x_206; uint64_t x_207; uint64_t x_208; size_t x_209; size_t x_210; lean_object* x_211; size_t x_212; size_t x_213; size_t x_214; lean_object* x_215; uint8_t x_216; 
x_191 = lean_st_ref_take(x_3, x_190);
x_192 = lean_ctor_get(x_191, 0);
lean_inc(x_192);
x_193 = lean_ctor_get(x_191, 1);
lean_inc(x_193);
lean_dec(x_191);
x_194 = lean_ctor_get(x_192, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_192, 1);
lean_inc(x_195);
if (lean_is_exclusive(x_192)) {
 lean_ctor_release(x_192, 0);
 lean_ctor_release(x_192, 1);
 x_196 = x_192;
} else {
 lean_dec_ref(x_192);
 x_196 = lean_box(0);
}
x_197 = lean_box(0);
x_198 = lean_box(2);
x_199 = lean_array_get_size(x_195);
x_200 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_2);
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
x_215 = lean_array_uget(x_195, x_214);
x_216 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_2, x_215);
if (x_216 == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; uint8_t x_225; 
x_217 = lean_nat_add(x_194, x_211);
lean_dec(x_194);
x_218 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_218, 0, x_2);
lean_ctor_set(x_218, 1, x_198);
lean_ctor_set(x_218, 2, x_215);
x_219 = lean_array_uset(x_195, x_214, x_218);
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
lean_object* x_226; lean_object* x_227; 
x_226 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_219);
if (lean_is_scalar(x_196)) {
 x_227 = lean_alloc_ctor(0, 2, 0);
} else {
 x_227 = x_196;
}
lean_ctor_set(x_227, 0, x_217);
lean_ctor_set(x_227, 1, x_226);
x_5 = x_193;
x_6 = x_197;
x_7 = x_227;
goto block_13;
}
else
{
lean_object* x_228; 
if (lean_is_scalar(x_196)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_196;
}
lean_ctor_set(x_228, 0, x_217);
lean_ctor_set(x_228, 1, x_219);
x_5 = x_193;
x_6 = x_197;
x_7 = x_228;
goto block_13;
}
}
else
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
x_229 = lean_box(0);
x_230 = lean_array_uset(x_195, x_214, x_229);
x_231 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_2, x_198, x_215);
x_232 = lean_array_uset(x_230, x_214, x_231);
if (lean_is_scalar(x_196)) {
 x_233 = lean_alloc_ctor(0, 2, 0);
} else {
 x_233 = x_196;
}
lean_ctor_set(x_233, 0, x_194);
lean_ctor_set(x_233, 1, x_232);
x_5 = x_193;
x_6 = x_197;
x_7 = x_233;
goto block_13;
}
}
}
block_13:
{
lean_object* x_8; uint8_t x_9; 
x_8 = lean_st_ref_set(x_3, x_7, x_5);
x_9 = !lean_is_exclusive(x_8);
if (x_9 == 0)
{
lean_object* x_10; 
x_10 = lean_ctor_get(x_8, 0);
lean_dec(x_10);
lean_ctor_set(x_8, 0, x_6);
return x_8;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_6);
lean_ctor_set(x_12, 1, x_11);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(x_1, x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = lean_box(0);
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_panic_fn(x_48, x_1);
x_50 = lean_apply_7(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_50;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_15;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_14 = lean_unsigned_to_nat(43u);
x_15 = lean_unsigned_to_nat(38u);
x_16 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
case 5:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_2 = x_20;
x_9 = x_22;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_21;
}
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_28 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___lam__0(x_1, x_24, x_25, x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_24);
return x_28;
}
case 7:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_33 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___lam__0(x_1, x_29, x_30, x_31, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_29);
return x_33;
}
case 8:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_35 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_36 = lean_unsigned_to_nat(43u);
x_37 = lean_unsigned_to_nat(38u);
x_38 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_40;
}
case 11:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_42 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_43 = lean_unsigned_to_nat(43u);
x_44 = lean_unsigned_to_nat(38u);
x_45 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_46 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
x_47 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0_spec__0(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_47;
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__4(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_box(0);
x_16 = lean_nat_dec_lt(x_13, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_13);
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(x_1, x_12, x_20, x_21, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_apply_8(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_24);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_30, x_30);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_free_object(x_25);
x_34 = lean_usize_of_nat(x_29);
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(x_1, x_24, x_34, x_35, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_24);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_get_size(x_24);
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_38);
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(x_1, x_24, x_45, x_46, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_24);
return x_47;
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_25;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_8(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___lam__0), 9, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__8(x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_11 = x_10;
goto block_19;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_11 = x_10;
goto block_19;
}
else
{
lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_25 = lean_box(0);
x_26 = lean_usize_of_nat(x_21);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3(x_1, x_20, x_26, x_27, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_11 = x_29;
goto block_19;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_18;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_9 = x_13;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_8(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_16);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_17);
x_26 = lean_usize_of_nat(x_21);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(x_1, x_16, x_26, x_27, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_16);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_16);
x_32 = lean_box(0);
x_33 = lean_nat_dec_lt(x_30, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = lean_usize_of_nat(x_30);
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(x_1, x_16, x_37, x_38, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_16);
return x_39;
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
case 4:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_42 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = lean_apply_8(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_45, 1);
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_40, 3);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_array_get_size(x_49);
x_52 = lean_box(0);
x_53 = lean_nat_dec_lt(x_50, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_45, 0, x_52);
return x_45;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_51, x_51);
if (x_54 == 0)
{
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_45, 0, x_52);
return x_45;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
lean_free_object(x_45);
x_55 = lean_usize_of_nat(x_50);
x_56 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_57 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(x_1, x_49, x_55, x_56, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_49);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec(x_45);
x_59 = lean_ctor_get(x_40, 3);
lean_inc(x_59);
lean_dec(x_40);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_59);
x_62 = lean_box(0);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_61, x_61);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_58);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = lean_usize_of_nat(x_60);
x_68 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_69 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(x_1, x_59, x_67, x_68, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_59);
return x_69;
}
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_45;
}
}
else
{
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_42;
}
}
case 5:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
lean_dec(x_2);
x_71 = lean_apply_8(x_1, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_71;
}
case 6:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec(x_2);
x_73 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_73;
}
default: 
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
x_76 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3___lam__0(x_1, x_74, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__11(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
lean_dec(x_5);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_1);
x_15 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(x_15, 0, x_14);
x_16 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_17 = l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0(x_15, x_16, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_3, x_21);
x_3 = x_22;
x_5 = x_18;
x_12 = x_19;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_17;
}
}
else
{
lean_object* x_24; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_5);
lean_ctor_set(x_24, 1, x_12);
return x_24;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_1);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goFVar___boxed), 9, 1);
lean_closure_set(x_10, 0, x_9);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_11);
x_15 = lean_nat_dec_lt(x_13, x_14);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_16;
}
else
{
uint8_t x_17; 
x_17 = lean_nat_dec_le(x_14, x_14);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_1);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_18;
}
else
{
lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_19 = lean_box(0);
x_20 = lean_usize_of_nat(x_13);
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__11(x_1, x_11, x_20, x_21, x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_11);
lean_dec(x_1);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_22, 1);
lean_inc(x_23);
lean_dec(x_22);
x_24 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
return x_24;
}
else
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_22;
}
}
}
}
else
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3(x_10, x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_26;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__0_spec__0___lam__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__3(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__4_spec__4_spec__5(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__3_spec__9(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt_spec__11(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_2, x_3);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_4);
x_13 = lean_array_uget(x_1, x_2);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goAlt(x_13, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
x_17 = lean_unsigned_to_nat(1u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_add(x_2, x_18);
x_2 = x_19;
x_4 = x_15;
x_11 = x_16;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
return x_14;
}
}
else
{
lean_object* x_21; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_4);
lean_ctor_set(x_21, 1, x_11);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = lean_ctor_get(x_1, 3);
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_9);
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
else
{
uint8_t x_15; 
x_15 = lean_nat_dec_le(x_11, x_11);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_8);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_10);
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(x_9, x_17, x_18, x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_1);
lean_ctor_set(x_8, 1, x_7);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_2, 1);
lean_inc(x_10);
lean_dec(x_2);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_9, 0);
lean_inc(x_95);
lean_inc(x_95);
x_96 = l_Lean_Compiler_LCNF_FloatLetIn_ignore_x3f___redArg(x_95, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_unbox(x_97);
lean_dec(x_97);
if (x_98 == 0)
{
lean_object* x_99; 
lean_dec(x_95);
x_99 = lean_ctor_get(x_96, 1);
lean_inc(x_99);
lean_dec(x_96);
x_11 = x_99;
goto block_94;
}
else
{
lean_object* x_100; uint8_t x_101; 
lean_dec(x_9);
x_100 = lean_ctor_get(x_96, 1);
lean_inc(x_100);
lean_dec(x_96);
x_101 = !lean_is_exclusive(x_1);
if (x_101 == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; lean_object* x_118; size_t x_119; size_t x_120; size_t x_121; lean_object* x_122; uint8_t x_123; 
x_102 = lean_ctor_get(x_1, 0);
x_103 = lean_ctor_get(x_1, 1);
x_104 = lean_ctor_get(x_95, 0);
lean_inc(x_104);
lean_dec(x_95);
x_105 = lean_box(2);
x_106 = lean_array_get_size(x_103);
x_107 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_104);
x_108 = lean_unsigned_to_nat(32u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_unsigned_to_nat(16u);
x_113 = lean_uint64_of_nat(x_112);
x_114 = lean_uint64_shift_right(x_111, x_113);
x_115 = lean_uint64_xor(x_111, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_usize_of_nat(x_118);
x_120 = lean_usize_sub(x_117, x_119);
x_121 = lean_usize_land(x_116, x_120);
x_122 = lean_array_uget(x_103, x_121);
x_123 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_104, x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; uint8_t x_132; 
x_124 = lean_nat_add(x_102, x_118);
lean_dec(x_102);
x_125 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_125, 0, x_104);
lean_ctor_set(x_125, 1, x_105);
lean_ctor_set(x_125, 2, x_122);
x_126 = lean_array_uset(x_103, x_121, x_125);
x_127 = lean_unsigned_to_nat(2u);
x_128 = lean_nat_shiftl(x_124, x_127);
x_129 = lean_unsigned_to_nat(3u);
x_130 = lean_nat_div(x_128, x_129);
lean_dec(x_128);
x_131 = lean_array_get_size(x_126);
x_132 = lean_nat_dec_le(x_130, x_131);
lean_dec(x_131);
lean_dec(x_130);
if (x_132 == 0)
{
lean_object* x_133; 
x_133 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_126);
lean_ctor_set(x_1, 1, x_133);
lean_ctor_set(x_1, 0, x_124);
x_2 = x_10;
x_7 = x_100;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_126);
lean_ctor_set(x_1, 0, x_124);
x_2 = x_10;
x_7 = x_100;
goto _start;
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_136 = lean_box(0);
x_137 = lean_array_uset(x_103, x_121, x_136);
x_138 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_104, x_105, x_122);
x_139 = lean_array_uset(x_137, x_121, x_138);
lean_ctor_set(x_1, 1, x_139);
x_2 = x_10;
x_7 = x_100;
goto _start;
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; uint64_t x_146; lean_object* x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; lean_object* x_151; uint64_t x_152; uint64_t x_153; uint64_t x_154; size_t x_155; size_t x_156; lean_object* x_157; size_t x_158; size_t x_159; size_t x_160; lean_object* x_161; uint8_t x_162; 
x_141 = lean_ctor_get(x_1, 0);
x_142 = lean_ctor_get(x_1, 1);
lean_inc(x_142);
lean_inc(x_141);
lean_dec(x_1);
x_143 = lean_ctor_get(x_95, 0);
lean_inc(x_143);
lean_dec(x_95);
x_144 = lean_box(2);
x_145 = lean_array_get_size(x_142);
x_146 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_143);
x_147 = lean_unsigned_to_nat(32u);
x_148 = lean_uint64_of_nat(x_147);
x_149 = lean_uint64_shift_right(x_146, x_148);
x_150 = lean_uint64_xor(x_146, x_149);
x_151 = lean_unsigned_to_nat(16u);
x_152 = lean_uint64_of_nat(x_151);
x_153 = lean_uint64_shift_right(x_150, x_152);
x_154 = lean_uint64_xor(x_150, x_153);
x_155 = lean_uint64_to_usize(x_154);
x_156 = lean_usize_of_nat(x_145);
lean_dec(x_145);
x_157 = lean_unsigned_to_nat(1u);
x_158 = lean_usize_of_nat(x_157);
x_159 = lean_usize_sub(x_156, x_158);
x_160 = lean_usize_land(x_155, x_159);
x_161 = lean_array_uget(x_142, x_160);
x_162 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_143, x_161);
if (x_162 == 0)
{
lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; uint8_t x_171; 
x_163 = lean_nat_add(x_141, x_157);
lean_dec(x_141);
x_164 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_164, 0, x_143);
lean_ctor_set(x_164, 1, x_144);
lean_ctor_set(x_164, 2, x_161);
x_165 = lean_array_uset(x_142, x_160, x_164);
x_166 = lean_unsigned_to_nat(2u);
x_167 = lean_nat_shiftl(x_163, x_166);
x_168 = lean_unsigned_to_nat(3u);
x_169 = lean_nat_div(x_167, x_168);
lean_dec(x_167);
x_170 = lean_array_get_size(x_165);
x_171 = lean_nat_dec_le(x_169, x_170);
lean_dec(x_170);
lean_dec(x_169);
if (x_171 == 0)
{
lean_object* x_172; lean_object* x_173; 
x_172 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_165);
x_173 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_173, 0, x_163);
lean_ctor_set(x_173, 1, x_172);
x_1 = x_173;
x_2 = x_10;
x_7 = x_100;
goto _start;
}
else
{
lean_object* x_175; 
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_163);
lean_ctor_set(x_175, 1, x_165);
x_1 = x_175;
x_2 = x_10;
x_7 = x_100;
goto _start;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_box(0);
x_178 = lean_array_uset(x_142, x_160, x_177);
x_179 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_143, x_144, x_161);
x_180 = lean_array_uset(x_178, x_160, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_141);
lean_ctor_set(x_181, 1, x_180);
x_1 = x_181;
x_2 = x_10;
x_7 = x_100;
goto _start;
}
}
}
}
else
{
uint8_t x_183; 
lean_dec(x_95);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_1);
x_183 = !lean_is_exclusive(x_96);
if (x_183 == 0)
{
return x_96;
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; 
x_184 = lean_ctor_get(x_96, 0);
x_185 = lean_ctor_get(x_96, 1);
lean_inc(x_185);
lean_inc(x_184);
lean_dec(x_96);
x_186 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
return x_186;
}
}
}
else
{
x_11 = x_7;
goto block_94;
}
block_94:
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_1);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; size_t x_31; size_t x_32; lean_object* x_33; uint8_t x_34; 
x_13 = lean_ctor_get(x_1, 0);
x_14 = lean_ctor_get(x_1, 1);
x_15 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_9);
lean_dec(x_9);
x_16 = lean_box(3);
x_17 = lean_array_get_size(x_14);
x_18 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_15);
x_19 = lean_unsigned_to_nat(32u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_unsigned_to_nat(16u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_usize_of_nat(x_29);
x_31 = lean_usize_sub(x_28, x_30);
x_32 = lean_usize_land(x_27, x_31);
x_33 = lean_array_uget(x_14, x_32);
x_34 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_15, x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_35 = lean_nat_add(x_13, x_29);
lean_dec(x_13);
x_36 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_36, 0, x_15);
lean_ctor_set(x_36, 1, x_16);
lean_ctor_set(x_36, 2, x_33);
x_37 = lean_array_uset(x_14, x_32, x_36);
x_38 = lean_unsigned_to_nat(2u);
x_39 = lean_nat_shiftl(x_35, x_38);
x_40 = lean_unsigned_to_nat(3u);
x_41 = lean_nat_div(x_39, x_40);
lean_dec(x_39);
x_42 = lean_array_get_size(x_37);
x_43 = lean_nat_dec_le(x_41, x_42);
lean_dec(x_42);
lean_dec(x_41);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_37);
lean_ctor_set(x_1, 1, x_44);
lean_ctor_set(x_1, 0, x_35);
x_2 = x_10;
x_7 = x_11;
goto _start;
}
else
{
lean_ctor_set(x_1, 1, x_37);
lean_ctor_set(x_1, 0, x_35);
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_47 = lean_box(0);
x_48 = lean_array_uset(x_14, x_32, x_47);
x_49 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_15, x_16, x_33);
x_50 = lean_array_uset(x_48, x_32, x_49);
lean_ctor_set(x_1, 1, x_50);
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; size_t x_66; size_t x_67; lean_object* x_68; size_t x_69; size_t x_70; size_t x_71; lean_object* x_72; uint8_t x_73; 
x_52 = lean_ctor_get(x_1, 0);
x_53 = lean_ctor_get(x_1, 1);
lean_inc(x_53);
lean_inc(x_52);
lean_dec(x_1);
x_54 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_9);
lean_dec(x_9);
x_55 = lean_box(3);
x_56 = lean_array_get_size(x_53);
x_57 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_54);
x_58 = lean_unsigned_to_nat(32u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_shift_right(x_57, x_59);
x_61 = lean_uint64_xor(x_57, x_60);
x_62 = lean_unsigned_to_nat(16u);
x_63 = lean_uint64_of_nat(x_62);
x_64 = lean_uint64_shift_right(x_61, x_63);
x_65 = lean_uint64_xor(x_61, x_64);
x_66 = lean_uint64_to_usize(x_65);
x_67 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_68 = lean_unsigned_to_nat(1u);
x_69 = lean_usize_of_nat(x_68);
x_70 = lean_usize_sub(x_67, x_69);
x_71 = lean_usize_land(x_66, x_70);
x_72 = lean_array_uget(x_53, x_71);
x_73 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_54, x_72);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; 
x_74 = lean_nat_add(x_52, x_68);
lean_dec(x_52);
x_75 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_75, 0, x_54);
lean_ctor_set(x_75, 1, x_55);
lean_ctor_set(x_75, 2, x_72);
x_76 = lean_array_uset(x_53, x_71, x_75);
x_77 = lean_unsigned_to_nat(2u);
x_78 = lean_nat_shiftl(x_74, x_77);
x_79 = lean_unsigned_to_nat(3u);
x_80 = lean_nat_div(x_78, x_79);
lean_dec(x_78);
x_81 = lean_array_get_size(x_76);
x_82 = lean_nat_dec_le(x_80, x_81);
lean_dec(x_81);
lean_dec(x_80);
if (x_82 == 0)
{
lean_object* x_83; lean_object* x_84; 
x_83 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_76);
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_74);
lean_ctor_set(x_84, 1, x_83);
x_1 = x_84;
x_2 = x_10;
x_7 = x_11;
goto _start;
}
else
{
lean_object* x_86; 
x_86 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_86, 0, x_74);
lean_ctor_set(x_86, 1, x_76);
x_1 = x_86;
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_88 = lean_box(0);
x_89 = lean_array_uset(x_53, x_71, x_88);
x_90 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_54, x_55, x_72);
x_91 = lean_array_uset(x_89, x_71, x_90);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_52);
lean_ctor_set(x_92, 1, x_91);
x_1 = x_92;
x_2 = x_10;
x_7 = x_11;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(x_1, x_2, x_4, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_30 = l_List_lengthTR(lean_box(0), x_2);
x_31 = lean_unsigned_to_nat(0u);
x_32 = lean_unsigned_to_nat(2u);
x_33 = lean_nat_shiftl(x_30, x_32);
lean_dec(x_30);
x_34 = lean_unsigned_to_nat(3u);
x_35 = lean_nat_div(x_33, x_34);
lean_dec(x_33);
x_36 = l_Nat_nextPowerOfTwo(x_35);
lean_dec(x_35);
x_37 = lean_box(0);
x_38 = lean_mk_array(x_36, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_31);
lean_ctor_set(x_39, 1, x_38);
lean_inc(x_2);
x_40 = l_List_reverse___redArg(x_2);
x_41 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(x_39, x_40, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; lean_object* x_53; uint64_t x_54; uint64_t x_55; uint64_t x_56; size_t x_57; size_t x_58; lean_object* x_59; size_t x_60; size_t x_61; size_t x_62; lean_object* x_63; uint8_t x_64; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 2);
lean_inc(x_46);
x_47 = lean_array_get_size(x_45);
x_48 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_46);
x_49 = lean_unsigned_to_nat(32u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_right(x_48, x_50);
x_52 = lean_uint64_xor(x_48, x_51);
x_53 = lean_unsigned_to_nat(16u);
x_54 = lean_uint64_of_nat(x_53);
x_55 = lean_uint64_shift_right(x_52, x_54);
x_56 = lean_uint64_xor(x_52, x_55);
x_57 = lean_uint64_to_usize(x_56);
x_58 = lean_usize_of_nat(x_47);
lean_dec(x_47);
x_59 = lean_unsigned_to_nat(1u);
x_60 = lean_usize_of_nat(x_59);
x_61 = lean_usize_sub(x_58, x_60);
x_62 = lean_usize_land(x_57, x_61);
x_63 = lean_array_uget(x_45, x_62);
x_64 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_46, x_63);
if (x_64 == 0)
{
lean_dec(x_63);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_44);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
else
{
uint8_t x_65; 
x_65 = !lean_is_exclusive(x_42);
if (x_65 == 0)
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_42, 1);
lean_dec(x_66);
x_67 = lean_ctor_get(x_42, 0);
lean_dec(x_67);
x_68 = lean_box(2);
if (x_64 == 0)
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_69 = lean_nat_add(x_44, x_59);
lean_dec(x_44);
x_70 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_70, 0, x_46);
lean_ctor_set(x_70, 1, x_68);
lean_ctor_set(x_70, 2, x_63);
x_71 = lean_array_uset(x_45, x_62, x_70);
x_72 = lean_nat_shiftl(x_69, x_32);
x_73 = lean_nat_div(x_72, x_34);
lean_dec(x_72);
x_74 = lean_array_get_size(x_71);
x_75 = lean_nat_dec_le(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_71);
lean_ctor_set(x_42, 1, x_76);
lean_ctor_set(x_42, 0, x_69);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
else
{
lean_ctor_set(x_42, 1, x_71);
lean_ctor_set(x_42, 0, x_69);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_array_uset(x_45, x_62, x_37);
x_78 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_46, x_68, x_63);
x_79 = lean_array_uset(x_77, x_62, x_78);
lean_ctor_set(x_42, 1, x_79);
x_8 = x_42;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
else
{
lean_object* x_80; 
lean_dec(x_42);
x_80 = lean_box(2);
if (x_64 == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_81 = lean_nat_add(x_44, x_59);
lean_dec(x_44);
x_82 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_82, 0, x_46);
lean_ctor_set(x_82, 1, x_80);
lean_ctor_set(x_82, 2, x_63);
x_83 = lean_array_uset(x_45, x_62, x_82);
x_84 = lean_nat_shiftl(x_81, x_32);
x_85 = lean_nat_div(x_84, x_34);
lean_dec(x_84);
x_86 = lean_array_get_size(x_83);
x_87 = lean_nat_dec_le(x_85, x_86);
lean_dec(x_86);
lean_dec(x_85);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_83);
x_89 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_89, 0, x_81);
lean_ctor_set(x_89, 1, x_88);
x_8 = x_89;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
else
{
lean_object* x_90; 
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_81);
lean_ctor_set(x_90, 1, x_83);
x_8 = x_90;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_array_uset(x_45, x_62, x_37);
x_92 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_46, x_80, x_63);
x_93 = lean_array_uset(x_91, x_62, x_92);
x_94 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_94, 0, x_44);
lean_ctor_set(x_94, 1, x_93);
x_8 = x_94;
x_9 = x_2;
x_10 = x_3;
x_11 = x_4;
x_12 = x_5;
x_13 = x_6;
x_14 = x_43;
goto block_29;
}
}
}
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_41;
}
block_29:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_st_mk_ref(x_8, x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
lean_inc(x_16);
x_18 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions_goCases(x_1, x_16, x_9, x_10, x_11, x_12, x_13, x_17);
lean_dec(x_1);
if (lean_obj_tag(x_18) == 0)
{
lean_object* x_19; lean_object* x_20; uint8_t x_21; 
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = lean_st_ref_get(x_16, x_19);
lean_dec(x_16);
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
return x_20;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_ctor_get(x_20, 0);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_20);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_23);
return x_24;
}
}
else
{
uint8_t x_25; 
lean_dec(x_16);
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
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_foldlM___at___Lean_Compiler_LCNF_FloatLetIn_initialDecisions_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_5, x_1);
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
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
x_7 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_4);
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
x_29 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_25);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1_spec__1___redArg(x_3, x_6);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(lean_object* x_1) {
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
x_8 = l_Std_DHashMap_Internal_Raw_u2080_expand_go___at___Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1_spec__1___redArg(x_5, x_1, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
else
{
uint8_t x_4; 
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_3, 1);
x_7 = lean_ctor_get(x_3, 2);
x_8 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_5, x_1);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_1, x_2, x_7);
lean_ctor_set(x_3, 2, x_9);
return x_3;
}
else
{
lean_dec(x_6);
lean_dec(x_5);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 0, x_1);
return x_3;
}
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_3, 0);
x_11 = lean_ctor_get(x_3, 1);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_3);
x_13 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_10, x_1);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_1, x_2, x_12);
x_15 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_15, 0, x_10);
lean_ctor_set(x_15, 1, x_11);
lean_ctor_set(x_15, 2, x_14);
return x_15;
}
else
{
lean_object* x_16; 
lean_dec(x_11);
lean_dec(x_10);
x_16 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_16, 0, x_1);
lean_ctor_set(x_16, 1, x_2);
lean_ctor_set(x_16, 2, x_12);
return x_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
uint8_t x_6; 
x_6 = !lean_is_exclusive(x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; size_t x_27; size_t x_28; lean_object* x_29; uint8_t x_30; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
x_9 = lean_box(0);
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_usize_of_nat(x_10);
x_12 = lean_usize_sub(x_2, x_11);
x_13 = lean_array_uget(x_1, x_12);
x_14 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_13);
lean_dec(x_13);
x_15 = lean_array_get_size(x_8);
x_16 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_14);
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
x_27 = lean_usize_sub(x_26, x_11);
x_28 = lean_usize_land(x_25, x_27);
x_29 = lean_array_uget(x_8, x_28);
x_30 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_14, x_29);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_31 = lean_nat_add(x_7, x_10);
lean_dec(x_7);
x_32 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_32, 0, x_14);
lean_ctor_set(x_32, 1, x_9);
lean_ctor_set(x_32, 2, x_29);
x_33 = lean_array_uset(x_8, x_28, x_32);
x_34 = lean_unsigned_to_nat(2u);
x_35 = lean_nat_shiftl(x_31, x_34);
x_36 = lean_unsigned_to_nat(3u);
x_37 = lean_nat_div(x_35, x_36);
lean_dec(x_35);
x_38 = lean_array_get_size(x_33);
x_39 = lean_nat_dec_le(x_37, x_38);
lean_dec(x_38);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_33);
lean_ctor_set(x_4, 1, x_40);
lean_ctor_set(x_4, 0, x_31);
x_2 = x_12;
goto _start;
}
else
{
lean_ctor_set(x_4, 1, x_33);
lean_ctor_set(x_4, 0, x_31);
x_2 = x_12;
goto _start;
}
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_box(0);
x_44 = lean_array_uset(x_8, x_28, x_43);
x_45 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_14, x_9, x_29);
x_46 = lean_array_uset(x_44, x_28, x_45);
lean_ctor_set(x_4, 1, x_46);
x_2 = x_12;
goto _start;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; uint64_t x_57; lean_object* x_58; uint64_t x_59; uint64_t x_60; uint64_t x_61; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; size_t x_66; size_t x_67; size_t x_68; size_t x_69; lean_object* x_70; uint8_t x_71; 
x_48 = lean_ctor_get(x_4, 0);
x_49 = lean_ctor_get(x_4, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_4);
x_50 = lean_box(0);
x_51 = lean_unsigned_to_nat(1u);
x_52 = lean_usize_of_nat(x_51);
x_53 = lean_usize_sub(x_2, x_52);
x_54 = lean_array_uget(x_1, x_53);
x_55 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_54);
lean_dec(x_54);
x_56 = lean_array_get_size(x_49);
x_57 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_55);
x_58 = lean_unsigned_to_nat(32u);
x_59 = lean_uint64_of_nat(x_58);
x_60 = lean_uint64_shift_right(x_57, x_59);
x_61 = lean_uint64_xor(x_57, x_60);
x_62 = lean_unsigned_to_nat(16u);
x_63 = lean_uint64_of_nat(x_62);
x_64 = lean_uint64_shift_right(x_61, x_63);
x_65 = lean_uint64_xor(x_61, x_64);
x_66 = lean_uint64_to_usize(x_65);
x_67 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_68 = lean_usize_sub(x_67, x_52);
x_69 = lean_usize_land(x_66, x_68);
x_70 = lean_array_uget(x_49, x_69);
x_71 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_55, x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_72 = lean_nat_add(x_48, x_51);
lean_dec(x_48);
x_73 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_73, 0, x_55);
lean_ctor_set(x_73, 1, x_50);
lean_ctor_set(x_73, 2, x_70);
x_74 = lean_array_uset(x_49, x_69, x_73);
x_75 = lean_unsigned_to_nat(2u);
x_76 = lean_nat_shiftl(x_72, x_75);
x_77 = lean_unsigned_to_nat(3u);
x_78 = lean_nat_div(x_76, x_77);
lean_dec(x_76);
x_79 = lean_array_get_size(x_74);
x_80 = lean_nat_dec_le(x_78, x_79);
lean_dec(x_79);
lean_dec(x_78);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
x_81 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_74);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_72);
lean_ctor_set(x_82, 1, x_81);
x_2 = x_53;
x_4 = x_82;
goto _start;
}
else
{
lean_object* x_84; 
x_84 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_84, 0, x_72);
lean_ctor_set(x_84, 1, x_74);
x_2 = x_53;
x_4 = x_84;
goto _start;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_86 = lean_box(0);
x_87 = lean_array_uset(x_49, x_69, x_86);
x_88 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_55, x_50, x_70);
x_89 = lean_array_uset(x_87, x_69, x_88);
x_90 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_90, 0, x_48);
lean_ctor_set(x_90, 1, x_89);
x_2 = x_53;
x_4 = x_90;
goto _start;
}
}
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint64_t x_23; lean_object* x_24; uint64_t x_25; uint64_t x_26; uint64_t x_27; lean_object* x_28; uint64_t x_29; uint64_t x_30; uint64_t x_31; size_t x_32; size_t x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; uint8_t x_38; 
x_2 = lean_ctor_get(x_1, 3);
x_3 = lean_array_get_size(x_2);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_add(x_3, x_11);
x_13 = lean_unsigned_to_nat(2u);
x_14 = lean_nat_shiftl(x_12, x_13);
lean_dec(x_12);
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_nat_div(x_14, x_15);
lean_dec(x_14);
x_17 = l_Nat_nextPowerOfTwo(x_16);
lean_dec(x_16);
x_18 = lean_box(0);
x_19 = lean_mk_array(x_17, x_18);
x_20 = lean_box(2);
x_21 = lean_box(0);
x_22 = lean_array_get_size(x_19);
x_23 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_20);
x_24 = lean_unsigned_to_nat(32u);
x_25 = lean_uint64_of_nat(x_24);
x_26 = lean_uint64_shift_right(x_23, x_25);
x_27 = lean_uint64_xor(x_23, x_26);
x_28 = lean_unsigned_to_nat(16u);
x_29 = lean_uint64_of_nat(x_28);
x_30 = lean_uint64_shift_right(x_27, x_29);
x_31 = lean_uint64_xor(x_27, x_30);
x_32 = lean_uint64_to_usize(x_31);
x_33 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_34 = lean_usize_of_nat(x_11);
x_35 = lean_usize_sub(x_33, x_34);
x_36 = lean_usize_land(x_32, x_35);
x_37 = lean_array_uget(x_19, x_36);
x_38 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_20, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_39 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_39, 0, x_20);
lean_ctor_set(x_39, 1, x_21);
lean_ctor_set(x_39, 2, x_37);
x_40 = lean_array_uset(x_19, x_36, x_39);
x_41 = lean_nat_shiftl(x_11, x_13);
x_42 = lean_nat_div(x_41, x_15);
lean_dec(x_41);
x_43 = lean_array_get_size(x_40);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_40);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_11);
lean_ctor_set(x_46, 1, x_45);
x_4 = x_46;
goto block_10;
}
else
{
lean_object* x_47; 
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_11);
lean_ctor_set(x_47, 1, x_40);
x_4 = x_47;
goto block_10;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_48 = lean_unsigned_to_nat(0u);
x_49 = lean_array_uset(x_19, x_36, x_18);
x_50 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_20, x_21, x_37);
x_51 = lean_array_uset(x_49, x_36, x_50);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_48);
lean_ctor_set(x_52, 1, x_51);
x_4 = x_52;
goto block_10;
}
block_10:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_nat_dec_lt(x_5, x_3);
if (x_6 == 0)
{
lean_dec(x_3);
return x_4;
}
else
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_usize_of_nat(x_3);
lean_dec(x_3);
x_8 = lean_usize_of_nat(x_5);
x_9 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5(x_2, x_7, x_8, x_4);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldrMUnsafe_fold___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__5(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_st_ref_get(x_2, x_3);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
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
x_12 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_28 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_27);
lean_dec(x_27);
if (x_28 == 0)
{
lean_object* x_29; 
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_4, 0, x_29);
return x_4;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
lean_free_object(x_4);
x_30 = lean_st_ref_take(x_2, x_8);
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
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
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_48; lean_object* x_49; size_t x_50; size_t x_51; size_t x_52; lean_object* x_53; uint8_t x_54; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
x_38 = lean_box(0);
x_48 = lean_box(2);
x_49 = lean_array_get_size(x_37);
x_50 = lean_usize_of_nat(x_49);
lean_dec(x_49);
x_51 = lean_usize_sub(x_50, x_24);
x_52 = lean_usize_land(x_21, x_51);
x_53 = lean_array_uget(x_37, x_52);
x_54 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_55 = lean_nat_add(x_36, x_23);
lean_dec(x_36);
x_56 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_56, 0, x_1);
lean_ctor_set(x_56, 1, x_48);
lean_ctor_set(x_56, 2, x_53);
x_57 = lean_array_uset(x_37, x_52, x_56);
x_58 = lean_unsigned_to_nat(2u);
x_59 = lean_nat_shiftl(x_55, x_58);
x_60 = lean_unsigned_to_nat(3u);
x_61 = lean_nat_div(x_59, x_60);
lean_dec(x_59);
x_62 = lean_array_get_size(x_57);
x_63 = lean_nat_dec_le(x_61, x_62);
lean_dec(x_62);
lean_dec(x_61);
if (x_63 == 0)
{
lean_object* x_64; 
x_64 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_57);
lean_ctor_set(x_32, 1, x_64);
lean_ctor_set(x_32, 0, x_55);
x_39 = x_32;
goto block_47;
}
else
{
lean_ctor_set(x_32, 1, x_57);
lean_ctor_set(x_32, 0, x_55);
x_39 = x_32;
goto block_47;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_65 = lean_box(0);
x_66 = lean_array_uset(x_37, x_52, x_65);
x_67 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_48, x_53);
x_68 = lean_array_uset(x_66, x_52, x_67);
lean_ctor_set(x_32, 1, x_68);
x_39 = x_32;
goto block_47;
}
block_47:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_dec(x_31);
if (lean_is_scalar(x_34)) {
 x_41 = lean_alloc_ctor(0, 2, 0);
} else {
 x_41 = x_34;
}
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
x_42 = lean_st_ref_set(x_2, x_41, x_33);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_42, 0);
lean_dec(x_44);
lean_ctor_set(x_42, 0, x_38);
return x_42;
}
else
{
lean_object* x_45; lean_object* x_46; 
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
lean_dec(x_42);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_38);
lean_ctor_set(x_46, 1, x_45);
return x_46;
}
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; size_t x_84; lean_object* x_85; uint8_t x_86; 
x_69 = lean_ctor_get(x_32, 0);
x_70 = lean_ctor_get(x_32, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_32);
x_71 = lean_box(0);
x_80 = lean_box(2);
x_81 = lean_array_get_size(x_70);
x_82 = lean_usize_of_nat(x_81);
lean_dec(x_81);
x_83 = lean_usize_sub(x_82, x_24);
x_84 = lean_usize_land(x_21, x_83);
x_85 = lean_array_uget(x_70, x_84);
x_86 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_85);
if (x_86 == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_87 = lean_nat_add(x_69, x_23);
lean_dec(x_69);
x_88 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_88, 0, x_1);
lean_ctor_set(x_88, 1, x_80);
lean_ctor_set(x_88, 2, x_85);
x_89 = lean_array_uset(x_70, x_84, x_88);
x_90 = lean_unsigned_to_nat(2u);
x_91 = lean_nat_shiftl(x_87, x_90);
x_92 = lean_unsigned_to_nat(3u);
x_93 = lean_nat_div(x_91, x_92);
lean_dec(x_91);
x_94 = lean_array_get_size(x_89);
x_95 = lean_nat_dec_le(x_93, x_94);
lean_dec(x_94);
lean_dec(x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; 
x_96 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_89);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_87);
lean_ctor_set(x_97, 1, x_96);
x_72 = x_97;
goto block_79;
}
else
{
lean_object* x_98; 
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_87);
lean_ctor_set(x_98, 1, x_89);
x_72 = x_98;
goto block_79;
}
}
else
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; 
x_99 = lean_box(0);
x_100 = lean_array_uset(x_70, x_84, x_99);
x_101 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_80, x_85);
x_102 = lean_array_uset(x_100, x_84, x_101);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_69);
lean_ctor_set(x_103, 1, x_102);
x_72 = x_103;
goto block_79;
}
block_79:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_73 = lean_ctor_get(x_31, 1);
lean_inc(x_73);
lean_dec(x_31);
if (lean_is_scalar(x_34)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_34;
}
lean_ctor_set(x_74, 0, x_72);
lean_ctor_set(x_74, 1, x_73);
x_75 = lean_st_ref_set(x_2, x_74, x_33);
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
lean_ctor_set(x_78, 0, x_71);
lean_ctor_set(x_78, 1, x_76);
return x_78;
}
}
}
}
else
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; lean_object* x_118; size_t x_119; size_t x_120; size_t x_121; lean_object* x_122; uint8_t x_123; 
x_104 = lean_ctor_get(x_4, 1);
lean_inc(x_104);
lean_dec(x_4);
x_105 = lean_ctor_get(x_6, 1);
lean_inc(x_105);
lean_dec(x_6);
x_106 = lean_array_get_size(x_105);
x_107 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_108 = lean_unsigned_to_nat(32u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_unsigned_to_nat(16u);
x_113 = lean_uint64_of_nat(x_112);
x_114 = lean_uint64_shift_right(x_111, x_113);
x_115 = lean_uint64_xor(x_111, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_usize_of_nat(x_118);
x_120 = lean_usize_sub(x_117, x_119);
x_121 = lean_usize_land(x_116, x_120);
x_122 = lean_array_uget(x_105, x_121);
lean_dec(x_105);
x_123 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; 
lean_dec(x_1);
x_124 = lean_box(0);
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_124);
lean_ctor_set(x_125, 1, x_104);
return x_125;
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_143; lean_object* x_144; size_t x_145; size_t x_146; size_t x_147; lean_object* x_148; uint8_t x_149; 
x_126 = lean_st_ref_take(x_2, x_104);
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_126, 1);
lean_inc(x_129);
if (lean_is_exclusive(x_126)) {
 lean_ctor_release(x_126, 0);
 lean_ctor_release(x_126, 1);
 x_130 = x_126;
} else {
 lean_dec_ref(x_126);
 x_130 = lean_box(0);
}
x_131 = lean_ctor_get(x_128, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_128)) {
 lean_ctor_release(x_128, 0);
 lean_ctor_release(x_128, 1);
 x_133 = x_128;
} else {
 lean_dec_ref(x_128);
 x_133 = lean_box(0);
}
x_134 = lean_box(0);
x_143 = lean_box(2);
x_144 = lean_array_get_size(x_132);
x_145 = lean_usize_of_nat(x_144);
lean_dec(x_144);
x_146 = lean_usize_sub(x_145, x_119);
x_147 = lean_usize_land(x_116, x_146);
x_148 = lean_array_uget(x_132, x_147);
x_149 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; uint8_t x_158; 
x_150 = lean_nat_add(x_131, x_118);
lean_dec(x_131);
x_151 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_151, 0, x_1);
lean_ctor_set(x_151, 1, x_143);
lean_ctor_set(x_151, 2, x_148);
x_152 = lean_array_uset(x_132, x_147, x_151);
x_153 = lean_unsigned_to_nat(2u);
x_154 = lean_nat_shiftl(x_150, x_153);
x_155 = lean_unsigned_to_nat(3u);
x_156 = lean_nat_div(x_154, x_155);
lean_dec(x_154);
x_157 = lean_array_get_size(x_152);
x_158 = lean_nat_dec_le(x_156, x_157);
lean_dec(x_157);
lean_dec(x_156);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; 
x_159 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_152);
if (lean_is_scalar(x_133)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_133;
}
lean_ctor_set(x_160, 0, x_150);
lean_ctor_set(x_160, 1, x_159);
x_135 = x_160;
goto block_142;
}
else
{
lean_object* x_161; 
if (lean_is_scalar(x_133)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_133;
}
lean_ctor_set(x_161, 0, x_150);
lean_ctor_set(x_161, 1, x_152);
x_135 = x_161;
goto block_142;
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_162 = lean_box(0);
x_163 = lean_array_uset(x_132, x_147, x_162);
x_164 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_143, x_148);
x_165 = lean_array_uset(x_163, x_147, x_164);
if (lean_is_scalar(x_133)) {
 x_166 = lean_alloc_ctor(0, 2, 0);
} else {
 x_166 = x_133;
}
lean_ctor_set(x_166, 0, x_131);
lean_ctor_set(x_166, 1, x_165);
x_135 = x_166;
goto block_142;
}
block_142:
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_136 = lean_ctor_get(x_127, 1);
lean_inc(x_136);
lean_dec(x_127);
if (lean_is_scalar(x_130)) {
 x_137 = lean_alloc_ctor(0, 2, 0);
} else {
 x_137 = x_130;
}
lean_ctor_set(x_137, 0, x_135);
lean_ctor_set(x_137, 1, x_136);
x_138 = lean_st_ref_set(x_2, x_137, x_129);
x_139 = lean_ctor_get(x_138, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_140 = x_138;
} else {
 lean_dec_ref(x_138);
 x_140 = lean_box(0);
}
if (lean_is_scalar(x_140)) {
 x_141 = lean_alloc_ctor(0, 2, 0);
} else {
 x_141 = x_140;
}
lean_ctor_set(x_141, 0, x_134);
lean_ctor_set(x_141, 1, x_139);
return x_141;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(x_1, x_2, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
x_5 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
x_6 = lean_unsigned_to_nat(138u);
x_7 = lean_unsigned_to_nat(11u);
x_8 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_panic_fn(x_1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_11, x_2);
if (x_14 == 0)
{
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_12);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
x_46 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_45);
x_47 = lean_box(0);
x_48 = l_instInhabitedOfMonad___redArg(x_46, x_47);
x_49 = lean_panic_fn(x_48, x_1);
x_50 = lean_apply_7(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_50;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, uint8_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_3, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_14);
return x_15;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_1);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 2:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_2);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_13 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_14 = lean_unsigned_to_nat(43u);
x_15 = lean_unsigned_to_nat(38u);
x_16 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(x_17, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_18;
}
case 5:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_21 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_19, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_2 = x_20;
x_9 = x_22;
goto _start;
}
else
{
lean_dec(x_20);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_21;
}
}
case 6:
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_2, 2);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_28 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1___lam__0(x_1, x_24, x_25, x_26, x_27, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_24);
return x_28;
}
case 7:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; 
x_29 = lean_ctor_get(x_2, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_2, 1);
lean_inc(x_30);
x_31 = lean_ctor_get(x_2, 2);
lean_inc(x_31);
x_32 = lean_ctor_get_uint8(x_2, sizeof(void*)*3 + 8);
lean_dec(x_2);
x_33 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1___lam__0(x_1, x_29, x_30, x_31, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_29);
return x_33;
}
case 8:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_35 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_36 = lean_unsigned_to_nat(43u);
x_37 = lean_unsigned_to_nat(38u);
x_38 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_39 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_34, x_35, x_36, x_37, x_38);
lean_dec(x_38);
lean_dec(x_35);
lean_dec(x_34);
x_40 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(x_39, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_40;
}
case 11:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = lean_mk_string_unchecked("Lean.Compiler.LCNF.FVarUtil", 27, 27);
x_42 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Expr.forFVarM", 32, 32);
x_43 = lean_unsigned_to_nat(43u);
x_44 = lean_unsigned_to_nat(38u);
x_45 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_46 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_41, x_42, x_43, x_44, x_45);
lean_dec(x_45);
lean_dec(x_42);
lean_dec(x_41);
x_47 = l_panic___at___Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1_spec__1(x_46, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_47;
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_10 = lean_box(0);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
case 1:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 0);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_apply_8(x_1, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
default: 
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_2, 0);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Arg_forFVarM___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__3(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
lean_dec(x_2);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get_size(x_12);
x_15 = lean_box(0);
x_16 = lean_nat_dec_lt(x_13, x_14);
if (x_16 == 0)
{
lean_object* x_17; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_9);
return x_17;
}
else
{
uint8_t x_18; 
x_18 = lean_nat_dec_le(x_14, x_14);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_15);
lean_ctor_set(x_19, 1, x_9);
return x_19;
}
else
{
size_t x_20; size_t x_21; lean_object* x_22; 
x_20 = lean_usize_of_nat(x_13);
x_21 = lean_usize_of_nat(x_14);
lean_dec(x_14);
x_22 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_12, x_20, x_21, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_12);
return x_22;
}
}
}
case 4:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_2, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_2, 1);
lean_inc(x_24);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_25 = lean_apply_8(x_1, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_25, 1);
x_28 = lean_ctor_get(x_25, 0);
lean_dec(x_28);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_24);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
uint8_t x_33; 
x_33 = lean_nat_dec_le(x_30, x_30);
if (x_33 == 0)
{
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_25, 0, x_31);
return x_25;
}
else
{
size_t x_34; size_t x_35; lean_object* x_36; 
lean_free_object(x_25);
x_34 = lean_usize_of_nat(x_29);
x_35 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_36 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_24, x_34, x_35, x_31, x_3, x_4, x_5, x_6, x_7, x_8, x_27);
lean_dec(x_24);
return x_36;
}
}
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_37 = lean_ctor_get(x_25, 1);
lean_inc(x_37);
lean_dec(x_25);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_array_get_size(x_24);
x_40 = lean_box(0);
x_41 = lean_nat_dec_lt(x_38, x_39);
if (x_41 == 0)
{
lean_object* x_42; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_37);
return x_42;
}
else
{
uint8_t x_43; 
x_43 = lean_nat_dec_le(x_39, x_39);
if (x_43 == 0)
{
lean_object* x_44; 
lean_dec(x_39);
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_40);
lean_ctor_set(x_44, 1, x_37);
return x_44;
}
else
{
size_t x_45; size_t x_46; lean_object* x_47; 
x_45 = lean_usize_of_nat(x_38);
x_46 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_47 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_24, x_45, x_46, x_40, x_3, x_4, x_5, x_6, x_7, x_8, x_37);
lean_dec(x_24);
return x_47;
}
}
}
}
else
{
lean_dec(x_24);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_25;
}
}
default: 
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_9);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_2, 3);
lean_inc(x_13);
lean_dec(x_2);
x_14 = l_Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3(x_1, x_13, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
return x_14;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 2);
lean_inc(x_10);
lean_dec(x_2);
x_11 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_5);
x_14 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_15 = l_Lean_Compiler_LCNF_Param_forFVarM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__7(x_1, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_unsigned_to_nat(1u);
x_19 = lean_usize_of_nat(x_18);
x_20 = lean_usize_add(x_3, x_19);
x_3 = x_20;
x_5 = x_16;
x_12 = x_17;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_15;
}
}
else
{
lean_object* x_22; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_12);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = lean_apply_8(x_2, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_apply_8(x_2, x_12, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_3, x_4);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_5);
lean_inc(x_1);
x_14 = lean_alloc_closure((void*)(l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10___lam__0), 9, 1);
lean_closure_set(x_14, 0, x_1);
x_15 = lean_array_uget(x_2, x_3);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_16 = l_Lean_Compiler_LCNF_AltCore_forCodeM___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__9(x_15, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; 
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_3, x_20);
x_3 = x_21;
x_5 = x_17;
x_12 = x_18;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_object* x_23; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_5);
lean_ctor_set(x_23, 1, x_12);
return x_23;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_2, 2);
lean_inc(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_20);
x_23 = lean_nat_dec_lt(x_21, x_22);
if (x_23 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_11 = x_10;
goto block_19;
}
else
{
uint8_t x_24; 
x_24 = lean_nat_dec_le(x_22, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_20);
x_11 = x_10;
goto block_19;
}
else
{
lean_object* x_25; size_t x_26; size_t x_27; lean_object* x_28; 
x_25 = lean_box(0);
x_26 = lean_usize_of_nat(x_21);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__8(x_1, x_20, x_26, x_27, x_25, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_20);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_11 = x_29;
goto block_19;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_28;
}
}
}
block_19:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 3);
lean_inc(x_12);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_13 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 4);
lean_inc(x_15);
lean_dec(x_2);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_1);
x_16 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(x_1, x_15, x_4, x_5, x_6, x_7, x_8, x_9, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_17);
return x_18;
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_16;
}
}
else
{
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_2)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_2, 1);
lean_inc(x_11);
lean_dec(x_2);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_2 = x_11;
x_9 = x_13;
goto _start;
}
else
{
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_12;
}
}
case 3:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_2, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_2, 1);
lean_inc(x_16);
lean_dec(x_2);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = lean_apply_8(x_1, x_15, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_19 = lean_ctor_get(x_17, 1);
x_20 = lean_ctor_get(x_17, 0);
lean_dec(x_20);
x_21 = lean_unsigned_to_nat(0u);
x_22 = lean_array_get_size(x_16);
x_23 = lean_box(0);
x_24 = lean_nat_dec_lt(x_21, x_22);
if (x_24 == 0)
{
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
uint8_t x_25; 
x_25 = lean_nat_dec_le(x_22, x_22);
if (x_25 == 0)
{
lean_dec(x_22);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_17, 0, x_23);
return x_17;
}
else
{
size_t x_26; size_t x_27; lean_object* x_28; 
lean_free_object(x_17);
x_26 = lean_usize_of_nat(x_21);
x_27 = lean_usize_of_nat(x_22);
lean_dec(x_22);
x_28 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_16, x_26, x_27, x_23, x_3, x_4, x_5, x_6, x_7, x_8, x_19);
lean_dec(x_16);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; 
x_29 = lean_ctor_get(x_17, 1);
lean_inc(x_29);
lean_dec(x_17);
x_30 = lean_unsigned_to_nat(0u);
x_31 = lean_array_get_size(x_16);
x_32 = lean_box(0);
x_33 = lean_nat_dec_lt(x_30, x_31);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_29);
return x_34;
}
else
{
uint8_t x_35; 
x_35 = lean_nat_dec_le(x_31, x_31);
if (x_35 == 0)
{
lean_object* x_36; 
lean_dec(x_31);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_32);
lean_ctor_set(x_36, 1, x_29);
return x_36;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
x_37 = lean_usize_of_nat(x_30);
x_38 = lean_usize_of_nat(x_31);
lean_dec(x_31);
x_39 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_16, x_37, x_38, x_32, x_3, x_4, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_16);
return x_39;
}
}
}
}
else
{
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_17;
}
}
case 4:
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_40 = lean_ctor_get(x_2, 0);
lean_inc(x_40);
lean_dec(x_2);
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_42 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_41, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_42, 1);
lean_inc(x_43);
lean_dec(x_42);
x_44 = lean_ctor_get(x_40, 2);
lean_inc(x_44);
lean_inc(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_45 = lean_apply_8(x_1, x_44, x_3, x_4, x_5, x_6, x_7, x_8, x_43);
if (lean_obj_tag(x_45) == 0)
{
uint8_t x_46; 
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_47 = lean_ctor_get(x_45, 1);
x_48 = lean_ctor_get(x_45, 0);
lean_dec(x_48);
x_49 = lean_ctor_get(x_40, 3);
lean_inc(x_49);
lean_dec(x_40);
x_50 = lean_unsigned_to_nat(0u);
x_51 = lean_array_get_size(x_49);
x_52 = lean_box(0);
x_53 = lean_nat_dec_lt(x_50, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_45, 0, x_52);
return x_45;
}
else
{
uint8_t x_54; 
x_54 = lean_nat_dec_le(x_51, x_51);
if (x_54 == 0)
{
lean_dec(x_51);
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
lean_ctor_set(x_45, 0, x_52);
return x_45;
}
else
{
size_t x_55; size_t x_56; lean_object* x_57; 
lean_free_object(x_45);
x_55 = lean_usize_of_nat(x_50);
x_56 = lean_usize_of_nat(x_51);
lean_dec(x_51);
x_57 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10(x_1, x_49, x_55, x_56, x_52, x_3, x_4, x_5, x_6, x_7, x_8, x_47);
lean_dec(x_49);
return x_57;
}
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_58 = lean_ctor_get(x_45, 1);
lean_inc(x_58);
lean_dec(x_45);
x_59 = lean_ctor_get(x_40, 3);
lean_inc(x_59);
lean_dec(x_40);
x_60 = lean_unsigned_to_nat(0u);
x_61 = lean_array_get_size(x_59);
x_62 = lean_box(0);
x_63 = lean_nat_dec_lt(x_60, x_61);
if (x_63 == 0)
{
lean_object* x_64; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_58);
return x_64;
}
else
{
uint8_t x_65; 
x_65 = lean_nat_dec_le(x_61, x_61);
if (x_65 == 0)
{
lean_object* x_66; 
lean_dec(x_61);
lean_dec(x_59);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_66 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_66, 0, x_62);
lean_ctor_set(x_66, 1, x_58);
return x_66;
}
else
{
size_t x_67; size_t x_68; lean_object* x_69; 
x_67 = lean_usize_of_nat(x_60);
x_68 = lean_usize_of_nat(x_61);
lean_dec(x_61);
x_69 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10(x_1, x_59, x_67, x_68, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_58);
lean_dec(x_59);
return x_69;
}
}
}
}
else
{
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_45;
}
}
else
{
lean_dec(x_40);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_42;
}
}
case 5:
{
lean_object* x_70; lean_object* x_71; 
x_70 = lean_ctor_get(x_2, 0);
lean_inc(x_70);
lean_dec(x_2);
x_71 = lean_apply_8(x_1, x_70, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_71;
}
case 6:
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec(x_2);
x_73 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_72, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_73;
}
default: 
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_74 = lean_ctor_get(x_2, 0);
lean_inc(x_74);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
x_76 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7___lam__0(x_1, x_74, x_75, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_76;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_17 = lean_ctor_get(x_2, 2);
lean_inc(x_17);
x_18 = lean_unsigned_to_nat(0u);
x_19 = lean_array_get_size(x_17);
x_20 = lean_nat_dec_lt(x_18, x_19);
if (x_20 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
x_10 = x_9;
goto block_16;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_19, x_19);
if (x_21 == 0)
{
lean_dec(x_19);
lean_dec(x_17);
x_10 = x_9;
goto block_16;
}
else
{
lean_object* x_22; size_t x_23; size_t x_24; lean_object* x_25; 
x_22 = lean_box(0);
x_23 = lean_usize_of_nat(x_18);
x_24 = lean_usize_of_nat(x_19);
lean_dec(x_19);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__8(x_1, x_17, x_23, x_24, x_22, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_17);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; 
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_10 = x_26;
goto block_16;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_25;
}
}
}
block_16:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 3);
lean_inc(x_11);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_1);
x_12 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_2, 4);
lean_inc(x_14);
lean_dec(x_2);
x_15 = l_Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7(x_1, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
return x_15;
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; lean_object* x_21; lean_object* x_154; 
x_20 = l_instInhabitedList(lean_box(0));
x_154 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_dontFloat_goFVar___boxed), 8, 0);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_155; lean_object* x_156; 
x_155 = lean_ctor_get(x_1, 0);
lean_inc(x_155);
lean_inc(x_2);
x_156 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(x_154, x_155, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_21 = x_156;
goto block_153;
}
else
{
lean_object* x_157; lean_object* x_158; 
x_157 = lean_ctor_get(x_1, 0);
lean_inc(x_157);
lean_inc(x_2);
x_158 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(x_154, x_157, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_21 = x_158;
goto block_153;
}
block_19:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_11);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_st_ref_set(x_2, x_13, x_10);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_9);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_9);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
block_153:
{
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_22 = lean_ctor_get(x_21, 1);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_st_ref_take(x_2, x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_24, 1);
lean_inc(x_25);
x_26 = !lean_is_exclusive(x_23);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; lean_object* x_37; uint64_t x_38; uint64_t x_39; uint64_t x_40; size_t x_41; size_t x_42; lean_object* x_43; size_t x_44; size_t x_45; size_t x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; 
x_27 = lean_ctor_get(x_23, 1);
x_28 = lean_ctor_get(x_23, 0);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 1);
lean_inc(x_29);
x_30 = lean_box(2);
x_31 = lean_array_get_size(x_29);
x_32 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_30);
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
x_47 = lean_ctor_get(x_25, 0);
lean_inc(x_47);
x_48 = lean_ctor_get(x_25, 1);
lean_inc(x_48);
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; size_t x_57; size_t x_58; size_t x_59; lean_object* x_60; uint8_t x_61; 
x_50 = lean_ctor_get(x_25, 1);
lean_dec(x_50);
x_51 = lean_ctor_get(x_25, 0);
lean_dec(x_51);
x_52 = lean_array_uget(x_29, x_46);
lean_dec(x_29);
x_53 = lean_box(0);
x_54 = lean_ctor_get(x_24, 0);
lean_inc(x_54);
lean_dec(x_24);
x_55 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_20, x_30, x_52);
lean_dec(x_52);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_55);
lean_ctor_set(x_23, 0, x_1);
x_56 = lean_array_get_size(x_48);
x_57 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_58 = lean_usize_sub(x_57, x_44);
x_59 = lean_usize_land(x_41, x_58);
x_60 = lean_array_uget(x_48, x_59);
x_61 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_30, x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_70; 
x_62 = lean_nat_add(x_47, x_43);
lean_dec(x_47);
x_63 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_63, 0, x_30);
lean_ctor_set(x_63, 1, x_23);
lean_ctor_set(x_63, 2, x_60);
x_64 = lean_array_uset(x_48, x_59, x_63);
x_65 = lean_unsigned_to_nat(2u);
x_66 = lean_nat_shiftl(x_62, x_65);
x_67 = lean_unsigned_to_nat(3u);
x_68 = lean_nat_div(x_66, x_67);
lean_dec(x_66);
x_69 = lean_array_get_size(x_64);
x_70 = lean_nat_dec_le(x_68, x_69);
lean_dec(x_69);
lean_dec(x_68);
if (x_70 == 0)
{
lean_object* x_71; 
x_71 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_64);
lean_ctor_set(x_25, 1, x_71);
lean_ctor_set(x_25, 0, x_62);
x_9 = x_53;
x_10 = x_27;
x_11 = x_54;
x_12 = x_25;
goto block_19;
}
else
{
lean_ctor_set(x_25, 1, x_64);
lean_ctor_set(x_25, 0, x_62);
x_9 = x_53;
x_10 = x_27;
x_11 = x_54;
x_12 = x_25;
goto block_19;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_72 = lean_box(0);
x_73 = lean_array_uset(x_48, x_59, x_72);
x_74 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_30, x_23, x_60);
x_75 = lean_array_uset(x_73, x_59, x_74);
lean_ctor_set(x_25, 1, x_75);
x_9 = x_53;
x_10 = x_27;
x_11 = x_54;
x_12 = x_25;
goto block_19;
}
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; size_t x_81; size_t x_82; size_t x_83; lean_object* x_84; uint8_t x_85; 
lean_dec(x_25);
x_76 = lean_array_uget(x_29, x_46);
lean_dec(x_29);
x_77 = lean_box(0);
x_78 = lean_ctor_get(x_24, 0);
lean_inc(x_78);
lean_dec(x_24);
x_79 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_20, x_30, x_76);
lean_dec(x_76);
lean_ctor_set_tag(x_23, 1);
lean_ctor_set(x_23, 1, x_79);
lean_ctor_set(x_23, 0, x_1);
x_80 = lean_array_get_size(x_48);
x_81 = lean_usize_of_nat(x_80);
lean_dec(x_80);
x_82 = lean_usize_sub(x_81, x_44);
x_83 = lean_usize_land(x_41, x_82);
x_84 = lean_array_uget(x_48, x_83);
x_85 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_30, x_84);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_86 = lean_nat_add(x_47, x_43);
lean_dec(x_47);
x_87 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_87, 0, x_30);
lean_ctor_set(x_87, 1, x_23);
lean_ctor_set(x_87, 2, x_84);
x_88 = lean_array_uset(x_48, x_83, x_87);
x_89 = lean_unsigned_to_nat(2u);
x_90 = lean_nat_shiftl(x_86, x_89);
x_91 = lean_unsigned_to_nat(3u);
x_92 = lean_nat_div(x_90, x_91);
lean_dec(x_90);
x_93 = lean_array_get_size(x_88);
x_94 = lean_nat_dec_le(x_92, x_93);
lean_dec(x_93);
lean_dec(x_92);
if (x_94 == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_88);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_86);
lean_ctor_set(x_96, 1, x_95);
x_9 = x_77;
x_10 = x_27;
x_11 = x_78;
x_12 = x_96;
goto block_19;
}
else
{
lean_object* x_97; 
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_86);
lean_ctor_set(x_97, 1, x_88);
x_9 = x_77;
x_10 = x_27;
x_11 = x_78;
x_12 = x_97;
goto block_19;
}
}
else
{
lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_98 = lean_box(0);
x_99 = lean_array_uset(x_48, x_83, x_98);
x_100 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_30, x_23, x_84);
x_101 = lean_array_uset(x_99, x_83, x_100);
x_102 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_102, 0, x_47);
lean_ctor_set(x_102, 1, x_101);
x_9 = x_77;
x_10 = x_27;
x_11 = x_78;
x_12 = x_102;
goto block_19;
}
}
}
else
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; uint64_t x_107; lean_object* x_108; uint64_t x_109; uint64_t x_110; uint64_t x_111; lean_object* x_112; uint64_t x_113; uint64_t x_114; uint64_t x_115; size_t x_116; size_t x_117; lean_object* x_118; size_t x_119; size_t x_120; size_t x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; size_t x_131; size_t x_132; size_t x_133; lean_object* x_134; uint8_t x_135; 
x_103 = lean_ctor_get(x_23, 1);
lean_inc(x_103);
lean_dec(x_23);
x_104 = lean_ctor_get(x_25, 1);
lean_inc(x_104);
x_105 = lean_box(2);
x_106 = lean_array_get_size(x_104);
x_107 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_105);
x_108 = lean_unsigned_to_nat(32u);
x_109 = lean_uint64_of_nat(x_108);
x_110 = lean_uint64_shift_right(x_107, x_109);
x_111 = lean_uint64_xor(x_107, x_110);
x_112 = lean_unsigned_to_nat(16u);
x_113 = lean_uint64_of_nat(x_112);
x_114 = lean_uint64_shift_right(x_111, x_113);
x_115 = lean_uint64_xor(x_111, x_114);
x_116 = lean_uint64_to_usize(x_115);
x_117 = lean_usize_of_nat(x_106);
lean_dec(x_106);
x_118 = lean_unsigned_to_nat(1u);
x_119 = lean_usize_of_nat(x_118);
x_120 = lean_usize_sub(x_117, x_119);
x_121 = lean_usize_land(x_116, x_120);
x_122 = lean_ctor_get(x_25, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_25, 1);
lean_inc(x_123);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_124 = x_25;
} else {
 lean_dec_ref(x_25);
 x_124 = lean_box(0);
}
x_125 = lean_array_uget(x_104, x_121);
lean_dec(x_104);
x_126 = lean_box(0);
x_127 = lean_ctor_get(x_24, 0);
lean_inc(x_127);
lean_dec(x_24);
x_128 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_20, x_105, x_125);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_1);
lean_ctor_set(x_129, 1, x_128);
x_130 = lean_array_get_size(x_123);
x_131 = lean_usize_of_nat(x_130);
lean_dec(x_130);
x_132 = lean_usize_sub(x_131, x_119);
x_133 = lean_usize_land(x_116, x_132);
x_134 = lean_array_uget(x_123, x_133);
x_135 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_105, x_134);
if (x_135 == 0)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_136 = lean_nat_add(x_122, x_118);
lean_dec(x_122);
x_137 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_137, 0, x_105);
lean_ctor_set(x_137, 1, x_129);
lean_ctor_set(x_137, 2, x_134);
x_138 = lean_array_uset(x_123, x_133, x_137);
x_139 = lean_unsigned_to_nat(2u);
x_140 = lean_nat_shiftl(x_136, x_139);
x_141 = lean_unsigned_to_nat(3u);
x_142 = lean_nat_div(x_140, x_141);
lean_dec(x_140);
x_143 = lean_array_get_size(x_138);
x_144 = lean_nat_dec_le(x_142, x_143);
lean_dec(x_143);
lean_dec(x_142);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; 
x_145 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_138);
if (lean_is_scalar(x_124)) {
 x_146 = lean_alloc_ctor(0, 2, 0);
} else {
 x_146 = x_124;
}
lean_ctor_set(x_146, 0, x_136);
lean_ctor_set(x_146, 1, x_145);
x_9 = x_126;
x_10 = x_103;
x_11 = x_127;
x_12 = x_146;
goto block_19;
}
else
{
lean_object* x_147; 
if (lean_is_scalar(x_124)) {
 x_147 = lean_alloc_ctor(0, 2, 0);
} else {
 x_147 = x_124;
}
lean_ctor_set(x_147, 0, x_136);
lean_ctor_set(x_147, 1, x_138);
x_9 = x_126;
x_10 = x_103;
x_11 = x_127;
x_12 = x_147;
goto block_19;
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_box(0);
x_149 = lean_array_uset(x_123, x_133, x_148);
x_150 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_105, x_129, x_134);
x_151 = lean_array_uset(x_149, x_133, x_150);
if (lean_is_scalar(x_124)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_124;
}
lean_ctor_set(x_152, 0, x_122);
lean_ctor_set(x_152, 1, x_151);
x_9 = x_126;
x_10 = x_103;
x_11 = x_127;
x_12 = x_152;
goto block_19;
}
}
}
else
{
lean_dec(x_20);
lean_dec(x_2);
lean_dec(x_1);
return x_21;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_5);
lean_dec(x_5);
x_14 = l_Lean_Compiler_LCNF_Expr_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__1___lam__0(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_LetValue_forFVarM___at___Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1_spec__3_spec__4(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__8(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Code_forFVarM___at___Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7_spec__7_spec__10(x_1, x_2, x_13, x_14, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
lean_dec(x_6);
x_8 = !lean_is_exclusive(x_5);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint64_t x_13; lean_object* x_14; uint64_t x_15; uint64_t x_16; uint64_t x_17; lean_object* x_18; uint64_t x_19; uint64_t x_20; uint64_t x_21; size_t x_22; size_t x_23; lean_object* x_24; size_t x_25; size_t x_26; size_t x_27; lean_object* x_28; lean_object* x_29; 
x_9 = lean_ctor_get(x_5, 1);
x_10 = lean_ctor_get(x_5, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_7, 1);
lean_inc(x_11);
lean_dec(x_7);
x_12 = lean_array_get_size(x_11);
x_13 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_14 = lean_unsigned_to_nat(32u);
x_15 = lean_uint64_of_nat(x_14);
x_16 = lean_uint64_shift_right(x_13, x_15);
x_17 = lean_uint64_xor(x_13, x_16);
x_18 = lean_unsigned_to_nat(16u);
x_19 = lean_uint64_of_nat(x_18);
x_20 = lean_uint64_shift_right(x_17, x_19);
x_21 = lean_uint64_xor(x_17, x_20);
x_22 = lean_uint64_to_usize(x_21);
x_23 = lean_usize_of_nat(x_12);
lean_dec(x_12);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_usize_of_nat(x_24);
x_26 = lean_usize_sub(x_23, x_25);
x_27 = lean_usize_land(x_22, x_26);
x_28 = lean_array_uget(x_11, x_27);
lean_dec(x_11);
x_29 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_28);
lean_dec(x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; 
lean_dec(x_2);
lean_dec(x_1);
x_30 = lean_box(0);
lean_ctor_set(x_5, 0, x_30);
return x_5;
}
else
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_31, x_2);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_dec(x_31);
lean_free_object(x_5);
lean_dec(x_2);
x_33 = lean_st_ref_take(x_3, x_9);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_33, 1);
lean_inc(x_36);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_37 = x_33;
} else {
 lean_dec_ref(x_33);
 x_37 = lean_box(0);
}
x_38 = !lean_is_exclusive(x_35);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_51; lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; uint8_t x_57; 
x_39 = lean_ctor_get(x_35, 0);
x_40 = lean_ctor_get(x_35, 1);
x_41 = lean_box(0);
x_51 = lean_box(2);
x_52 = lean_array_get_size(x_40);
x_53 = lean_usize_of_nat(x_52);
lean_dec(x_52);
x_54 = lean_usize_sub(x_53, x_25);
x_55 = lean_usize_land(x_22, x_54);
x_56 = lean_array_uget(x_40, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_nat_add(x_39, x_24);
lean_dec(x_39);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_1);
lean_ctor_set(x_59, 1, x_51);
lean_ctor_set(x_59, 2, x_56);
x_60 = lean_array_uset(x_40, x_55, x_59);
x_61 = lean_unsigned_to_nat(2u);
x_62 = lean_nat_shiftl(x_58, x_61);
x_63 = lean_unsigned_to_nat(3u);
x_64 = lean_nat_div(x_62, x_63);
lean_dec(x_62);
x_65 = lean_array_get_size(x_60);
x_66 = lean_nat_dec_le(x_64, x_65);
lean_dec(x_65);
lean_dec(x_64);
if (x_66 == 0)
{
lean_object* x_67; 
x_67 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_60);
lean_ctor_set(x_35, 1, x_67);
lean_ctor_set(x_35, 0, x_58);
x_42 = x_35;
goto block_50;
}
else
{
lean_ctor_set(x_35, 1, x_60);
lean_ctor_set(x_35, 0, x_58);
x_42 = x_35;
goto block_50;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_box(0);
x_69 = lean_array_uset(x_40, x_55, x_68);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_51, x_56);
x_71 = lean_array_uset(x_69, x_55, x_70);
lean_ctor_set(x_35, 1, x_71);
x_42 = x_35;
goto block_50;
}
block_50:
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; uint8_t x_46; 
x_43 = lean_ctor_get(x_34, 1);
lean_inc(x_43);
lean_dec(x_34);
if (lean_is_scalar(x_37)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_37;
}
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_st_ref_set(x_3, x_44, x_36);
x_46 = !lean_is_exclusive(x_45);
if (x_46 == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_45, 0);
lean_dec(x_47);
lean_ctor_set(x_45, 0, x_41);
return x_45;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_45, 1);
lean_inc(x_48);
lean_dec(x_45);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_41);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_83; lean_object* x_84; size_t x_85; size_t x_86; size_t x_87; lean_object* x_88; uint8_t x_89; 
x_72 = lean_ctor_get(x_35, 0);
x_73 = lean_ctor_get(x_35, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_35);
x_74 = lean_box(0);
x_83 = lean_box(2);
x_84 = lean_array_get_size(x_73);
x_85 = lean_usize_of_nat(x_84);
lean_dec(x_84);
x_86 = lean_usize_sub(x_85, x_25);
x_87 = lean_usize_land(x_22, x_86);
x_88 = lean_array_uget(x_73, x_87);
x_89 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_88);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint8_t x_98; 
x_90 = lean_nat_add(x_72, x_24);
lean_dec(x_72);
x_91 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_91, 0, x_1);
lean_ctor_set(x_91, 1, x_83);
lean_ctor_set(x_91, 2, x_88);
x_92 = lean_array_uset(x_73, x_87, x_91);
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
x_99 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_92);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_90);
lean_ctor_set(x_100, 1, x_99);
x_75 = x_100;
goto block_82;
}
else
{
lean_object* x_101; 
x_101 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_101, 0, x_90);
lean_ctor_set(x_101, 1, x_92);
x_75 = x_101;
goto block_82;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; 
x_102 = lean_box(0);
x_103 = lean_array_uset(x_73, x_87, x_102);
x_104 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_83, x_88);
x_105 = lean_array_uset(x_103, x_87, x_104);
x_106 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_106, 0, x_72);
lean_ctor_set(x_106, 1, x_105);
x_75 = x_106;
goto block_82;
}
block_82:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_76 = lean_ctor_get(x_34, 1);
lean_inc(x_76);
lean_dec(x_34);
if (lean_is_scalar(x_37)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_37;
}
lean_ctor_set(x_77, 0, x_75);
lean_ctor_set(x_77, 1, x_76);
x_78 = lean_st_ref_set(x_3, x_77, x_36);
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
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 2, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_74);
lean_ctor_set(x_81, 1, x_79);
return x_81;
}
}
}
else
{
lean_object* x_107; uint8_t x_108; 
x_107 = lean_box(3);
x_108 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_31, x_107);
lean_dec(x_31);
if (x_108 == 0)
{
lean_object* x_109; 
lean_dec(x_2);
lean_dec(x_1);
x_109 = lean_box(0);
lean_ctor_set(x_5, 0, x_109);
return x_5;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; uint8_t x_115; 
lean_free_object(x_5);
x_110 = lean_st_ref_take(x_3, x_9);
x_111 = lean_ctor_get(x_110, 0);
lean_inc(x_111);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_110, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_110)) {
 lean_ctor_release(x_110, 0);
 lean_ctor_release(x_110, 1);
 x_114 = x_110;
} else {
 lean_dec_ref(x_110);
 x_114 = lean_box(0);
}
x_115 = !lean_is_exclusive(x_112);
if (x_115 == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_128; size_t x_129; size_t x_130; size_t x_131; lean_object* x_132; uint8_t x_133; 
x_116 = lean_ctor_get(x_112, 0);
x_117 = lean_ctor_get(x_112, 1);
x_118 = lean_box(0);
x_128 = lean_array_get_size(x_117);
x_129 = lean_usize_of_nat(x_128);
lean_dec(x_128);
x_130 = lean_usize_sub(x_129, x_25);
x_131 = lean_usize_land(x_22, x_130);
x_132 = lean_array_uget(x_117, x_131);
x_133 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_132);
if (x_133 == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_134 = lean_nat_add(x_116, x_24);
lean_dec(x_116);
x_135 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_135, 0, x_1);
lean_ctor_set(x_135, 1, x_2);
lean_ctor_set(x_135, 2, x_132);
x_136 = lean_array_uset(x_117, x_131, x_135);
x_137 = lean_unsigned_to_nat(2u);
x_138 = lean_nat_shiftl(x_134, x_137);
x_139 = lean_unsigned_to_nat(3u);
x_140 = lean_nat_div(x_138, x_139);
lean_dec(x_138);
x_141 = lean_array_get_size(x_136);
x_142 = lean_nat_dec_le(x_140, x_141);
lean_dec(x_141);
lean_dec(x_140);
if (x_142 == 0)
{
lean_object* x_143; 
x_143 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_136);
lean_ctor_set(x_112, 1, x_143);
lean_ctor_set(x_112, 0, x_134);
x_119 = x_112;
goto block_127;
}
else
{
lean_ctor_set(x_112, 1, x_136);
lean_ctor_set(x_112, 0, x_134);
x_119 = x_112;
goto block_127;
}
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_box(0);
x_145 = lean_array_uset(x_117, x_131, x_144);
x_146 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_2, x_132);
x_147 = lean_array_uset(x_145, x_131, x_146);
lean_ctor_set(x_112, 1, x_147);
x_119 = x_112;
goto block_127;
}
block_127:
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; uint8_t x_123; 
x_120 = lean_ctor_get(x_111, 1);
lean_inc(x_120);
lean_dec(x_111);
if (lean_is_scalar(x_114)) {
 x_121 = lean_alloc_ctor(0, 2, 0);
} else {
 x_121 = x_114;
}
lean_ctor_set(x_121, 0, x_119);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_st_ref_set(x_3, x_121, x_113);
x_123 = !lean_is_exclusive(x_122);
if (x_123 == 0)
{
lean_object* x_124; 
x_124 = lean_ctor_get(x_122, 0);
lean_dec(x_124);
lean_ctor_set(x_122, 0, x_118);
return x_122;
}
else
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_122, 1);
lean_inc(x_125);
lean_dec(x_122);
x_126 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_126, 0, x_118);
lean_ctor_set(x_126, 1, x_125);
return x_126;
}
}
}
else
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_159; size_t x_160; size_t x_161; size_t x_162; lean_object* x_163; uint8_t x_164; 
x_148 = lean_ctor_get(x_112, 0);
x_149 = lean_ctor_get(x_112, 1);
lean_inc(x_149);
lean_inc(x_148);
lean_dec(x_112);
x_150 = lean_box(0);
x_159 = lean_array_get_size(x_149);
x_160 = lean_usize_of_nat(x_159);
lean_dec(x_159);
x_161 = lean_usize_sub(x_160, x_25);
x_162 = lean_usize_land(x_22, x_161);
x_163 = lean_array_uget(x_149, x_162);
x_164 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
x_165 = lean_nat_add(x_148, x_24);
lean_dec(x_148);
x_166 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_166, 0, x_1);
lean_ctor_set(x_166, 1, x_2);
lean_ctor_set(x_166, 2, x_163);
x_167 = lean_array_uset(x_149, x_162, x_166);
x_168 = lean_unsigned_to_nat(2u);
x_169 = lean_nat_shiftl(x_165, x_168);
x_170 = lean_unsigned_to_nat(3u);
x_171 = lean_nat_div(x_169, x_170);
lean_dec(x_169);
x_172 = lean_array_get_size(x_167);
x_173 = lean_nat_dec_le(x_171, x_172);
lean_dec(x_172);
lean_dec(x_171);
if (x_173 == 0)
{
lean_object* x_174; lean_object* x_175; 
x_174 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_167);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_165);
lean_ctor_set(x_175, 1, x_174);
x_151 = x_175;
goto block_158;
}
else
{
lean_object* x_176; 
x_176 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_176, 0, x_165);
lean_ctor_set(x_176, 1, x_167);
x_151 = x_176;
goto block_158;
}
}
else
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_177 = lean_box(0);
x_178 = lean_array_uset(x_149, x_162, x_177);
x_179 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_2, x_163);
x_180 = lean_array_uset(x_178, x_162, x_179);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_148);
lean_ctor_set(x_181, 1, x_180);
x_151 = x_181;
goto block_158;
}
block_158:
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_152 = lean_ctor_get(x_111, 1);
lean_inc(x_152);
lean_dec(x_111);
if (lean_is_scalar(x_114)) {
 x_153 = lean_alloc_ctor(0, 2, 0);
} else {
 x_153 = x_114;
}
lean_ctor_set(x_153, 0, x_151);
lean_ctor_set(x_153, 1, x_152);
x_154 = lean_st_ref_set(x_3, x_153, x_113);
x_155 = lean_ctor_get(x_154, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_154)) {
 lean_ctor_release(x_154, 0);
 lean_ctor_release(x_154, 1);
 x_156 = x_154;
} else {
 lean_dec_ref(x_154);
 x_156 = lean_box(0);
}
if (lean_is_scalar(x_156)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_156;
}
lean_ctor_set(x_157, 0, x_150);
lean_ctor_set(x_157, 1, x_155);
return x_157;
}
}
}
}
}
}
else
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; uint64_t x_185; lean_object* x_186; uint64_t x_187; uint64_t x_188; uint64_t x_189; lean_object* x_190; uint64_t x_191; uint64_t x_192; uint64_t x_193; size_t x_194; size_t x_195; lean_object* x_196; size_t x_197; size_t x_198; size_t x_199; lean_object* x_200; lean_object* x_201; 
x_182 = lean_ctor_get(x_5, 1);
lean_inc(x_182);
lean_dec(x_5);
x_183 = lean_ctor_get(x_7, 1);
lean_inc(x_183);
lean_dec(x_7);
x_184 = lean_array_get_size(x_183);
x_185 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_186 = lean_unsigned_to_nat(32u);
x_187 = lean_uint64_of_nat(x_186);
x_188 = lean_uint64_shift_right(x_185, x_187);
x_189 = lean_uint64_xor(x_185, x_188);
x_190 = lean_unsigned_to_nat(16u);
x_191 = lean_uint64_of_nat(x_190);
x_192 = lean_uint64_shift_right(x_189, x_191);
x_193 = lean_uint64_xor(x_189, x_192);
x_194 = lean_uint64_to_usize(x_193);
x_195 = lean_usize_of_nat(x_184);
lean_dec(x_184);
x_196 = lean_unsigned_to_nat(1u);
x_197 = lean_usize_of_nat(x_196);
x_198 = lean_usize_sub(x_195, x_197);
x_199 = lean_usize_land(x_194, x_198);
x_200 = lean_array_uget(x_183, x_199);
lean_dec(x_183);
x_201 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_1, x_200);
lean_dec(x_200);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; 
lean_dec(x_2);
lean_dec(x_1);
x_202 = lean_box(0);
x_203 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_203, 0, x_202);
lean_ctor_set(x_203, 1, x_182);
return x_203;
}
else
{
lean_object* x_204; uint8_t x_205; 
x_204 = lean_ctor_get(x_201, 0);
lean_inc(x_204);
lean_dec(x_201);
x_205 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_204, x_2);
if (x_205 == 0)
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_223; lean_object* x_224; size_t x_225; size_t x_226; size_t x_227; lean_object* x_228; uint8_t x_229; 
lean_dec(x_204);
lean_dec(x_2);
x_206 = lean_st_ref_take(x_3, x_182);
x_207 = lean_ctor_get(x_206, 0);
lean_inc(x_207);
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
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
x_211 = lean_ctor_get(x_208, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_208, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_208)) {
 lean_ctor_release(x_208, 0);
 lean_ctor_release(x_208, 1);
 x_213 = x_208;
} else {
 lean_dec_ref(x_208);
 x_213 = lean_box(0);
}
x_214 = lean_box(0);
x_223 = lean_box(2);
x_224 = lean_array_get_size(x_212);
x_225 = lean_usize_of_nat(x_224);
lean_dec(x_224);
x_226 = lean_usize_sub(x_225, x_197);
x_227 = lean_usize_land(x_194, x_226);
x_228 = lean_array_uget(x_212, x_227);
x_229 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_228);
if (x_229 == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; uint8_t x_238; 
x_230 = lean_nat_add(x_211, x_196);
lean_dec(x_211);
x_231 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_231, 0, x_1);
lean_ctor_set(x_231, 1, x_223);
lean_ctor_set(x_231, 2, x_228);
x_232 = lean_array_uset(x_212, x_227, x_231);
x_233 = lean_unsigned_to_nat(2u);
x_234 = lean_nat_shiftl(x_230, x_233);
x_235 = lean_unsigned_to_nat(3u);
x_236 = lean_nat_div(x_234, x_235);
lean_dec(x_234);
x_237 = lean_array_get_size(x_232);
x_238 = lean_nat_dec_le(x_236, x_237);
lean_dec(x_237);
lean_dec(x_236);
if (x_238 == 0)
{
lean_object* x_239; lean_object* x_240; 
x_239 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_232);
if (lean_is_scalar(x_213)) {
 x_240 = lean_alloc_ctor(0, 2, 0);
} else {
 x_240 = x_213;
}
lean_ctor_set(x_240, 0, x_230);
lean_ctor_set(x_240, 1, x_239);
x_215 = x_240;
goto block_222;
}
else
{
lean_object* x_241; 
if (lean_is_scalar(x_213)) {
 x_241 = lean_alloc_ctor(0, 2, 0);
} else {
 x_241 = x_213;
}
lean_ctor_set(x_241, 0, x_230);
lean_ctor_set(x_241, 1, x_232);
x_215 = x_241;
goto block_222;
}
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_box(0);
x_243 = lean_array_uset(x_212, x_227, x_242);
x_244 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_223, x_228);
x_245 = lean_array_uset(x_243, x_227, x_244);
if (lean_is_scalar(x_213)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_213;
}
lean_ctor_set(x_246, 0, x_211);
lean_ctor_set(x_246, 1, x_245);
x_215 = x_246;
goto block_222;
}
block_222:
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_216 = lean_ctor_get(x_207, 1);
lean_inc(x_216);
lean_dec(x_207);
if (lean_is_scalar(x_210)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_210;
}
lean_ctor_set(x_217, 0, x_215);
lean_ctor_set(x_217, 1, x_216);
x_218 = lean_st_ref_set(x_3, x_217, x_209);
x_219 = lean_ctor_get(x_218, 1);
lean_inc(x_219);
if (lean_is_exclusive(x_218)) {
 lean_ctor_release(x_218, 0);
 lean_ctor_release(x_218, 1);
 x_220 = x_218;
} else {
 lean_dec_ref(x_218);
 x_220 = lean_box(0);
}
if (lean_is_scalar(x_220)) {
 x_221 = lean_alloc_ctor(0, 2, 0);
} else {
 x_221 = x_220;
}
lean_ctor_set(x_221, 0, x_214);
lean_ctor_set(x_221, 1, x_219);
return x_221;
}
}
else
{
lean_object* x_247; uint8_t x_248; 
x_247 = lean_box(3);
x_248 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_204, x_247);
lean_dec(x_204);
if (x_248 == 0)
{
lean_object* x_249; lean_object* x_250; 
lean_dec(x_2);
lean_dec(x_1);
x_249 = lean_box(0);
x_250 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_250, 1, x_182);
return x_250;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_268; size_t x_269; size_t x_270; size_t x_271; lean_object* x_272; uint8_t x_273; 
x_251 = lean_st_ref_take(x_3, x_182);
x_252 = lean_ctor_get(x_251, 0);
lean_inc(x_252);
x_253 = lean_ctor_get(x_252, 0);
lean_inc(x_253);
x_254 = lean_ctor_get(x_251, 1);
lean_inc(x_254);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 lean_ctor_release(x_251, 1);
 x_255 = x_251;
} else {
 lean_dec_ref(x_251);
 x_255 = lean_box(0);
}
x_256 = lean_ctor_get(x_253, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_253, 1);
lean_inc(x_257);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_258 = x_253;
} else {
 lean_dec_ref(x_253);
 x_258 = lean_box(0);
}
x_259 = lean_box(0);
x_268 = lean_array_get_size(x_257);
x_269 = lean_usize_of_nat(x_268);
lean_dec(x_268);
x_270 = lean_usize_sub(x_269, x_197);
x_271 = lean_usize_land(x_194, x_270);
x_272 = lean_array_uget(x_257, x_271);
x_273 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_272);
if (x_273 == 0)
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; uint8_t x_282; 
x_274 = lean_nat_add(x_256, x_196);
lean_dec(x_256);
x_275 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_275, 0, x_1);
lean_ctor_set(x_275, 1, x_2);
lean_ctor_set(x_275, 2, x_272);
x_276 = lean_array_uset(x_257, x_271, x_275);
x_277 = lean_unsigned_to_nat(2u);
x_278 = lean_nat_shiftl(x_274, x_277);
x_279 = lean_unsigned_to_nat(3u);
x_280 = lean_nat_div(x_278, x_279);
lean_dec(x_278);
x_281 = lean_array_get_size(x_276);
x_282 = lean_nat_dec_le(x_280, x_281);
lean_dec(x_281);
lean_dec(x_280);
if (x_282 == 0)
{
lean_object* x_283; lean_object* x_284; 
x_283 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_276);
if (lean_is_scalar(x_258)) {
 x_284 = lean_alloc_ctor(0, 2, 0);
} else {
 x_284 = x_258;
}
lean_ctor_set(x_284, 0, x_274);
lean_ctor_set(x_284, 1, x_283);
x_260 = x_284;
goto block_267;
}
else
{
lean_object* x_285; 
if (lean_is_scalar(x_258)) {
 x_285 = lean_alloc_ctor(0, 2, 0);
} else {
 x_285 = x_258;
}
lean_ctor_set(x_285, 0, x_274);
lean_ctor_set(x_285, 1, x_276);
x_260 = x_285;
goto block_267;
}
}
else
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_box(0);
x_287 = lean_array_uset(x_257, x_271, x_286);
x_288 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_1, x_2, x_272);
x_289 = lean_array_uset(x_287, x_271, x_288);
if (lean_is_scalar(x_258)) {
 x_290 = lean_alloc_ctor(0, 2, 0);
} else {
 x_290 = x_258;
}
lean_ctor_set(x_290, 0, x_256);
lean_ctor_set(x_290, 1, x_289);
x_260 = x_290;
goto block_267;
}
block_267:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_261 = lean_ctor_get(x_252, 1);
lean_inc(x_261);
lean_dec(x_252);
if (lean_is_scalar(x_255)) {
 x_262 = lean_alloc_ctor(0, 2, 0);
} else {
 x_262 = x_255;
}
lean_ctor_set(x_262, 0, x_260);
lean_ctor_set(x_262, 1, x_261);
x_263 = lean_st_ref_set(x_3, x_262, x_254);
x_264 = lean_ctor_get(x_263, 1);
lean_inc(x_264);
if (lean_is_exclusive(x_263)) {
 lean_ctor_release(x_263, 0);
 lean_ctor_release(x_263, 1);
 x_265 = x_263;
} else {
 lean_dec_ref(x_263);
 x_265 = lean_box(0);
}
if (lean_is_scalar(x_265)) {
 x_266 = lean_alloc_ctor(0, 2, 0);
} else {
 x_266 = x_265;
}
lean_ctor_set(x_266, 0, x_259);
lean_ctor_set(x_266, 1, x_264);
return x_266;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(x_1, x_2, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_mk_string_unchecked("Std.Data.DHashMap.Internal.AssocList.Basic", 42, 42);
x_5 = lean_mk_string_unchecked("Std.DHashMap.Internal.AssocList.get!", 36, 36);
x_6 = lean_unsigned_to_nat(138u);
x_7 = lean_unsigned_to_nat(11u);
x_8 = lean_mk_string_unchecked("key is not present in hash table", 32, 32);
x_9 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
x_10 = lean_panic_fn(x_1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
x_11 = lean_ctor_get(x_3, 0);
x_12 = lean_ctor_get(x_3, 1);
x_13 = lean_ctor_get(x_3, 2);
x_14 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_11, x_2);
if (x_14 == 0)
{
x_3 = x_13;
goto _start;
}
else
{
lean_dec(x_1);
lean_inc(x_12);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float_goFVar___redArg(x_2, x_1, x_3, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; lean_object* x_34; uint64_t x_35; uint64_t x_36; uint64_t x_37; size_t x_38; size_t x_39; lean_object* x_40; size_t x_41; size_t x_42; size_t x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_165; 
x_20 = lean_st_ref_get(x_2, x_8);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_ctor_get(x_20, 1);
lean_inc(x_23);
lean_dec(x_20);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
x_26 = l_instInhabitedList(lean_box(0));
x_27 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_1);
x_28 = lean_array_get_size(x_24);
x_29 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_27);
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
x_44 = lean_array_uget(x_24, x_43);
lean_dec(x_24);
x_45 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_25, x_27, x_44);
lean_dec(x_44);
lean_dec(x_27);
lean_inc(x_45);
x_165 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed), 9, 1);
lean_closure_set(x_165, 0, x_45);
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_166; lean_object* x_167; 
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
lean_inc(x_2);
x_167 = l_Lean_Compiler_LCNF_LetDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__1(x_165, x_166, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
x_46 = x_167;
goto block_164;
}
else
{
lean_object* x_168; lean_object* x_169; 
x_168 = lean_ctor_get(x_1, 0);
lean_inc(x_168);
lean_inc(x_2);
x_169 = l_Lean_Compiler_LCNF_FunDecl_forFVarM___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__7(x_165, x_168, x_2, x_3, x_4, x_5, x_6, x_7, x_23);
x_46 = x_169;
goto block_164;
}
block_19:
{
lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_st_ref_set(x_2, x_13, x_9);
lean_dec(x_2);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_ctor_get(x_14, 0);
lean_dec(x_16);
lean_ctor_set(x_14, 0, x_11);
return x_14;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_11);
lean_ctor_set(x_18, 1, x_17);
return x_18;
}
}
block_164:
{
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_48 = lean_st_ref_take(x_2, x_47);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
x_51 = !lean_is_exclusive(x_48);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; uint64_t x_59; uint64_t x_60; size_t x_61; size_t x_62; size_t x_63; size_t x_64; lean_object* x_65; lean_object* x_66; uint8_t x_67; 
x_52 = lean_ctor_get(x_48, 1);
x_53 = lean_ctor_get(x_48, 0);
lean_dec(x_53);
x_54 = lean_ctor_get(x_50, 1);
lean_inc(x_54);
x_55 = lean_array_get_size(x_54);
x_56 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_45);
x_57 = lean_uint64_shift_right(x_56, x_31);
x_58 = lean_uint64_xor(x_56, x_57);
x_59 = lean_uint64_shift_right(x_58, x_35);
x_60 = lean_uint64_xor(x_58, x_59);
x_61 = lean_uint64_to_usize(x_60);
x_62 = lean_usize_of_nat(x_55);
lean_dec(x_55);
x_63 = lean_usize_sub(x_62, x_41);
x_64 = lean_usize_land(x_61, x_63);
x_65 = lean_ctor_get(x_50, 0);
lean_inc(x_65);
x_66 = lean_ctor_get(x_50, 1);
lean_inc(x_66);
x_67 = !lean_is_exclusive(x_50);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; size_t x_75; size_t x_76; size_t x_77; lean_object* x_78; uint8_t x_79; 
x_68 = lean_ctor_get(x_50, 1);
lean_dec(x_68);
x_69 = lean_ctor_get(x_50, 0);
lean_dec(x_69);
x_70 = lean_array_uget(x_54, x_64);
lean_dec(x_54);
x_71 = lean_box(0);
x_72 = lean_ctor_get(x_49, 0);
lean_inc(x_72);
lean_dec(x_49);
x_73 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_26, x_45, x_70);
lean_dec(x_70);
lean_ctor_set_tag(x_48, 1);
lean_ctor_set(x_48, 1, x_73);
lean_ctor_set(x_48, 0, x_1);
x_74 = lean_array_get_size(x_66);
x_75 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_76 = lean_usize_sub(x_75, x_41);
x_77 = lean_usize_land(x_61, x_76);
x_78 = lean_array_uget(x_66, x_77);
x_79 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_45, x_78);
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; 
x_80 = lean_nat_add(x_65, x_40);
lean_dec(x_65);
x_81 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_81, 0, x_45);
lean_ctor_set(x_81, 1, x_48);
lean_ctor_set(x_81, 2, x_78);
x_82 = lean_array_uset(x_66, x_77, x_81);
x_83 = lean_unsigned_to_nat(2u);
x_84 = lean_nat_shiftl(x_80, x_83);
x_85 = lean_unsigned_to_nat(3u);
x_86 = lean_nat_div(x_84, x_85);
lean_dec(x_84);
x_87 = lean_array_get_size(x_82);
x_88 = lean_nat_dec_le(x_86, x_87);
lean_dec(x_87);
lean_dec(x_86);
if (x_88 == 0)
{
lean_object* x_89; 
x_89 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_82);
lean_ctor_set(x_50, 1, x_89);
lean_ctor_set(x_50, 0, x_80);
x_9 = x_52;
x_10 = x_72;
x_11 = x_71;
x_12 = x_50;
goto block_19;
}
else
{
lean_ctor_set(x_50, 1, x_82);
lean_ctor_set(x_50, 0, x_80);
x_9 = x_52;
x_10 = x_72;
x_11 = x_71;
x_12 = x_50;
goto block_19;
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_box(0);
x_91 = lean_array_uset(x_66, x_77, x_90);
x_92 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_45, x_48, x_78);
x_93 = lean_array_uset(x_91, x_77, x_92);
lean_ctor_set(x_50, 1, x_93);
x_9 = x_52;
x_10 = x_72;
x_11 = x_71;
x_12 = x_50;
goto block_19;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; size_t x_99; size_t x_100; size_t x_101; lean_object* x_102; uint8_t x_103; 
lean_dec(x_50);
x_94 = lean_array_uget(x_54, x_64);
lean_dec(x_54);
x_95 = lean_box(0);
x_96 = lean_ctor_get(x_49, 0);
lean_inc(x_96);
lean_dec(x_49);
x_97 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_26, x_45, x_94);
lean_dec(x_94);
lean_ctor_set_tag(x_48, 1);
lean_ctor_set(x_48, 1, x_97);
lean_ctor_set(x_48, 0, x_1);
x_98 = lean_array_get_size(x_66);
x_99 = lean_usize_of_nat(x_98);
lean_dec(x_98);
x_100 = lean_usize_sub(x_99, x_41);
x_101 = lean_usize_land(x_61, x_100);
x_102 = lean_array_uget(x_66, x_101);
x_103 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_45, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_104 = lean_nat_add(x_65, x_40);
lean_dec(x_65);
x_105 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_105, 0, x_45);
lean_ctor_set(x_105, 1, x_48);
lean_ctor_set(x_105, 2, x_102);
x_106 = lean_array_uset(x_66, x_101, x_105);
x_107 = lean_unsigned_to_nat(2u);
x_108 = lean_nat_shiftl(x_104, x_107);
x_109 = lean_unsigned_to_nat(3u);
x_110 = lean_nat_div(x_108, x_109);
lean_dec(x_108);
x_111 = lean_array_get_size(x_106);
x_112 = lean_nat_dec_le(x_110, x_111);
lean_dec(x_111);
lean_dec(x_110);
if (x_112 == 0)
{
lean_object* x_113; lean_object* x_114; 
x_113 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_106);
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_104);
lean_ctor_set(x_114, 1, x_113);
x_9 = x_52;
x_10 = x_96;
x_11 = x_95;
x_12 = x_114;
goto block_19;
}
else
{
lean_object* x_115; 
x_115 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_115, 0, x_104);
lean_ctor_set(x_115, 1, x_106);
x_9 = x_52;
x_10 = x_96;
x_11 = x_95;
x_12 = x_115;
goto block_19;
}
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; 
x_116 = lean_box(0);
x_117 = lean_array_uset(x_66, x_101, x_116);
x_118 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_45, x_48, x_102);
x_119 = lean_array_uset(x_117, x_101, x_118);
x_120 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_120, 0, x_65);
lean_ctor_set(x_120, 1, x_119);
x_9 = x_52;
x_10 = x_96;
x_11 = x_95;
x_12 = x_120;
goto block_19;
}
}
}
else
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; uint64_t x_124; uint64_t x_125; uint64_t x_126; uint64_t x_127; uint64_t x_128; size_t x_129; size_t x_130; size_t x_131; size_t x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; size_t x_142; size_t x_143; size_t x_144; lean_object* x_145; uint8_t x_146; 
x_121 = lean_ctor_get(x_48, 1);
lean_inc(x_121);
lean_dec(x_48);
x_122 = lean_ctor_get(x_50, 1);
lean_inc(x_122);
x_123 = lean_array_get_size(x_122);
x_124 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_45);
x_125 = lean_uint64_shift_right(x_124, x_31);
x_126 = lean_uint64_xor(x_124, x_125);
x_127 = lean_uint64_shift_right(x_126, x_35);
x_128 = lean_uint64_xor(x_126, x_127);
x_129 = lean_uint64_to_usize(x_128);
x_130 = lean_usize_of_nat(x_123);
lean_dec(x_123);
x_131 = lean_usize_sub(x_130, x_41);
x_132 = lean_usize_land(x_129, x_131);
x_133 = lean_ctor_get(x_50, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_50, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_135 = x_50;
} else {
 lean_dec_ref(x_50);
 x_135 = lean_box(0);
}
x_136 = lean_array_uget(x_122, x_132);
lean_dec(x_122);
x_137 = lean_box(0);
x_138 = lean_ctor_get(x_49, 0);
lean_inc(x_138);
lean_dec(x_49);
x_139 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_26, x_45, x_136);
lean_dec(x_136);
x_140 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_139);
x_141 = lean_array_get_size(x_134);
x_142 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_143 = lean_usize_sub(x_142, x_41);
x_144 = lean_usize_land(x_129, x_143);
x_145 = lean_array_uget(x_134, x_144);
x_146 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__0___redArg(x_45, x_145);
if (x_146 == 0)
{
lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; uint8_t x_155; 
x_147 = lean_nat_add(x_133, x_40);
lean_dec(x_133);
x_148 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_148, 0, x_45);
lean_ctor_set(x_148, 1, x_140);
lean_ctor_set(x_148, 2, x_145);
x_149 = lean_array_uset(x_134, x_144, x_148);
x_150 = lean_unsigned_to_nat(2u);
x_151 = lean_nat_shiftl(x_147, x_150);
x_152 = lean_unsigned_to_nat(3u);
x_153 = lean_nat_div(x_151, x_152);
lean_dec(x_151);
x_154 = lean_array_get_size(x_149);
x_155 = lean_nat_dec_le(x_153, x_154);
lean_dec(x_154);
lean_dec(x_153);
if (x_155 == 0)
{
lean_object* x_156; lean_object* x_157; 
x_156 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__1___redArg(x_149);
if (lean_is_scalar(x_135)) {
 x_157 = lean_alloc_ctor(0, 2, 0);
} else {
 x_157 = x_135;
}
lean_ctor_set(x_157, 0, x_147);
lean_ctor_set(x_157, 1, x_156);
x_9 = x_121;
x_10 = x_138;
x_11 = x_137;
x_12 = x_157;
goto block_19;
}
else
{
lean_object* x_158; 
if (lean_is_scalar(x_135)) {
 x_158 = lean_alloc_ctor(0, 2, 0);
} else {
 x_158 = x_135;
}
lean_ctor_set(x_158, 0, x_147);
lean_ctor_set(x_158, 1, x_149);
x_9 = x_121;
x_10 = x_138;
x_11 = x_137;
x_12 = x_158;
goto block_19;
}
}
else
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_159 = lean_box(0);
x_160 = lean_array_uset(x_134, x_144, x_159);
x_161 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_FloatLetIn_initialNewArms_spec__4___redArg(x_45, x_140, x_145);
x_162 = lean_array_uset(x_160, x_144, x_161);
if (lean_is_scalar(x_135)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_135;
}
lean_ctor_set(x_163, 0, x_133);
lean_ctor_set(x_163, 1, x_162);
x_9 = x_121;
x_10 = x_138;
x_11 = x_137;
x_12 = x_163;
goto block_19;
}
}
}
else
{
lean_dec(x_45);
lean_dec(x_26);
lean_dec(x_2);
lean_dec(x_1);
return x_46;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_FloatLetIn_float___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_2);
lean_ctor_set(x_10, 1, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; size_t x_31; size_t x_32; lean_object* x_33; size_t x_34; size_t x_35; size_t x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
lean_dec(x_2);
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_st_ref_get(x_3, x_9);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
lean_dec(x_14);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision;
x_19 = lean_box(0);
x_20 = l_Lean_Compiler_LCNF_CodeDecl_fvarId(x_11);
x_21 = lean_array_get_size(x_17);
x_22 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_20);
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
x_37 = lean_array_uget(x_17, x_36);
lean_dec(x_17);
x_38 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_float_spec__0___redArg(x_18, x_20, x_37);
lean_dec(x_37);
lean_dec(x_20);
x_39 = lean_box(3);
x_40 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; uint8_t x_42; 
x_41 = lean_box(2);
x_42 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_beqDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_63_(x_38, x_41);
lean_dec(x_38);
if (x_42 == 0)
{
lean_object* x_43; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_43 = l_Lean_Compiler_LCNF_FloatLetIn_float(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_ctor_get(x_43, 1);
lean_inc(x_44);
lean_dec(x_43);
x_1 = x_12;
x_2 = x_19;
x_9 = x_44;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_43;
}
}
else
{
lean_object* x_46; 
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_46 = l_Lean_Compiler_LCNF_FloatLetIn_dontFloat(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_16);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_1 = x_12;
x_2 = x_19;
x_9 = x_47;
goto _start;
}
else
{
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_46;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_38);
x_49 = l_Lean_Compiler_LCNF_eraseCodeDecl___redArg(x_11, x_6, x_16);
lean_dec(x_11);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_1 = x_12;
x_2 = x_19;
x_9 = x_50;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_box(0);
lean_inc(x_2);
x_9 = l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___redArg(x_2, x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_ctor_get(x_9, 0);
lean_dec(x_11);
lean_ctor_set(x_9, 0, x_8);
return x_9;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_12);
return x_13;
}
}
else
{
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_1, x_5, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_box(0);
x_15 = lean_array_uget(x_4, x_3);
x_16 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_15);
x_17 = lean_array_get_size(x_13);
x_18 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_16);
x_19 = lean_unsigned_to_nat(32u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_unsigned_to_nat(16u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_usize_of_nat(x_29);
x_31 = lean_usize_sub(x_28, x_30);
x_32 = lean_mk_string_unchecked("Compiler", 8, 8);
x_33 = lean_mk_string_unchecked("floatLetIn", 10, 10);
x_34 = l_Lean_Name_mkStr2(x_32, x_33);
lean_inc(x_34);
x_35 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_34, x_8, x_10);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_74; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_array_uset(x_4, x_3, x_14);
x_61 = lean_usize_land(x_27, x_31);
x_62 = l_instInhabitedList(lean_box(0));
x_63 = lean_array_uget(x_13, x_61);
x_64 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_62, x_16, x_63);
lean_dec(x_63);
x_74 = lean_unbox(x_37);
lean_dec(x_37);
if (x_74 == 0)
{
lean_free_object(x_35);
lean_dec(x_34);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = x_6;
x_66 = x_7;
x_67 = x_8;
x_68 = x_9;
x_69 = x_38;
goto block_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_75 = lean_mk_string_unchecked("Size of code that was pushed into arm: ", 39, 39);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161_(x_16, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_78);
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_79);
lean_ctor_set(x_35, 0, x_76);
x_80 = lean_mk_string_unchecked(" ", 1, 1);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_35);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_List_lengthTR(lean_box(0), x_64);
x_84 = l___private_Init_Data_Repr_0__Nat_reprFast(x_83);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Lean_MessageData_ofFormat(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_mk_string_unchecked("", 0, 0);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_34, x_90, x_7, x_8, x_9, x_38);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = x_6;
x_66 = x_7;
x_67 = x_8;
x_68 = x_9;
x_69 = x_92;
goto block_73;
}
block_60:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Lean_Compiler_LCNF_attachCodeDecls(x_43, x_46);
lean_dec(x_43);
x_48 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_48, x_42, x_40, x_41, x_45, x_44);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_15, x_50);
x_53 = lean_usize_add(x_3, x_30);
x_54 = lean_array_uset(x_39, x_3, x_52);
x_3 = x_53;
x_4 = x_54;
x_10 = x_51;
goto _start;
}
else
{
uint8_t x_56; 
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_73:
{
lean_object* x_70; 
x_70 = lean_array_mk(x_64);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_15, 2);
lean_inc(x_71);
x_40 = x_66;
x_41 = x_67;
x_42 = x_65;
x_43 = x_70;
x_44 = x_69;
x_45 = x_68;
x_46 = x_71;
goto block_60;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_15, 0);
lean_inc(x_72);
x_40 = x_66;
x_41 = x_67;
x_42 = x_65;
x_43 = x_70;
x_44 = x_69;
x_45 = x_68;
x_46 = x_72;
goto block_60;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_130; 
x_93 = lean_ctor_get(x_35, 0);
x_94 = lean_ctor_get(x_35, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_35);
x_95 = lean_array_uset(x_4, x_3, x_14);
x_117 = lean_usize_land(x_27, x_31);
x_118 = l_instInhabitedList(lean_box(0));
x_119 = lean_array_uget(x_13, x_117);
x_120 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_118, x_16, x_119);
lean_dec(x_119);
x_130 = lean_unbox(x_93);
lean_dec(x_93);
if (x_130 == 0)
{
lean_dec(x_34);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_94;
goto block_129;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_131 = lean_mk_string_unchecked("Size of code that was pushed into arm: ", 39, 39);
x_132 = l_Lean_stringToMessageData(x_131);
lean_dec(x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161_(x_16, x_133);
x_135 = l_Lean_MessageData_ofFormat(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked(" ", 1, 1);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_List_lengthTR(lean_box(0), x_120);
x_141 = l___private_Init_Data_Repr_0__Nat_reprFast(x_140);
x_142 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lean_MessageData_ofFormat(x_142);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_139);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("", 0, 0);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_34, x_147, x_7, x_8, x_9, x_94);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_149;
goto block_129;
}
block_116:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = l_Lean_Compiler_LCNF_attachCodeDecls(x_99, x_102);
lean_dec(x_99);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_104, 0, x_103);
x_105 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_104, x_98, x_96, x_97, x_101, x_100);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_15, x_106);
x_109 = lean_usize_add(x_3, x_30);
x_110 = lean_array_uset(x_95, x_3, x_108);
x_3 = x_109;
x_4 = x_110;
x_10 = x_107;
goto _start;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_95);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_114 = x_105;
} else {
 lean_dec_ref(x_105);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
block_129:
{
lean_object* x_126; 
x_126 = lean_array_mk(x_120);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_15, 2);
lean_inc(x_127);
x_96 = x_122;
x_97 = x_123;
x_98 = x_121;
x_99 = x_126;
x_100 = x_125;
x_101 = x_124;
x_102 = x_127;
goto block_116;
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_15, 0);
lean_inc(x_128);
x_96 = x_122;
x_97 = x_123;
x_98 = x_121;
x_99 = x_126;
x_100 = x_125;
x_101 = x_124;
x_102 = x_128;
goto block_116;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_lt(x_3, x_2);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint64_t x_18; lean_object* x_19; uint64_t x_20; uint64_t x_21; uint64_t x_22; lean_object* x_23; uint64_t x_24; uint64_t x_25; uint64_t x_26; size_t x_27; size_t x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; uint8_t x_36; 
x_13 = lean_ctor_get(x_1, 1);
x_14 = lean_box(0);
x_15 = lean_array_uget(x_4, x_3);
x_16 = l_Lean_Compiler_LCNF_FloatLetIn_Decision_ofAlt(x_15);
x_17 = lean_array_get_size(x_13);
x_18 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_16);
x_19 = lean_unsigned_to_nat(32u);
x_20 = lean_uint64_of_nat(x_19);
x_21 = lean_uint64_shift_right(x_18, x_20);
x_22 = lean_uint64_xor(x_18, x_21);
x_23 = lean_unsigned_to_nat(16u);
x_24 = lean_uint64_of_nat(x_23);
x_25 = lean_uint64_shift_right(x_22, x_24);
x_26 = lean_uint64_xor(x_22, x_25);
x_27 = lean_uint64_to_usize(x_26);
x_28 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_29 = lean_unsigned_to_nat(1u);
x_30 = lean_usize_of_nat(x_29);
x_31 = lean_usize_sub(x_28, x_30);
x_32 = lean_mk_string_unchecked("Compiler", 8, 8);
x_33 = lean_mk_string_unchecked("floatLetIn", 10, 10);
x_34 = l_Lean_Name_mkStr2(x_32, x_33);
lean_inc(x_34);
x_35 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_34, x_8, x_10);
x_36 = !lean_is_exclusive(x_35);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; size_t x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; uint8_t x_74; 
x_37 = lean_ctor_get(x_35, 0);
x_38 = lean_ctor_get(x_35, 1);
x_39 = lean_array_uset(x_4, x_3, x_14);
x_61 = lean_usize_land(x_27, x_31);
x_62 = l_instInhabitedList(lean_box(0));
x_63 = lean_array_uget(x_13, x_61);
x_64 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_62, x_16, x_63);
lean_dec(x_63);
x_74 = lean_unbox(x_37);
lean_dec(x_37);
if (x_74 == 0)
{
lean_free_object(x_35);
lean_dec(x_34);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = x_6;
x_66 = x_7;
x_67 = x_8;
x_68 = x_9;
x_69 = x_38;
goto block_73;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; 
x_75 = lean_mk_string_unchecked("Size of code that was pushed into arm: ", 39, 39);
x_76 = l_Lean_stringToMessageData(x_75);
lean_dec(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161_(x_16, x_77);
x_79 = l_Lean_MessageData_ofFormat(x_78);
lean_ctor_set_tag(x_35, 7);
lean_ctor_set(x_35, 1, x_79);
lean_ctor_set(x_35, 0, x_76);
x_80 = lean_mk_string_unchecked(" ", 1, 1);
x_81 = l_Lean_stringToMessageData(x_80);
lean_dec(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_35);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_List_lengthTR(lean_box(0), x_64);
x_84 = l___private_Init_Data_Repr_0__Nat_reprFast(x_83);
x_85 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_85, 0, x_84);
x_86 = l_Lean_MessageData_ofFormat(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_82);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_mk_string_unchecked("", 0, 0);
x_89 = l_Lean_stringToMessageData(x_88);
lean_dec(x_88);
x_90 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_90, 0, x_87);
lean_ctor_set(x_90, 1, x_89);
x_91 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_34, x_90, x_7, x_8, x_9, x_38);
x_92 = lean_ctor_get(x_91, 1);
lean_inc(x_92);
lean_dec(x_91);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_65 = x_6;
x_66 = x_7;
x_67 = x_8;
x_68 = x_9;
x_69 = x_92;
goto block_73;
}
block_60:
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = l_Lean_Compiler_LCNF_attachCodeDecls(x_44, x_46);
lean_dec(x_44);
x_48 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_48, x_41, x_40, x_45, x_43, x_42);
if (lean_obj_tag(x_49) == 0)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
x_52 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_15, x_50);
x_53 = lean_usize_add(x_3, x_30);
x_54 = lean_array_uset(x_39, x_3, x_52);
x_55 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(x_1, x_2, x_53, x_54, x_5, x_6, x_7, x_8, x_9, x_51);
return x_55;
}
else
{
uint8_t x_56; 
lean_dec(x_39);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_56 = !lean_is_exclusive(x_49);
if (x_56 == 0)
{
return x_49;
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; 
x_57 = lean_ctor_get(x_49, 0);
x_58 = lean_ctor_get(x_49, 1);
lean_inc(x_58);
lean_inc(x_57);
lean_dec(x_49);
x_59 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_59, 0, x_57);
lean_ctor_set(x_59, 1, x_58);
return x_59;
}
}
}
block_73:
{
lean_object* x_70; 
x_70 = lean_array_mk(x_64);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_71; 
x_71 = lean_ctor_get(x_15, 2);
lean_inc(x_71);
x_40 = x_66;
x_41 = x_65;
x_42 = x_69;
x_43 = x_68;
x_44 = x_70;
x_45 = x_67;
x_46 = x_71;
goto block_60;
}
else
{
lean_object* x_72; 
x_72 = lean_ctor_get(x_15, 0);
lean_inc(x_72);
x_40 = x_66;
x_41 = x_65;
x_42 = x_69;
x_43 = x_68;
x_44 = x_70;
x_45 = x_67;
x_46 = x_72;
goto block_60;
}
}
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; size_t x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_130; 
x_93 = lean_ctor_get(x_35, 0);
x_94 = lean_ctor_get(x_35, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_35);
x_95 = lean_array_uset(x_4, x_3, x_14);
x_117 = lean_usize_land(x_27, x_31);
x_118 = l_instInhabitedList(lean_box(0));
x_119 = lean_array_uget(x_13, x_117);
x_120 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_118, x_16, x_119);
lean_dec(x_119);
x_130 = lean_unbox(x_93);
lean_dec(x_93);
if (x_130 == 0)
{
lean_dec(x_34);
lean_dec(x_16);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_94;
goto block_129;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_131 = lean_mk_string_unchecked("Size of code that was pushed into arm: ", 39, 39);
x_132 = l_Lean_stringToMessageData(x_131);
lean_dec(x_131);
x_133 = lean_unsigned_to_nat(0u);
x_134 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_reprDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_161_(x_16, x_133);
x_135 = l_Lean_MessageData_ofFormat(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_132);
lean_ctor_set(x_136, 1, x_135);
x_137 = lean_mk_string_unchecked(" ", 1, 1);
x_138 = l_Lean_stringToMessageData(x_137);
lean_dec(x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = l_List_lengthTR(lean_box(0), x_120);
x_141 = l___private_Init_Data_Repr_0__Nat_reprFast(x_140);
x_142 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_142, 0, x_141);
x_143 = l_Lean_MessageData_ofFormat(x_142);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_139);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("", 0, 0);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_34, x_147, x_7, x_8, x_9, x_94);
x_149 = lean_ctor_get(x_148, 1);
lean_inc(x_149);
lean_dec(x_148);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_121 = x_6;
x_122 = x_7;
x_123 = x_8;
x_124 = x_9;
x_125 = x_149;
goto block_129;
}
block_116:
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_103 = l_Lean_Compiler_LCNF_attachCodeDecls(x_100, x_102);
lean_dec(x_100);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_104, 0, x_103);
x_105 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_104, x_97, x_96, x_101, x_99, x_98);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; size_t x_109; lean_object* x_110; lean_object* x_111; 
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_15, x_106);
x_109 = lean_usize_add(x_3, x_30);
x_110 = lean_array_uset(x_95, x_3, x_108);
x_111 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(x_1, x_2, x_109, x_110, x_5, x_6, x_7, x_8, x_9, x_107);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_95);
lean_dec(x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_112 = lean_ctor_get(x_105, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_105, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_114 = x_105;
} else {
 lean_dec_ref(x_105);
 x_114 = lean_box(0);
}
if (lean_is_scalar(x_114)) {
 x_115 = lean_alloc_ctor(1, 2, 0);
} else {
 x_115 = x_114;
}
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_113);
return x_115;
}
}
block_129:
{
lean_object* x_126; 
x_126 = lean_array_mk(x_120);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_15, 2);
lean_inc(x_127);
x_96 = x_122;
x_97 = x_121;
x_98 = x_125;
x_99 = x_124;
x_100 = x_126;
x_101 = x_123;
x_102 = x_127;
goto block_116;
}
else
{
lean_object* x_128; 
x_128 = lean_ctor_get(x_15, 0);
lean_inc(x_128);
x_96 = x_122;
x_97 = x_121;
x_98 = x_125;
x_99 = x_124;
x_100 = x_126;
x_101 = x_123;
x_102 = x_128;
goto block_116;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 1);
lean_inc(x_9);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_11, 0, x_9);
x_12 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_10, x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = lean_ctor_get(x_13, 4);
lean_inc(x_15);
x_16 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_16, 0, x_15);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_16, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ctor_get(x_13, 3);
lean_inc(x_20);
x_21 = lean_ctor_get(x_13, 2);
lean_inc(x_21);
x_22 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_13, x_20, x_21, x_18, x_4, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
lean_dec(x_22);
x_25 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_25, 0, x_23);
x_26 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_26, 0, x_14);
x_27 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_25, x_26, x_2, x_3, x_4, x_5, x_6, x_24);
return x_27;
}
else
{
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_17;
}
}
case 2:
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_28 = lean_ctor_get(x_1, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_1, 1);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_ctor_get(x_28, 4);
lean_inc(x_30);
x_31 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_31, 0, x_30);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_32 = l_Lean_Compiler_LCNF_FloatLetIn_withNewScope___redArg(x_31, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
x_35 = lean_ctor_get(x_28, 3);
lean_inc(x_35);
x_36 = lean_ctor_get(x_28, 2);
lean_inc(x_36);
x_37 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_28, x_35, x_36, x_33, x_4, x_34);
x_38 = lean_ctor_get(x_37, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_37, 1);
lean_inc(x_39);
lean_dec(x_37);
x_40 = lean_alloc_ctor(2, 1, 0);
lean_ctor_set(x_40, 0, x_38);
x_41 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 1);
lean_closure_set(x_41, 0, x_29);
x_42 = l_Lean_Compiler_LCNF_FloatLetIn_withNewCandidate___redArg(x_40, x_41, x_2, x_3, x_4, x_5, x_6, x_39);
return x_42;
}
else
{
lean_dec(x_29);
lean_dec(x_28);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_32;
}
}
case 4:
{
lean_object* x_43; lean_object* x_44; 
x_43 = lean_ctor_get(x_1, 0);
lean_inc(x_43);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_43);
x_44 = l_Lean_Compiler_LCNF_FloatLetIn_initialDecisions(x_43, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_44) == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_44, 1);
lean_inc(x_46);
lean_dec(x_44);
x_47 = l_Lean_Compiler_LCNF_FloatLetIn_initialNewArms(x_43);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_st_mk_ref(x_48, x_46);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_ctor_get(x_49, 1);
lean_inc(x_51);
lean_dec(x_49);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_50);
x_52 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_goCases(x_50, x_2, x_3, x_4, x_5, x_6, x_51);
if (lean_obj_tag(x_52) == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint64_t x_61; lean_object* x_62; uint64_t x_63; uint64_t x_64; uint64_t x_65; lean_object* x_66; uint64_t x_67; uint64_t x_68; uint64_t x_69; size_t x_70; size_t x_71; lean_object* x_72; size_t x_73; size_t x_74; lean_object* x_75; size_t x_76; lean_object* x_77; size_t x_78; lean_object* x_79; 
x_53 = lean_ctor_get(x_52, 1);
lean_inc(x_53);
lean_dec(x_52);
x_54 = lean_st_ref_get(x_50, x_53);
lean_dec(x_50);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_58 = lean_ctor_get(x_56, 1);
lean_inc(x_58);
x_59 = lean_box(2);
x_60 = lean_array_get_size(x_58);
x_61 = l___private_Lean_Compiler_LCNF_FloatLetIn_0__Lean_Compiler_LCNF_FloatLetIn_hashDecision____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_16_(x_59);
x_62 = lean_unsigned_to_nat(32u);
x_63 = lean_uint64_of_nat(x_62);
x_64 = lean_uint64_shift_right(x_61, x_63);
x_65 = lean_uint64_xor(x_61, x_64);
x_66 = lean_unsigned_to_nat(16u);
x_67 = lean_uint64_of_nat(x_66);
x_68 = lean_uint64_shift_right(x_65, x_67);
x_69 = lean_uint64_xor(x_65, x_68);
x_70 = lean_uint64_to_usize(x_69);
x_71 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_72 = lean_unsigned_to_nat(1u);
x_73 = lean_usize_of_nat(x_72);
x_74 = lean_usize_sub(x_71, x_73);
x_75 = lean_ctor_get(x_43, 3);
lean_inc(x_75);
x_76 = lean_array_size(x_75);
x_77 = lean_unsigned_to_nat(0u);
x_78 = lean_usize_of_nat(x_77);
lean_inc(x_75);
x_79 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2(x_56, x_76, x_78, x_75, x_2, x_3, x_4, x_5, x_6, x_57);
lean_dec(x_2);
lean_dec(x_56);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; size_t x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_92; lean_object* x_93; uint8_t x_98; size_t x_101; size_t x_102; uint8_t x_103; 
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
x_83 = lean_usize_land(x_70, x_74);
x_84 = l_instInhabitedList(lean_box(0));
x_85 = lean_array_uget(x_58, x_83);
lean_dec(x_58);
x_86 = l_Std_DHashMap_Internal_AssocList_get_x21___at___Lean_Compiler_LCNF_FloatLetIn_dontFloat_spec__0___redArg(x_84, x_59, x_85);
lean_dec(x_85);
x_92 = lean_ctor_get(x_43, 1);
lean_inc(x_92);
x_93 = lean_ctor_get(x_43, 2);
lean_inc(x_93);
x_101 = lean_ptr_addr(x_75);
lean_dec(x_75);
x_102 = lean_ptr_addr(x_80);
x_103 = lean_usize_dec_eq(x_101, x_102);
if (x_103 == 0)
{
x_98 = x_103;
goto block_100;
}
else
{
size_t x_104; uint8_t x_105; 
x_104 = lean_ptr_addr(x_92);
x_105 = lean_usize_dec_eq(x_104, x_104);
x_98 = x_105;
goto block_100;
}
block_91:
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_array_mk(x_86);
x_89 = l_Lean_Compiler_LCNF_attachCodeDecls(x_88, x_87);
lean_dec(x_88);
if (lean_is_scalar(x_82)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_82;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_81);
return x_90;
}
block_97:
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
x_94 = lean_ctor_get(x_43, 0);
lean_inc(x_94);
lean_dec(x_43);
x_95 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_92);
lean_ctor_set(x_95, 2, x_93);
lean_ctor_set(x_95, 3, x_80);
x_96 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_87 = x_96;
goto block_91;
}
block_100:
{
if (x_98 == 0)
{
lean_dec(x_1);
goto block_97;
}
else
{
uint8_t x_99; 
x_99 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_93, x_93);
if (x_99 == 0)
{
lean_dec(x_1);
goto block_97;
}
else
{
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_80);
lean_dec(x_43);
x_87 = x_1;
goto block_91;
}
}
}
}
else
{
uint8_t x_106; 
lean_dec(x_75);
lean_dec(x_58);
lean_dec(x_43);
lean_dec(x_1);
x_106 = !lean_is_exclusive(x_79);
if (x_106 == 0)
{
return x_79;
}
else
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_107 = lean_ctor_get(x_79, 0);
x_108 = lean_ctor_get(x_79, 1);
lean_inc(x_108);
lean_inc(x_107);
lean_dec(x_79);
x_109 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
return x_109;
}
}
}
else
{
uint8_t x_110; 
lean_dec(x_50);
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_110 = !lean_is_exclusive(x_52);
if (x_110 == 0)
{
return x_52;
}
else
{
lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_111 = lean_ctor_get(x_52, 0);
x_112 = lean_ctor_get(x_52, 1);
lean_inc(x_112);
lean_inc(x_111);
lean_dec(x_52);
x_113 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_112);
return x_113;
}
}
}
else
{
uint8_t x_114; 
lean_dec(x_43);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_114 = !lean_is_exclusive(x_44);
if (x_114 == 0)
{
return x_44;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_44, 0);
x_116 = lean_ctor_get(x_44, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_44);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
default: 
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_118 = lean_array_mk(x_2);
x_119 = l_Array_reverse(lean_box(0), x_118);
x_120 = l_Lean_Compiler_LCNF_attachCodeDecls(x_119, x_1);
lean_dec(x_119);
x_121 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_121, 0, x_120);
lean_ctor_set(x_121, 1, x_7);
return x_121;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_addTrace___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
x_11 = lean_apply_7(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_ctor_set(x_2, 0, x_13);
lean_ctor_set(x_11, 0, x_2);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_ctor_get(x_11, 0);
x_15 = lean_ctor_get(x_11, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_11);
lean_ctor_set(x_2, 0, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_2);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
else
{
uint8_t x_17; 
lean_free_object(x_2);
x_17 = !lean_is_exclusive(x_11);
if (x_17 == 0)
{
return x_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_11, 0);
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_inc(x_18);
lean_dec(x_11);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_2, 0);
lean_inc(x_21);
lean_dec(x_2);
x_22 = lean_apply_7(x_1, x_21, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_22, 1);
lean_inc(x_24);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_25 = x_22;
} else {
 lean_dec_ref(x_22);
 x_25 = lean_box(0);
}
x_26 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_26, 0, x_23);
if (lean_is_scalar(x_25)) {
 x_27 = lean_alloc_ctor(0, 2, 0);
} else {
 x_27 = x_25;
}
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_28 = lean_ctor_get(x_22, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_22, 1);
lean_inc(x_29);
if (lean_is_exclusive(x_22)) {
 lean_ctor_release(x_22, 0);
 lean_ctor_release(x_22, 1);
 x_30 = x_22;
} else {
 lean_dec_ref(x_22);
 x_30 = lean_box(0);
}
if (lean_is_scalar(x_30)) {
 x_31 = lean_alloc_ctor(1, 2, 0);
} else {
 x_31 = x_30;
}
lean_ctor_set(x_31, 0, x_28);
lean_ctor_set(x_31, 1, x_29);
return x_31;
}
}
}
else
{
lean_object* x_32; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_2);
lean_ctor_set(x_32, 1, x_8);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn_go), 7, 0);
x_8 = lean_ctor_get(x_1, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_FloatLetIn_floatLetIn_spec__0(x_7, x_8, x_9, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_1, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_1, 3);
lean_inc(x_16);
x_17 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_19 = lean_ctor_get(x_1, 5);
lean_inc(x_19);
lean_dec(x_1);
x_20 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_20, 0, x_13);
lean_ctor_set(x_20, 1, x_14);
lean_ctor_set(x_20, 2, x_15);
lean_ctor_set(x_20, 3, x_16);
lean_ctor_set(x_20, 4, x_12);
lean_ctor_set(x_20, 5, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*6, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*6 + 1, x_18);
lean_ctor_set(x_10, 0, x_20);
return x_10;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_inc(x_21);
lean_dec(x_10);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
x_25 = lean_ctor_get(x_1, 2);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 3);
lean_inc(x_26);
x_27 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_28 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_29 = lean_ctor_get(x_1, 5);
lean_inc(x_29);
lean_dec(x_1);
x_30 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_30, 0, x_23);
lean_ctor_set(x_30, 1, x_24);
lean_ctor_set(x_30, 2, x_25);
lean_ctor_set(x_30, 3, x_26);
lean_ctor_set(x_30, 4, x_21);
lean_ctor_set(x_30, 5, x_29);
lean_ctor_set_uint8(x_30, sizeof(void*)*6, x_27);
lean_ctor_set_uint8(x_30, sizeof(void*)*6 + 1, x_28);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_22);
return x_31;
}
}
else
{
uint8_t x_32; 
lean_dec(x_1);
x_32 = !lean_is_exclusive(x_10);
if (x_32 == 0)
{
return x_10;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_10, 0);
x_34 = lean_ctor_get(x_10, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_10);
x_35 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
return x_35;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_floatLetIn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_FloatLetIn_floatLetIn(x_1, x_2, x_3, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn(uint8_t x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_floatLetIn___lam__0), 6, 0);
x_4 = lean_mk_string_unchecked("floatLetIn", 10, 10);
x_5 = l_Lean_Name_mkStr1(x_4);
x_6 = l_Lean_Compiler_LCNF_Pass_mkPerDeclaration(x_5, x_3, x_1, x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_floatLetIn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_Compiler_LCNF_floatLetIn(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2271_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("floatLetIn", 10, 10);
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
x_17 = l_Lean_Name_str___override(x_16, x_2);
x_18 = l_Lean_Name_str___override(x_17, x_10);
x_19 = lean_mk_string_unchecked("FloatLetIn", 10, 10);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(2271u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_FVarUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PassManager(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Types(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_FloatLetIn(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_FVarUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PassManager(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instHashableDecision);
l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instBEqDecision);
l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instInhabitedDecision);
l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision = _init_l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision();
lean_mark_persistent(l_Lean_Compiler_LCNF_FloatLetIn_instReprDecision);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_FloatLetIn___hyg_2271_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
