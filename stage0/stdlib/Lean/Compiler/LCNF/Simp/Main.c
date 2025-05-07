// Lean compiler output
// Module: Lean.Compiler.LCNF.Simp.Main
// Imports: Lean.Compiler.ImplementedByAttr Lean.Compiler.LCNF.ElimDead Lean.Compiler.LCNF.AlphaEqv Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.Bind Lean.Compiler.LCNF.Simp.FunDeclInfo Lean.Compiler.LCNF.Simp.InlineCandidate Lean.Compiler.LCNF.Simp.InlineProj Lean.Compiler.LCNF.Simp.Used Lean.Compiler.LCNF.Simp.DefaultAlt Lean.Compiler.LCNF.Simp.SimpValue Lean.Compiler.LCNF.Simp.ConstantFold
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
lean_object* l_Lean_Compiler_LCNF_mkAuxLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkReturnErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isUsed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isFun(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_isInstance___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addDefaultAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Compiler_LCNF_findFunDecl_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedCode;
lean_object* l_Lean_Compiler_LCNF_Code_internalize(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_Simp_eraseFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_incVisited(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_getArity(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferAppType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_normFunDeclImp(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkNewParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withInlining_check(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_betaReduce(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(lean_object*);
lean_object* l_Array_ofSubarray___redArg(lean_object*);
lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_hasLocalInst(lean_object*);
lean_object* l_Lean_Compiler_LCNF_CompilerM_codeBind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_eraseCode___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_betaReduce_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_replaceExprFVars___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_simpValue_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getDecl_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
extern lean_object* l_Lean_Compiler_LCNF_instInhabitedParam;
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_Code_isReturnOf(lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_mkAuxParam(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkAuxFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object*);
lean_object* l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Simp_attachCodeDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(lean_object* x_1) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_2; 
x_2 = lean_ctor_get(x_1, 1);
lean_inc(x_2);
lean_dec(x_1);
x_1 = x_2;
goto _start;
}
case 1:
{
lean_object* x_4; 
x_4 = lean_ctor_get(x_1, 1);
lean_inc(x_4);
lean_dec(x_1);
x_1 = x_4;
goto _start;
}
case 4:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_ctor_get(x_6, 3);
lean_inc(x_7);
lean_dec(x_6);
x_8 = lean_array_get_size(x_7);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_dec_eq(x_8, x_9);
lean_dec(x_8);
if (x_10 == 0)
{
lean_dec(x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_11 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_12 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_11);
x_13 = lean_unsigned_to_nat(0u);
x_14 = lean_array_get(x_12, x_7, x_13);
lean_dec(x_7);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 2);
lean_inc(x_15);
lean_dec(x_14);
x_1 = x_15;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_ctor_get(x_14, 0);
lean_inc(x_17);
lean_dec(x_14);
x_1 = x_17;
goto _start;
}
}
}
case 5:
{
lean_object* x_19; uint8_t x_20; 
lean_dec(x_1);
x_19 = lean_box(1);
x_20 = lean_unbox(x_19);
return x_20;
}
default: 
{
lean_object* x_21; uint8_t x_22; 
lean_dec(x_1);
x_21 = lean_box(0);
x_22 = lean_unbox(x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(lean_object* x_1) {
_start:
{
uint8_t x_2; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_lt(x_3, x_2);
if (x_10 == 0)
{
lean_object* x_11; 
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_4);
lean_ctor_set(x_11, 1, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_12 = lean_ctor_get(x_1, 0);
x_13 = lean_array_uget(x_12, x_3);
x_14 = lean_ctor_get(x_4, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 2);
lean_inc(x_15);
x_16 = l_Lean_Compiler_LCNF_replaceExprFVars___redArg(x_15, x_14, x_10, x_9);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_box(0);
x_20 = lean_unbox(x_19);
x_21 = l_Lean_Compiler_LCNF_mkAuxParam(x_17, x_20, x_5, x_6, x_7, x_8, x_18);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
x_23 = lean_ctor_get(x_21, 1);
lean_inc(x_23);
if (lean_is_exclusive(x_21)) {
 lean_ctor_release(x_21, 0);
 lean_ctor_release(x_21, 1);
 x_24 = x_21;
} else {
 lean_dec_ref(x_21);
 x_24 = lean_box(0);
}
x_25 = lean_ctor_get(x_4, 0);
lean_inc(x_25);
lean_dec(x_4);
x_26 = !lean_is_exclusive(x_14);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; uint64_t x_41; lean_object* x_42; uint64_t x_43; uint64_t x_44; uint64_t x_45; lean_object* x_46; uint64_t x_47; uint64_t x_48; uint64_t x_49; size_t x_50; size_t x_51; lean_object* x_52; size_t x_53; size_t x_54; size_t x_55; lean_object* x_56; uint8_t x_57; 
x_27 = lean_ctor_get(x_14, 0);
x_28 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
x_29 = lean_array_push(x_25, x_22);
x_37 = lean_ctor_get(x_22, 0);
lean_inc(x_37);
lean_dec(x_22);
x_38 = lean_ctor_get(x_13, 0);
lean_inc(x_38);
lean_dec(x_13);
x_39 = l_Lean_Expr_fvar___override(x_37);
x_40 = lean_array_get_size(x_28);
x_41 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_38);
x_42 = lean_unsigned_to_nat(32u);
x_43 = lean_uint64_of_nat(x_42);
x_44 = lean_uint64_shift_right(x_41, x_43);
x_45 = lean_uint64_xor(x_41, x_44);
x_46 = lean_unsigned_to_nat(16u);
x_47 = lean_uint64_of_nat(x_46);
x_48 = lean_uint64_shift_right(x_45, x_47);
x_49 = lean_uint64_xor(x_45, x_48);
x_50 = lean_uint64_to_usize(x_49);
x_51 = lean_usize_of_nat(x_40);
lean_dec(x_40);
x_52 = lean_unsigned_to_nat(1u);
x_53 = lean_usize_of_nat(x_52);
x_54 = lean_usize_sub(x_51, x_53);
x_55 = lean_usize_land(x_50, x_54);
x_56 = lean_array_uget(x_28, x_55);
x_57 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_38, x_56);
if (x_57 == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_58 = lean_nat_add(x_27, x_52);
lean_dec(x_27);
x_59 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_59, 0, x_38);
lean_ctor_set(x_59, 1, x_39);
lean_ctor_set(x_59, 2, x_56);
x_60 = lean_array_uset(x_28, x_55, x_59);
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
lean_ctor_set(x_14, 1, x_67);
lean_ctor_set(x_14, 0, x_58);
x_30 = x_14;
goto block_36;
}
else
{
lean_ctor_set(x_14, 1, x_60);
lean_ctor_set(x_14, 0, x_58);
x_30 = x_14;
goto block_36;
}
}
else
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_68 = lean_box(0);
x_69 = lean_array_uset(x_28, x_55, x_68);
x_70 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_38, x_39, x_56);
x_71 = lean_array_uset(x_69, x_55, x_70);
lean_ctor_set(x_14, 1, x_71);
x_30 = x_14;
goto block_36;
}
block_36:
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; 
if (lean_is_scalar(x_24)) {
 x_31 = lean_alloc_ctor(0, 2, 0);
} else {
 x_31 = x_24;
}
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_unsigned_to_nat(1u);
x_33 = lean_usize_of_nat(x_32);
x_34 = lean_usize_add(x_3, x_33);
x_3 = x_34;
x_4 = x_31;
x_9 = x_23;
goto _start;
}
}
else
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; uint64_t x_86; lean_object* x_87; uint64_t x_88; uint64_t x_89; uint64_t x_90; lean_object* x_91; uint64_t x_92; uint64_t x_93; uint64_t x_94; size_t x_95; size_t x_96; lean_object* x_97; size_t x_98; size_t x_99; size_t x_100; lean_object* x_101; uint8_t x_102; 
x_72 = lean_ctor_get(x_14, 0);
x_73 = lean_ctor_get(x_14, 1);
lean_inc(x_73);
lean_inc(x_72);
lean_dec(x_14);
lean_inc(x_22);
x_74 = lean_array_push(x_25, x_22);
x_82 = lean_ctor_get(x_22, 0);
lean_inc(x_82);
lean_dec(x_22);
x_83 = lean_ctor_get(x_13, 0);
lean_inc(x_83);
lean_dec(x_13);
x_84 = l_Lean_Expr_fvar___override(x_82);
x_85 = lean_array_get_size(x_73);
x_86 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_83);
x_87 = lean_unsigned_to_nat(32u);
x_88 = lean_uint64_of_nat(x_87);
x_89 = lean_uint64_shift_right(x_86, x_88);
x_90 = lean_uint64_xor(x_86, x_89);
x_91 = lean_unsigned_to_nat(16u);
x_92 = lean_uint64_of_nat(x_91);
x_93 = lean_uint64_shift_right(x_90, x_92);
x_94 = lean_uint64_xor(x_90, x_93);
x_95 = lean_uint64_to_usize(x_94);
x_96 = lean_usize_of_nat(x_85);
lean_dec(x_85);
x_97 = lean_unsigned_to_nat(1u);
x_98 = lean_usize_of_nat(x_97);
x_99 = lean_usize_sub(x_96, x_98);
x_100 = lean_usize_land(x_95, x_99);
x_101 = lean_array_uget(x_73, x_100);
x_102 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_83, x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_103 = lean_nat_add(x_72, x_97);
lean_dec(x_72);
x_104 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_104, 0, x_83);
lean_ctor_set(x_104, 1, x_84);
lean_ctor_set(x_104, 2, x_101);
x_105 = lean_array_uset(x_73, x_100, x_104);
x_106 = lean_unsigned_to_nat(2u);
x_107 = lean_nat_shiftl(x_103, x_106);
x_108 = lean_unsigned_to_nat(3u);
x_109 = lean_nat_div(x_107, x_108);
lean_dec(x_107);
x_110 = lean_array_get_size(x_105);
x_111 = lean_nat_dec_le(x_109, x_110);
lean_dec(x_110);
lean_dec(x_109);
if (x_111 == 0)
{
lean_object* x_112; lean_object* x_113; 
x_112 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_105);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_103);
lean_ctor_set(x_113, 1, x_112);
x_75 = x_113;
goto block_81;
}
else
{
lean_object* x_114; 
x_114 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_114, 0, x_103);
lean_ctor_set(x_114, 1, x_105);
x_75 = x_114;
goto block_81;
}
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
x_115 = lean_box(0);
x_116 = lean_array_uset(x_73, x_100, x_115);
x_117 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_83, x_84, x_101);
x_118 = lean_array_uset(x_116, x_100, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_72);
lean_ctor_set(x_119, 1, x_118);
x_75 = x_119;
goto block_81;
}
block_81:
{
lean_object* x_76; lean_object* x_77; size_t x_78; size_t x_79; 
if (lean_is_scalar(x_24)) {
 x_76 = lean_alloc_ctor(0, 2, 0);
} else {
 x_76 = x_24;
}
lean_ctor_set(x_76, 0, x_74);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_unsigned_to_nat(1u);
x_78 = lean_usize_of_nat(x_77);
x_79 = lean_usize_add(x_3, x_78);
x_3 = x_79;
x_4 = x_76;
x_9 = x_23;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1, x_2, x_3, x_4, x_8, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
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
x_18 = lean_mk_array(x_16, x_17);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_11);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_1, 3);
lean_inc(x_20);
x_21 = lean_array_get_size(x_20);
lean_inc(x_21);
x_22 = l_Array_toSubarray___redArg(x_20, x_11, x_21);
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_22);
lean_ctor_set(x_24, 1, x_19);
x_25 = lean_array_size(x_23);
x_26 = lean_usize_of_nat(x_11);
x_27 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_betaReduce_spec__0(x_23, x_25, x_26, x_24, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
x_30 = !lean_is_exclusive(x_28);
if (x_30 == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; size_t x_36; lean_object* x_37; size_t x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint8_t x_49; lean_object* x_50; 
x_31 = lean_ctor_get(x_28, 0);
lean_dec(x_31);
x_32 = lean_mk_empty_array_with_capacity(x_11);
x_33 = lean_array_get_size(x_23);
x_34 = l_Array_toSubarray___redArg(x_23, x_21, x_33);
lean_ctor_set(x_28, 0, x_32);
x_35 = lean_ctor_get(x_34, 2);
lean_inc(x_35);
x_36 = lean_usize_of_nat(x_35);
lean_dec(x_35);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_34, x_36, x_38, x_28, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_34);
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_ctor_get(x_40, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 1);
lean_inc(x_43);
lean_dec(x_40);
x_44 = lean_ctor_get(x_1, 1);
lean_inc(x_44);
lean_dec(x_1);
x_45 = l_Lean_Compiler_LCNF_Code_internalize(x_44, x_43, x_5, x_6, x_7, x_8, x_41);
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
x_47 = lean_ctor_get(x_45, 1);
lean_inc(x_47);
lean_dec(x_45);
x_48 = lean_box(0);
x_49 = lean_unbox(x_48);
lean_inc(x_46);
x_50 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_46, x_49, x_3, x_5, x_6, x_7, x_8, x_47);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_51 = lean_ctor_get(x_50, 1);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_mk_string_unchecked("_f", 2, 2);
x_53 = l_Lean_Name_mkStr1(x_52);
x_54 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_42, x_46, x_53, x_5, x_6, x_7, x_8, x_51);
return x_54;
}
else
{
uint8_t x_55; 
lean_dec(x_46);
lean_dec(x_42);
x_55 = !lean_is_exclusive(x_50);
if (x_55 == 0)
{
return x_50;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_50, 0);
x_57 = lean_ctor_get(x_50, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_50);
x_58 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_58, 0, x_56);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; size_t x_65; lean_object* x_66; size_t x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; 
x_59 = lean_ctor_get(x_28, 1);
lean_inc(x_59);
lean_dec(x_28);
x_60 = lean_mk_empty_array_with_capacity(x_11);
x_61 = lean_array_get_size(x_23);
x_62 = l_Array_toSubarray___redArg(x_23, x_21, x_61);
x_63 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_63, 0, x_60);
lean_ctor_set(x_63, 1, x_59);
x_64 = lean_ctor_get(x_62, 2);
lean_inc(x_64);
x_65 = lean_usize_of_nat(x_64);
lean_dec(x_64);
x_66 = lean_ctor_get(x_62, 1);
lean_inc(x_66);
x_67 = lean_usize_of_nat(x_66);
lean_dec(x_66);
x_68 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_62, x_65, x_67, x_63, x_5, x_6, x_7, x_8, x_29);
lean_dec(x_62);
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_68, 1);
lean_inc(x_70);
lean_dec(x_68);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
lean_dec(x_69);
x_73 = lean_ctor_get(x_1, 1);
lean_inc(x_73);
lean_dec(x_1);
x_74 = l_Lean_Compiler_LCNF_Code_internalize(x_73, x_72, x_5, x_6, x_7, x_8, x_70);
x_75 = lean_ctor_get(x_74, 0);
lean_inc(x_75);
x_76 = lean_ctor_get(x_74, 1);
lean_inc(x_76);
lean_dec(x_74);
x_77 = lean_box(0);
x_78 = lean_unbox(x_77);
lean_inc(x_75);
x_79 = l_Lean_Compiler_LCNF_Simp_updateFunDeclInfo___redArg(x_75, x_78, x_3, x_5, x_6, x_7, x_8, x_76);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_mk_string_unchecked("_f", 2, 2);
x_82 = l_Lean_Name_mkStr1(x_81);
x_83 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_71, x_75, x_82, x_5, x_6, x_7, x_8, x_80);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
lean_dec(x_75);
lean_dec(x_71);
x_84 = lean_ctor_get(x_79, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_79, 1);
lean_inc(x_85);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_86 = x_79;
} else {
 lean_dec_ref(x_79);
 x_86 = lean_box(0);
}
if (lean_is_scalar(x_86)) {
 x_87 = lean_alloc_ctor(1, 2, 0);
} else {
 x_87 = x_86;
}
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_85);
return x_87;
}
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_Simp_specializePartialApp_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_specializePartialApp___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Compiler_LCNF_findFunDecl_x3f(x_1, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
if (lean_obj_tag(x_12) == 0)
{
uint8_t x_13; 
lean_dec(x_2);
x_13 = !lean_is_exclusive(x_11);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
lean_ctor_set(x_11, 0, x_15);
return x_11;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_ctor_get(x_11, 1);
lean_inc(x_16);
lean_dec(x_11);
x_17 = lean_box(0);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_16);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_11, 1);
lean_inc(x_19);
lean_dec(x_11);
x_20 = !lean_is_exclusive(x_12);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_21 = lean_ctor_get(x_12, 0);
x_22 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_21, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
uint8_t x_25; 
lean_free_object(x_12);
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
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; lean_object* x_38; 
x_31 = lean_ctor_get(x_22, 1);
lean_inc(x_31);
lean_dec(x_22);
x_32 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_31);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_ctor_get(x_21, 2);
lean_inc(x_34);
x_35 = lean_ctor_get(x_21, 4);
lean_inc(x_35);
lean_dec(x_21);
x_36 = lean_box(0);
x_37 = lean_unbox(x_36);
x_38 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_34, x_35, x_2, x_37, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_33);
lean_dec(x_34);
if (lean_obj_tag(x_38) == 0)
{
uint8_t x_39; 
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; 
x_40 = lean_ctor_get(x_38, 0);
lean_ctor_set(x_12, 0, x_40);
lean_ctor_set(x_38, 0, x_12);
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
lean_ctor_set(x_12, 0, x_41);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_12);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
else
{
uint8_t x_44; 
lean_free_object(x_12);
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
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_48 = lean_ctor_get(x_12, 0);
lean_inc(x_48);
lean_dec(x_12);
x_49 = l_Lean_Compiler_LCNF_Simp_shouldInlineLocal(x_48, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_19);
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
x_51 = lean_unbox(x_50);
lean_dec(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
lean_dec(x_48);
lean_dec(x_2);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_49)) {
 lean_ctor_release(x_49, 0);
 lean_ctor_release(x_49, 1);
 x_53 = x_49;
} else {
 lean_dec_ref(x_49);
 x_53 = lean_box(0);
}
x_54 = lean_box(0);
if (lean_is_scalar(x_53)) {
 x_55 = lean_alloc_ctor(0, 2, 0);
} else {
 x_55 = x_53;
}
lean_ctor_set(x_55, 0, x_54);
lean_ctor_set(x_55, 1, x_52);
return x_55;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; lean_object* x_63; 
x_56 = lean_ctor_get(x_49, 1);
lean_inc(x_56);
lean_dec(x_49);
x_57 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_4, x_56);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_59 = lean_ctor_get(x_48, 2);
lean_inc(x_59);
x_60 = lean_ctor_get(x_48, 4);
lean_inc(x_60);
lean_dec(x_48);
x_61 = lean_box(0);
x_62 = lean_unbox(x_61);
x_63 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_59, x_60, x_2, x_62, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_58);
lean_dec(x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_66 = x_63;
} else {
 lean_dec_ref(x_63);
 x_66 = lean_box(0);
}
x_67 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_67, 0, x_64);
if (lean_is_scalar(x_66)) {
 x_68 = lean_alloc_ctor(0, 2, 0);
} else {
 x_68 = x_66;
}
lean_ctor_set(x_68, 0, x_67);
lean_ctor_set(x_68, 1, x_65);
return x_68;
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_69 = lean_ctor_get(x_63, 0);
lean_inc(x_69);
x_70 = lean_ctor_get(x_63, 1);
lean_inc(x_70);
if (lean_is_exclusive(x_63)) {
 lean_ctor_release(x_63, 0);
 lean_ctor_release(x_63, 1);
 x_71 = x_63;
} else {
 lean_dec_ref(x_63);
 x_71 = lean_box(0);
}
if (lean_is_scalar(x_71)) {
 x_72 = lean_alloc_ctor(1, 2, 0);
} else {
 x_72 = x_71;
}
lean_ctor_set(x_72, 0, x_69);
lean_ctor_set(x_72, 1, x_70);
return x_72;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineJp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = lean_ctor_get_uint8(x_10, 0);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_12 = lean_box(0);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
if (lean_obj_tag(x_14) == 3)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_ctor_get(x_14, 1);
x_18 = lean_ctor_get(x_14, 2);
x_19 = lean_st_ref_get(x_8, x_9);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_21, 0);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_box(0);
x_25 = lean_unbox(x_24);
lean_inc(x_16);
x_26 = l_Lean_Environment_find_x3f(x_23, x_16, x_25);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; 
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_27 = lean_box(0);
lean_ctor_set(x_19, 0, x_27);
return x_19;
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_26);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; uint8_t x_31; 
x_29 = lean_ctor_get(x_26, 0);
x_30 = l_Lean_ConstantInfo_type(x_29);
lean_dec(x_29);
x_31 = l_Lean_Compiler_LCNF_hasLocalInst(x_30);
lean_dec(x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_32 = lean_box(0);
lean_ctor_set(x_19, 0, x_32);
return x_19;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_40; 
lean_free_object(x_19);
x_33 = l_Lean_Meta_isInstance___redArg(x_16, x_8, x_22);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
if (lean_is_exclusive(x_33)) {
 lean_ctor_release(x_33, 0);
 lean_ctor_release(x_33, 1);
 x_36 = x_33;
} else {
 lean_dec_ref(x_33);
 x_36 = lean_box(0);
}
x_40 = lean_unbox(x_34);
lean_dec(x_34);
if (x_40 == 0)
{
if (x_31 == 0)
{
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_39;
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_dec(x_36);
lean_inc(x_16);
x_41 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_16, x_5, x_8, x_35);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
if (lean_obj_tag(x_42) == 0)
{
uint8_t x_43; 
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_43 = !lean_is_exclusive(x_41);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_41, 0);
lean_dec(x_44);
x_45 = lean_box(0);
lean_ctor_set(x_41, 0, x_45);
return x_41;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_41, 1);
lean_inc(x_46);
lean_dec(x_41);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
else
{
uint8_t x_49; 
x_49 = !lean_is_exclusive(x_41);
if (x_49 == 0)
{
lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_50 = lean_ctor_get(x_41, 1);
x_51 = lean_ctor_get(x_41, 0);
lean_dec(x_51);
x_52 = !lean_is_exclusive(x_42);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_42, 0);
x_54 = lean_array_get_size(x_18);
x_55 = l_Lean_Compiler_LCNF_Decl_getArity(x_53);
lean_dec(x_53);
x_56 = lean_nat_dec_lt(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_42);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_57 = lean_box(0);
lean_ctor_set(x_41, 0, x_57);
return x_41;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_free_object(x_41);
x_58 = lean_ctor_get(x_1, 2);
lean_inc(x_58);
x_59 = l_Lean_Compiler_LCNF_mkNewParams(x_58, x_5, x_6, x_7, x_8, x_50);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
lean_object* x_61; lean_object* x_62; size_t x_63; lean_object* x_64; size_t x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
x_63 = lean_array_size(x_61);
x_64 = lean_unsigned_to_nat(0u);
x_65 = lean_usize_of_nat(x_64);
lean_inc(x_61);
x_66 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_63, x_65, x_61);
x_67 = l_Array_append(lean_box(0), x_18, x_66);
lean_dec(x_66);
lean_ctor_set(x_14, 2, x_67);
x_68 = lean_mk_string_unchecked("_x", 2, 2);
x_69 = l_Lean_Name_mkStr1(x_68);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_70 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_14, x_69, x_5, x_6, x_7, x_8, x_62);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = lean_ctor_get(x_71, 0);
lean_inc(x_73);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_73);
lean_ctor_set(x_59, 1, x_26);
lean_ctor_set(x_59, 0, x_71);
x_74 = lean_mk_string_unchecked("_f", 2, 2);
x_75 = l_Lean_Name_mkStr1(x_74);
x_76 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_61, x_59, x_75, x_5, x_6, x_7, x_8, x_72);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_79 = lean_ctor_get(x_1, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_77, 0);
lean_inc(x_80);
x_81 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_79, x_80, x_3, x_6, x_7, x_8, x_78);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; uint8_t x_84; 
x_82 = lean_ctor_get(x_81, 1);
lean_inc(x_82);
lean_dec(x_81);
x_83 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_82);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_84 = !lean_is_exclusive(x_83);
if (x_84 == 0)
{
lean_object* x_85; 
x_85 = lean_ctor_get(x_83, 0);
lean_dec(x_85);
lean_ctor_set(x_42, 0, x_77);
lean_ctor_set(x_83, 0, x_42);
return x_83;
}
else
{
lean_object* x_86; lean_object* x_87; 
x_86 = lean_ctor_get(x_83, 1);
lean_inc(x_86);
lean_dec(x_83);
lean_ctor_set(x_42, 0, x_77);
x_87 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_87, 0, x_42);
lean_ctor_set(x_87, 1, x_86);
return x_87;
}
}
else
{
uint8_t x_88; 
lean_dec(x_77);
lean_free_object(x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_88 = !lean_is_exclusive(x_81);
if (x_88 == 0)
{
return x_81;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_81, 0);
x_90 = lean_ctor_get(x_81, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_81);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
else
{
uint8_t x_92; 
lean_free_object(x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_92 = !lean_is_exclusive(x_76);
if (x_92 == 0)
{
return x_76;
}
else
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_ctor_get(x_76, 0);
x_94 = lean_ctor_get(x_76, 1);
lean_inc(x_94);
lean_inc(x_93);
lean_dec(x_76);
x_95 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
return x_95;
}
}
}
else
{
uint8_t x_96; 
lean_free_object(x_59);
lean_dec(x_61);
lean_free_object(x_42);
lean_free_object(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_96 = !lean_is_exclusive(x_70);
if (x_96 == 0)
{
return x_70;
}
else
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_97 = lean_ctor_get(x_70, 0);
x_98 = lean_ctor_get(x_70, 1);
lean_inc(x_98);
lean_inc(x_97);
lean_dec(x_70);
x_99 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_99, 0, x_97);
lean_ctor_set(x_99, 1, x_98);
return x_99;
}
}
}
else
{
lean_object* x_100; lean_object* x_101; size_t x_102; lean_object* x_103; size_t x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_100 = lean_ctor_get(x_59, 0);
x_101 = lean_ctor_get(x_59, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_59);
x_102 = lean_array_size(x_100);
x_103 = lean_unsigned_to_nat(0u);
x_104 = lean_usize_of_nat(x_103);
lean_inc(x_100);
x_105 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_102, x_104, x_100);
x_106 = l_Array_append(lean_box(0), x_18, x_105);
lean_dec(x_105);
lean_ctor_set(x_14, 2, x_106);
x_107 = lean_mk_string_unchecked("_x", 2, 2);
x_108 = l_Lean_Name_mkStr1(x_107);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_109 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_14, x_108, x_5, x_6, x_7, x_8, x_101);
if (lean_obj_tag(x_109) == 0)
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; 
x_110 = lean_ctor_get(x_109, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_109, 1);
lean_inc(x_111);
lean_dec(x_109);
x_112 = lean_ctor_get(x_110, 0);
lean_inc(x_112);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_112);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_26);
x_114 = lean_mk_string_unchecked("_f", 2, 2);
x_115 = l_Lean_Name_mkStr1(x_114);
x_116 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_100, x_113, x_115, x_5, x_6, x_7, x_8, x_111);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_1, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_117, 0);
lean_inc(x_120);
x_121 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_119, x_120, x_3, x_6, x_7, x_8, x_118);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_121, 1);
lean_inc(x_122);
lean_dec(x_121);
x_123 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_122);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_124 = lean_ctor_get(x_123, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_123)) {
 lean_ctor_release(x_123, 0);
 lean_ctor_release(x_123, 1);
 x_125 = x_123;
} else {
 lean_dec_ref(x_123);
 x_125 = lean_box(0);
}
lean_ctor_set(x_42, 0, x_117);
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(0, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_42);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_dec(x_117);
lean_free_object(x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_127 = lean_ctor_get(x_121, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_121, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_121)) {
 lean_ctor_release(x_121, 0);
 lean_ctor_release(x_121, 1);
 x_129 = x_121;
} else {
 lean_dec_ref(x_121);
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
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
lean_free_object(x_42);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_131 = lean_ctor_get(x_116, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_116, 1);
lean_inc(x_132);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_133 = x_116;
} else {
 lean_dec_ref(x_116);
 x_133 = lean_box(0);
}
if (lean_is_scalar(x_133)) {
 x_134 = lean_alloc_ctor(1, 2, 0);
} else {
 x_134 = x_133;
}
lean_ctor_set(x_134, 0, x_131);
lean_ctor_set(x_134, 1, x_132);
return x_134;
}
}
else
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; 
lean_dec(x_100);
lean_free_object(x_42);
lean_free_object(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_135 = lean_ctor_get(x_109, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_109, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_109)) {
 lean_ctor_release(x_109, 0);
 lean_ctor_release(x_109, 1);
 x_137 = x_109;
} else {
 lean_dec_ref(x_109);
 x_137 = lean_box(0);
}
if (lean_is_scalar(x_137)) {
 x_138 = lean_alloc_ctor(1, 2, 0);
} else {
 x_138 = x_137;
}
lean_ctor_set(x_138, 0, x_135);
lean_ctor_set(x_138, 1, x_136);
return x_138;
}
}
}
}
else
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_139 = lean_ctor_get(x_42, 0);
lean_inc(x_139);
lean_dec(x_42);
x_140 = lean_array_get_size(x_18);
x_141 = l_Lean_Compiler_LCNF_Decl_getArity(x_139);
lean_dec(x_139);
x_142 = lean_nat_dec_lt(x_140, x_141);
lean_dec(x_141);
lean_dec(x_140);
if (x_142 == 0)
{
lean_object* x_143; 
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_143 = lean_box(0);
lean_ctor_set(x_41, 0, x_143);
return x_41;
}
else
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; size_t x_149; lean_object* x_150; size_t x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
lean_free_object(x_41);
x_144 = lean_ctor_get(x_1, 2);
lean_inc(x_144);
x_145 = l_Lean_Compiler_LCNF_mkNewParams(x_144, x_5, x_6, x_7, x_8, x_50);
x_146 = lean_ctor_get(x_145, 0);
lean_inc(x_146);
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_145)) {
 lean_ctor_release(x_145, 0);
 lean_ctor_release(x_145, 1);
 x_148 = x_145;
} else {
 lean_dec_ref(x_145);
 x_148 = lean_box(0);
}
x_149 = lean_array_size(x_146);
x_150 = lean_unsigned_to_nat(0u);
x_151 = lean_usize_of_nat(x_150);
lean_inc(x_146);
x_152 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_149, x_151, x_146);
x_153 = l_Array_append(lean_box(0), x_18, x_152);
lean_dec(x_152);
lean_ctor_set(x_14, 2, x_153);
x_154 = lean_mk_string_unchecked("_x", 2, 2);
x_155 = l_Lean_Name_mkStr1(x_154);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_156 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_14, x_155, x_5, x_6, x_7, x_8, x_147);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_159);
if (lean_is_scalar(x_148)) {
 x_160 = lean_alloc_ctor(0, 2, 0);
} else {
 x_160 = x_148;
}
lean_ctor_set(x_160, 0, x_157);
lean_ctor_set(x_160, 1, x_26);
x_161 = lean_mk_string_unchecked("_f", 2, 2);
x_162 = l_Lean_Name_mkStr1(x_161);
x_163 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_146, x_160, x_162, x_5, x_6, x_7, x_8, x_158);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = lean_ctor_get(x_1, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_164, 0);
lean_inc(x_167);
x_168 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_166, x_167, x_3, x_6, x_7, x_8, x_165);
if (lean_obj_tag(x_168) == 0)
{
lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_169 = lean_ctor_get(x_168, 1);
lean_inc(x_169);
lean_dec(x_168);
x_170 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_169);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_171 = lean_ctor_get(x_170, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_170)) {
 lean_ctor_release(x_170, 0);
 lean_ctor_release(x_170, 1);
 x_172 = x_170;
} else {
 lean_dec_ref(x_170);
 x_172 = lean_box(0);
}
x_173 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_173, 0, x_164);
if (lean_is_scalar(x_172)) {
 x_174 = lean_alloc_ctor(0, 2, 0);
} else {
 x_174 = x_172;
}
lean_ctor_set(x_174, 0, x_173);
lean_ctor_set(x_174, 1, x_171);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; 
lean_dec(x_164);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_175 = lean_ctor_get(x_168, 0);
lean_inc(x_175);
x_176 = lean_ctor_get(x_168, 1);
lean_inc(x_176);
if (lean_is_exclusive(x_168)) {
 lean_ctor_release(x_168, 0);
 lean_ctor_release(x_168, 1);
 x_177 = x_168;
} else {
 lean_dec_ref(x_168);
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
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_179 = lean_ctor_get(x_163, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_163, 1);
lean_inc(x_180);
if (lean_is_exclusive(x_163)) {
 lean_ctor_release(x_163, 0);
 lean_ctor_release(x_163, 1);
 x_181 = x_163;
} else {
 lean_dec_ref(x_163);
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
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; 
lean_dec(x_148);
lean_dec(x_146);
lean_free_object(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_183 = lean_ctor_get(x_156, 0);
lean_inc(x_183);
x_184 = lean_ctor_get(x_156, 1);
lean_inc(x_184);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_185 = x_156;
} else {
 lean_dec_ref(x_156);
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
}
else
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; 
x_187 = lean_ctor_get(x_41, 1);
lean_inc(x_187);
lean_dec(x_41);
x_188 = lean_ctor_get(x_42, 0);
lean_inc(x_188);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_189 = x_42;
} else {
 lean_dec_ref(x_42);
 x_189 = lean_box(0);
}
x_190 = lean_array_get_size(x_18);
x_191 = l_Lean_Compiler_LCNF_Decl_getArity(x_188);
lean_dec(x_188);
x_192 = lean_nat_dec_lt(x_190, x_191);
lean_dec(x_191);
lean_dec(x_190);
if (x_192 == 0)
{
lean_object* x_193; lean_object* x_194; 
lean_dec(x_189);
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_193 = lean_box(0);
x_194 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_194, 0, x_193);
lean_ctor_set(x_194, 1, x_187);
return x_194;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; size_t x_200; lean_object* x_201; size_t x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; 
x_195 = lean_ctor_get(x_1, 2);
lean_inc(x_195);
x_196 = l_Lean_Compiler_LCNF_mkNewParams(x_195, x_5, x_6, x_7, x_8, x_187);
x_197 = lean_ctor_get(x_196, 0);
lean_inc(x_197);
x_198 = lean_ctor_get(x_196, 1);
lean_inc(x_198);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_199 = x_196;
} else {
 lean_dec_ref(x_196);
 x_199 = lean_box(0);
}
x_200 = lean_array_size(x_197);
x_201 = lean_unsigned_to_nat(0u);
x_202 = lean_usize_of_nat(x_201);
lean_inc(x_197);
x_203 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_200, x_202, x_197);
x_204 = l_Array_append(lean_box(0), x_18, x_203);
lean_dec(x_203);
lean_ctor_set(x_14, 2, x_204);
x_205 = lean_mk_string_unchecked("_x", 2, 2);
x_206 = l_Lean_Name_mkStr1(x_205);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_207 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_14, x_206, x_5, x_6, x_7, x_8, x_198);
if (lean_obj_tag(x_207) == 0)
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; 
x_208 = lean_ctor_get(x_207, 0);
lean_inc(x_208);
x_209 = lean_ctor_get(x_207, 1);
lean_inc(x_209);
lean_dec(x_207);
x_210 = lean_ctor_get(x_208, 0);
lean_inc(x_210);
lean_ctor_set_tag(x_26, 5);
lean_ctor_set(x_26, 0, x_210);
if (lean_is_scalar(x_199)) {
 x_211 = lean_alloc_ctor(0, 2, 0);
} else {
 x_211 = x_199;
}
lean_ctor_set(x_211, 0, x_208);
lean_ctor_set(x_211, 1, x_26);
x_212 = lean_mk_string_unchecked("_f", 2, 2);
x_213 = l_Lean_Name_mkStr1(x_212);
x_214 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_197, x_211, x_213, x_5, x_6, x_7, x_8, x_209);
if (lean_obj_tag(x_214) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_215 = lean_ctor_get(x_214, 0);
lean_inc(x_215);
x_216 = lean_ctor_get(x_214, 1);
lean_inc(x_216);
lean_dec(x_214);
x_217 = lean_ctor_get(x_1, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_215, 0);
lean_inc(x_218);
x_219 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_217, x_218, x_3, x_6, x_7, x_8, x_216);
if (lean_obj_tag(x_219) == 0)
{
lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; 
x_220 = lean_ctor_get(x_219, 1);
lean_inc(x_220);
lean_dec(x_219);
x_221 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_220);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
if (lean_is_exclusive(x_221)) {
 lean_ctor_release(x_221, 0);
 lean_ctor_release(x_221, 1);
 x_223 = x_221;
} else {
 lean_dec_ref(x_221);
 x_223 = lean_box(0);
}
if (lean_is_scalar(x_189)) {
 x_224 = lean_alloc_ctor(1, 1, 0);
} else {
 x_224 = x_189;
}
lean_ctor_set(x_224, 0, x_215);
if (lean_is_scalar(x_223)) {
 x_225 = lean_alloc_ctor(0, 2, 0);
} else {
 x_225 = x_223;
}
lean_ctor_set(x_225, 0, x_224);
lean_ctor_set(x_225, 1, x_222);
return x_225;
}
else
{
lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
lean_dec(x_215);
lean_dec(x_189);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_226 = lean_ctor_get(x_219, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_219, 1);
lean_inc(x_227);
if (lean_is_exclusive(x_219)) {
 lean_ctor_release(x_219, 0);
 lean_ctor_release(x_219, 1);
 x_228 = x_219;
} else {
 lean_dec_ref(x_219);
 x_228 = lean_box(0);
}
if (lean_is_scalar(x_228)) {
 x_229 = lean_alloc_ctor(1, 2, 0);
} else {
 x_229 = x_228;
}
lean_ctor_set(x_229, 0, x_226);
lean_ctor_set(x_229, 1, x_227);
return x_229;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_189);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_230 = lean_ctor_get(x_214, 0);
lean_inc(x_230);
x_231 = lean_ctor_get(x_214, 1);
lean_inc(x_231);
if (lean_is_exclusive(x_214)) {
 lean_ctor_release(x_214, 0);
 lean_ctor_release(x_214, 1);
 x_232 = x_214;
} else {
 lean_dec_ref(x_214);
 x_232 = lean_box(0);
}
if (lean_is_scalar(x_232)) {
 x_233 = lean_alloc_ctor(1, 2, 0);
} else {
 x_233 = x_232;
}
lean_ctor_set(x_233, 0, x_230);
lean_ctor_set(x_233, 1, x_231);
return x_233;
}
}
else
{
lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; 
lean_dec(x_199);
lean_dec(x_197);
lean_dec(x_189);
lean_free_object(x_26);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_234 = lean_ctor_get(x_207, 0);
lean_inc(x_234);
x_235 = lean_ctor_get(x_207, 1);
lean_inc(x_235);
if (lean_is_exclusive(x_207)) {
 lean_ctor_release(x_207, 0);
 lean_ctor_release(x_207, 1);
 x_236 = x_207;
} else {
 lean_dec_ref(x_207);
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
}
}
}
}
else
{
lean_free_object(x_26);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_39;
}
block_39:
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_box(0);
if (lean_is_scalar(x_36)) {
 x_38 = lean_alloc_ctor(0, 2, 0);
} else {
 x_38 = x_36;
}
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_35);
return x_38;
}
}
}
else
{
lean_object* x_238; lean_object* x_239; uint8_t x_240; 
x_238 = lean_ctor_get(x_26, 0);
lean_inc(x_238);
lean_dec(x_26);
x_239 = l_Lean_ConstantInfo_type(x_238);
lean_dec(x_238);
x_240 = l_Lean_Compiler_LCNF_hasLocalInst(x_239);
lean_dec(x_239);
if (x_240 == 0)
{
lean_object* x_241; 
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_241 = lean_box(0);
lean_ctor_set(x_19, 0, x_241);
return x_19;
}
else
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; uint8_t x_249; 
lean_free_object(x_19);
x_242 = l_Lean_Meta_isInstance___redArg(x_16, x_8, x_22);
x_243 = lean_ctor_get(x_242, 0);
lean_inc(x_243);
x_244 = lean_ctor_get(x_242, 1);
lean_inc(x_244);
if (lean_is_exclusive(x_242)) {
 lean_ctor_release(x_242, 0);
 lean_ctor_release(x_242, 1);
 x_245 = x_242;
} else {
 lean_dec_ref(x_242);
 x_245 = lean_box(0);
}
x_249 = lean_unbox(x_243);
lean_dec(x_243);
if (x_249 == 0)
{
if (x_240 == 0)
{
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_248;
}
else
{
lean_object* x_250; lean_object* x_251; 
lean_dec(x_245);
lean_inc(x_16);
x_250 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_16, x_5, x_8, x_244);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
if (lean_obj_tag(x_251) == 0)
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_252 = lean_ctor_get(x_250, 1);
lean_inc(x_252);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_253 = x_250;
} else {
 lean_dec_ref(x_250);
 x_253 = lean_box(0);
}
x_254 = lean_box(0);
if (lean_is_scalar(x_253)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_253;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_252);
return x_255;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; uint8_t x_262; 
x_256 = lean_ctor_get(x_250, 1);
lean_inc(x_256);
if (lean_is_exclusive(x_250)) {
 lean_ctor_release(x_250, 0);
 lean_ctor_release(x_250, 1);
 x_257 = x_250;
} else {
 lean_dec_ref(x_250);
 x_257 = lean_box(0);
}
x_258 = lean_ctor_get(x_251, 0);
lean_inc(x_258);
if (lean_is_exclusive(x_251)) {
 lean_ctor_release(x_251, 0);
 x_259 = x_251;
} else {
 lean_dec_ref(x_251);
 x_259 = lean_box(0);
}
x_260 = lean_array_get_size(x_18);
x_261 = l_Lean_Compiler_LCNF_Decl_getArity(x_258);
lean_dec(x_258);
x_262 = lean_nat_dec_lt(x_260, x_261);
lean_dec(x_261);
lean_dec(x_260);
if (x_262 == 0)
{
lean_object* x_263; lean_object* x_264; 
lean_dec(x_259);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_263 = lean_box(0);
if (lean_is_scalar(x_257)) {
 x_264 = lean_alloc_ctor(0, 2, 0);
} else {
 x_264 = x_257;
}
lean_ctor_set(x_264, 0, x_263);
lean_ctor_set(x_264, 1, x_256);
return x_264;
}
else
{
lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; size_t x_270; lean_object* x_271; size_t x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; 
lean_dec(x_257);
x_265 = lean_ctor_get(x_1, 2);
lean_inc(x_265);
x_266 = l_Lean_Compiler_LCNF_mkNewParams(x_265, x_5, x_6, x_7, x_8, x_256);
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = lean_array_size(x_267);
x_271 = lean_unsigned_to_nat(0u);
x_272 = lean_usize_of_nat(x_271);
lean_inc(x_267);
x_273 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_270, x_272, x_267);
x_274 = l_Array_append(lean_box(0), x_18, x_273);
lean_dec(x_273);
lean_ctor_set(x_14, 2, x_274);
x_275 = lean_mk_string_unchecked("_x", 2, 2);
x_276 = l_Lean_Name_mkStr1(x_275);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_277 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_14, x_276, x_5, x_6, x_7, x_8, x_268);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
x_279 = lean_ctor_get(x_277, 1);
lean_inc(x_279);
lean_dec(x_277);
x_280 = lean_ctor_get(x_278, 0);
lean_inc(x_280);
x_281 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_281, 0, x_280);
if (lean_is_scalar(x_269)) {
 x_282 = lean_alloc_ctor(0, 2, 0);
} else {
 x_282 = x_269;
}
lean_ctor_set(x_282, 0, x_278);
lean_ctor_set(x_282, 1, x_281);
x_283 = lean_mk_string_unchecked("_f", 2, 2);
x_284 = l_Lean_Name_mkStr1(x_283);
x_285 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_267, x_282, x_284, x_5, x_6, x_7, x_8, x_279);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; 
x_286 = lean_ctor_get(x_285, 0);
lean_inc(x_286);
x_287 = lean_ctor_get(x_285, 1);
lean_inc(x_287);
lean_dec(x_285);
x_288 = lean_ctor_get(x_1, 0);
lean_inc(x_288);
x_289 = lean_ctor_get(x_286, 0);
lean_inc(x_289);
x_290 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_288, x_289, x_3, x_6, x_7, x_8, x_287);
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; 
x_291 = lean_ctor_get(x_290, 1);
lean_inc(x_291);
lean_dec(x_290);
x_292 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_291);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_293 = lean_ctor_get(x_292, 1);
lean_inc(x_293);
if (lean_is_exclusive(x_292)) {
 lean_ctor_release(x_292, 0);
 lean_ctor_release(x_292, 1);
 x_294 = x_292;
} else {
 lean_dec_ref(x_292);
 x_294 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_295 = lean_alloc_ctor(1, 1, 0);
} else {
 x_295 = x_259;
}
lean_ctor_set(x_295, 0, x_286);
if (lean_is_scalar(x_294)) {
 x_296 = lean_alloc_ctor(0, 2, 0);
} else {
 x_296 = x_294;
}
lean_ctor_set(x_296, 0, x_295);
lean_ctor_set(x_296, 1, x_293);
return x_296;
}
else
{
lean_object* x_297; lean_object* x_298; lean_object* x_299; lean_object* x_300; 
lean_dec(x_286);
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_297 = lean_ctor_get(x_290, 0);
lean_inc(x_297);
x_298 = lean_ctor_get(x_290, 1);
lean_inc(x_298);
if (lean_is_exclusive(x_290)) {
 lean_ctor_release(x_290, 0);
 lean_ctor_release(x_290, 1);
 x_299 = x_290;
} else {
 lean_dec_ref(x_290);
 x_299 = lean_box(0);
}
if (lean_is_scalar(x_299)) {
 x_300 = lean_alloc_ctor(1, 2, 0);
} else {
 x_300 = x_299;
}
lean_ctor_set(x_300, 0, x_297);
lean_ctor_set(x_300, 1, x_298);
return x_300;
}
}
else
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; 
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_301 = lean_ctor_get(x_285, 0);
lean_inc(x_301);
x_302 = lean_ctor_get(x_285, 1);
lean_inc(x_302);
if (lean_is_exclusive(x_285)) {
 lean_ctor_release(x_285, 0);
 lean_ctor_release(x_285, 1);
 x_303 = x_285;
} else {
 lean_dec_ref(x_285);
 x_303 = lean_box(0);
}
if (lean_is_scalar(x_303)) {
 x_304 = lean_alloc_ctor(1, 2, 0);
} else {
 x_304 = x_303;
}
lean_ctor_set(x_304, 0, x_301);
lean_ctor_set(x_304, 1, x_302);
return x_304;
}
}
else
{
lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_269);
lean_dec(x_267);
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_305 = lean_ctor_get(x_277, 0);
lean_inc(x_305);
x_306 = lean_ctor_get(x_277, 1);
lean_inc(x_306);
if (lean_is_exclusive(x_277)) {
 lean_ctor_release(x_277, 0);
 lean_ctor_release(x_277, 1);
 x_307 = x_277;
} else {
 lean_dec_ref(x_277);
 x_307 = lean_box(0);
}
if (lean_is_scalar(x_307)) {
 x_308 = lean_alloc_ctor(1, 2, 0);
} else {
 x_308 = x_307;
}
lean_ctor_set(x_308, 0, x_305);
lean_ctor_set(x_308, 1, x_306);
return x_308;
}
}
}
}
}
else
{
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_248;
}
block_248:
{
lean_object* x_246; lean_object* x_247; 
x_246 = lean_box(0);
if (lean_is_scalar(x_245)) {
 x_247 = lean_alloc_ctor(0, 2, 0);
} else {
 x_247 = x_245;
}
lean_ctor_set(x_247, 0, x_246);
lean_ctor_set(x_247, 1, x_244);
return x_247;
}
}
}
}
}
else
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; uint8_t x_313; lean_object* x_314; 
x_309 = lean_ctor_get(x_19, 0);
x_310 = lean_ctor_get(x_19, 1);
lean_inc(x_310);
lean_inc(x_309);
lean_dec(x_19);
x_311 = lean_ctor_get(x_309, 0);
lean_inc(x_311);
lean_dec(x_309);
x_312 = lean_box(0);
x_313 = lean_unbox(x_312);
lean_inc(x_16);
x_314 = l_Lean_Environment_find_x3f(x_311, x_16, x_313);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; 
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_315 = lean_box(0);
x_316 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_316, 0, x_315);
lean_ctor_set(x_316, 1, x_310);
return x_316;
}
else
{
lean_object* x_317; lean_object* x_318; lean_object* x_319; uint8_t x_320; 
x_317 = lean_ctor_get(x_314, 0);
lean_inc(x_317);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 x_318 = x_314;
} else {
 lean_dec_ref(x_314);
 x_318 = lean_box(0);
}
x_319 = l_Lean_ConstantInfo_type(x_317);
lean_dec(x_317);
x_320 = l_Lean_Compiler_LCNF_hasLocalInst(x_319);
lean_dec(x_319);
if (x_320 == 0)
{
lean_object* x_321; lean_object* x_322; 
lean_dec(x_318);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_321 = lean_box(0);
x_322 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_322, 0, x_321);
lean_ctor_set(x_322, 1, x_310);
return x_322;
}
else
{
lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; uint8_t x_330; 
x_323 = l_Lean_Meta_isInstance___redArg(x_16, x_8, x_310);
x_324 = lean_ctor_get(x_323, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_323, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_323)) {
 lean_ctor_release(x_323, 0);
 lean_ctor_release(x_323, 1);
 x_326 = x_323;
} else {
 lean_dec_ref(x_323);
 x_326 = lean_box(0);
}
x_330 = lean_unbox(x_324);
lean_dec(x_324);
if (x_330 == 0)
{
if (x_320 == 0)
{
lean_dec(x_318);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_329;
}
else
{
lean_object* x_331; lean_object* x_332; 
lean_dec(x_326);
lean_inc(x_16);
x_331 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_16, x_5, x_8, x_325);
x_332 = lean_ctor_get(x_331, 0);
lean_inc(x_332);
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; 
lean_dec(x_318);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_333 = lean_ctor_get(x_331, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_334 = x_331;
} else {
 lean_dec_ref(x_331);
 x_334 = lean_box(0);
}
x_335 = lean_box(0);
if (lean_is_scalar(x_334)) {
 x_336 = lean_alloc_ctor(0, 2, 0);
} else {
 x_336 = x_334;
}
lean_ctor_set(x_336, 0, x_335);
lean_ctor_set(x_336, 1, x_333);
return x_336;
}
else
{
lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; 
x_337 = lean_ctor_get(x_331, 1);
lean_inc(x_337);
if (lean_is_exclusive(x_331)) {
 lean_ctor_release(x_331, 0);
 lean_ctor_release(x_331, 1);
 x_338 = x_331;
} else {
 lean_dec_ref(x_331);
 x_338 = lean_box(0);
}
x_339 = lean_ctor_get(x_332, 0);
lean_inc(x_339);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_340 = x_332;
} else {
 lean_dec_ref(x_332);
 x_340 = lean_box(0);
}
x_341 = lean_array_get_size(x_18);
x_342 = l_Lean_Compiler_LCNF_Decl_getArity(x_339);
lean_dec(x_339);
x_343 = lean_nat_dec_lt(x_341, x_342);
lean_dec(x_342);
lean_dec(x_341);
if (x_343 == 0)
{
lean_object* x_344; lean_object* x_345; 
lean_dec(x_340);
lean_dec(x_318);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_344 = lean_box(0);
if (lean_is_scalar(x_338)) {
 x_345 = lean_alloc_ctor(0, 2, 0);
} else {
 x_345 = x_338;
}
lean_ctor_set(x_345, 0, x_344);
lean_ctor_set(x_345, 1, x_337);
return x_345;
}
else
{
lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; size_t x_351; lean_object* x_352; size_t x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; 
lean_dec(x_338);
x_346 = lean_ctor_get(x_1, 2);
lean_inc(x_346);
x_347 = l_Lean_Compiler_LCNF_mkNewParams(x_346, x_5, x_6, x_7, x_8, x_337);
x_348 = lean_ctor_get(x_347, 0);
lean_inc(x_348);
x_349 = lean_ctor_get(x_347, 1);
lean_inc(x_349);
if (lean_is_exclusive(x_347)) {
 lean_ctor_release(x_347, 0);
 lean_ctor_release(x_347, 1);
 x_350 = x_347;
} else {
 lean_dec_ref(x_347);
 x_350 = lean_box(0);
}
x_351 = lean_array_size(x_348);
x_352 = lean_unsigned_to_nat(0u);
x_353 = lean_usize_of_nat(x_352);
lean_inc(x_348);
x_354 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_351, x_353, x_348);
x_355 = l_Array_append(lean_box(0), x_18, x_354);
lean_dec(x_354);
lean_ctor_set(x_14, 2, x_355);
x_356 = lean_mk_string_unchecked("_x", 2, 2);
x_357 = l_Lean_Name_mkStr1(x_356);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_358 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_14, x_357, x_5, x_6, x_7, x_8, x_349);
if (lean_obj_tag(x_358) == 0)
{
lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
x_359 = lean_ctor_get(x_358, 0);
lean_inc(x_359);
x_360 = lean_ctor_get(x_358, 1);
lean_inc(x_360);
lean_dec(x_358);
x_361 = lean_ctor_get(x_359, 0);
lean_inc(x_361);
if (lean_is_scalar(x_318)) {
 x_362 = lean_alloc_ctor(5, 1, 0);
} else {
 x_362 = x_318;
 lean_ctor_set_tag(x_362, 5);
}
lean_ctor_set(x_362, 0, x_361);
if (lean_is_scalar(x_350)) {
 x_363 = lean_alloc_ctor(0, 2, 0);
} else {
 x_363 = x_350;
}
lean_ctor_set(x_363, 0, x_359);
lean_ctor_set(x_363, 1, x_362);
x_364 = lean_mk_string_unchecked("_f", 2, 2);
x_365 = l_Lean_Name_mkStr1(x_364);
x_366 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_348, x_363, x_365, x_5, x_6, x_7, x_8, x_360);
if (lean_obj_tag(x_366) == 0)
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; 
x_367 = lean_ctor_get(x_366, 0);
lean_inc(x_367);
x_368 = lean_ctor_get(x_366, 1);
lean_inc(x_368);
lean_dec(x_366);
x_369 = lean_ctor_get(x_1, 0);
lean_inc(x_369);
x_370 = lean_ctor_get(x_367, 0);
lean_inc(x_370);
x_371 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_369, x_370, x_3, x_6, x_7, x_8, x_368);
if (lean_obj_tag(x_371) == 0)
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; 
x_372 = lean_ctor_get(x_371, 1);
lean_inc(x_372);
lean_dec(x_371);
x_373 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_372);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_374 = lean_ctor_get(x_373, 1);
lean_inc(x_374);
if (lean_is_exclusive(x_373)) {
 lean_ctor_release(x_373, 0);
 lean_ctor_release(x_373, 1);
 x_375 = x_373;
} else {
 lean_dec_ref(x_373);
 x_375 = lean_box(0);
}
if (lean_is_scalar(x_340)) {
 x_376 = lean_alloc_ctor(1, 1, 0);
} else {
 x_376 = x_340;
}
lean_ctor_set(x_376, 0, x_367);
if (lean_is_scalar(x_375)) {
 x_377 = lean_alloc_ctor(0, 2, 0);
} else {
 x_377 = x_375;
}
lean_ctor_set(x_377, 0, x_376);
lean_ctor_set(x_377, 1, x_374);
return x_377;
}
else
{
lean_object* x_378; lean_object* x_379; lean_object* x_380; lean_object* x_381; 
lean_dec(x_367);
lean_dec(x_340);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_378 = lean_ctor_get(x_371, 0);
lean_inc(x_378);
x_379 = lean_ctor_get(x_371, 1);
lean_inc(x_379);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 lean_ctor_release(x_371, 1);
 x_380 = x_371;
} else {
 lean_dec_ref(x_371);
 x_380 = lean_box(0);
}
if (lean_is_scalar(x_380)) {
 x_381 = lean_alloc_ctor(1, 2, 0);
} else {
 x_381 = x_380;
}
lean_ctor_set(x_381, 0, x_378);
lean_ctor_set(x_381, 1, x_379);
return x_381;
}
}
else
{
lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_340);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_382 = lean_ctor_get(x_366, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_366, 1);
lean_inc(x_383);
if (lean_is_exclusive(x_366)) {
 lean_ctor_release(x_366, 0);
 lean_ctor_release(x_366, 1);
 x_384 = x_366;
} else {
 lean_dec_ref(x_366);
 x_384 = lean_box(0);
}
if (lean_is_scalar(x_384)) {
 x_385 = lean_alloc_ctor(1, 2, 0);
} else {
 x_385 = x_384;
}
lean_ctor_set(x_385, 0, x_382);
lean_ctor_set(x_385, 1, x_383);
return x_385;
}
}
else
{
lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; 
lean_dec(x_350);
lean_dec(x_348);
lean_dec(x_340);
lean_dec(x_318);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_386 = lean_ctor_get(x_358, 0);
lean_inc(x_386);
x_387 = lean_ctor_get(x_358, 1);
lean_inc(x_387);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_388 = x_358;
} else {
 lean_dec_ref(x_358);
 x_388 = lean_box(0);
}
if (lean_is_scalar(x_388)) {
 x_389 = lean_alloc_ctor(1, 2, 0);
} else {
 x_389 = x_388;
}
lean_ctor_set(x_389, 0, x_386);
lean_ctor_set(x_389, 1, x_387);
return x_389;
}
}
}
}
}
else
{
lean_dec(x_318);
lean_free_object(x_14);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_329;
}
block_329:
{
lean_object* x_327; lean_object* x_328; 
x_327 = lean_box(0);
if (lean_is_scalar(x_326)) {
 x_328 = lean_alloc_ctor(0, 2, 0);
} else {
 x_328 = x_326;
}
lean_ctor_set(x_328, 0, x_327);
lean_ctor_set(x_328, 1, x_325);
return x_328;
}
}
}
}
}
else
{
lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; uint8_t x_399; lean_object* x_400; 
x_390 = lean_ctor_get(x_14, 0);
x_391 = lean_ctor_get(x_14, 1);
x_392 = lean_ctor_get(x_14, 2);
lean_inc(x_392);
lean_inc(x_391);
lean_inc(x_390);
lean_dec(x_14);
x_393 = lean_st_ref_get(x_8, x_9);
x_394 = lean_ctor_get(x_393, 0);
lean_inc(x_394);
x_395 = lean_ctor_get(x_393, 1);
lean_inc(x_395);
if (lean_is_exclusive(x_393)) {
 lean_ctor_release(x_393, 0);
 lean_ctor_release(x_393, 1);
 x_396 = x_393;
} else {
 lean_dec_ref(x_393);
 x_396 = lean_box(0);
}
x_397 = lean_ctor_get(x_394, 0);
lean_inc(x_397);
lean_dec(x_394);
x_398 = lean_box(0);
x_399 = lean_unbox(x_398);
lean_inc(x_390);
x_400 = l_Lean_Environment_find_x3f(x_397, x_390, x_399);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; 
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_401 = lean_box(0);
if (lean_is_scalar(x_396)) {
 x_402 = lean_alloc_ctor(0, 2, 0);
} else {
 x_402 = x_396;
}
lean_ctor_set(x_402, 0, x_401);
lean_ctor_set(x_402, 1, x_395);
return x_402;
}
else
{
lean_object* x_403; lean_object* x_404; lean_object* x_405; uint8_t x_406; 
x_403 = lean_ctor_get(x_400, 0);
lean_inc(x_403);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 x_404 = x_400;
} else {
 lean_dec_ref(x_400);
 x_404 = lean_box(0);
}
x_405 = l_Lean_ConstantInfo_type(x_403);
lean_dec(x_403);
x_406 = l_Lean_Compiler_LCNF_hasLocalInst(x_405);
lean_dec(x_405);
if (x_406 == 0)
{
lean_object* x_407; lean_object* x_408; 
lean_dec(x_404);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_407 = lean_box(0);
if (lean_is_scalar(x_396)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_396;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_395);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; uint8_t x_416; 
lean_dec(x_396);
x_409 = l_Lean_Meta_isInstance___redArg(x_390, x_8, x_395);
x_410 = lean_ctor_get(x_409, 0);
lean_inc(x_410);
x_411 = lean_ctor_get(x_409, 1);
lean_inc(x_411);
if (lean_is_exclusive(x_409)) {
 lean_ctor_release(x_409, 0);
 lean_ctor_release(x_409, 1);
 x_412 = x_409;
} else {
 lean_dec_ref(x_409);
 x_412 = lean_box(0);
}
x_416 = lean_unbox(x_410);
lean_dec(x_410);
if (x_416 == 0)
{
if (x_406 == 0)
{
lean_dec(x_404);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_415;
}
else
{
lean_object* x_417; lean_object* x_418; 
lean_dec(x_412);
lean_inc(x_390);
x_417 = l_Lean_Compiler_LCNF_getDecl_x3f___redArg(x_390, x_5, x_8, x_411);
x_418 = lean_ctor_get(x_417, 0);
lean_inc(x_418);
if (lean_obj_tag(x_418) == 0)
{
lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; 
lean_dec(x_404);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_419 = lean_ctor_get(x_417, 1);
lean_inc(x_419);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_420 = x_417;
} else {
 lean_dec_ref(x_417);
 x_420 = lean_box(0);
}
x_421 = lean_box(0);
if (lean_is_scalar(x_420)) {
 x_422 = lean_alloc_ctor(0, 2, 0);
} else {
 x_422 = x_420;
}
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_419);
return x_422;
}
else
{
lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; uint8_t x_429; 
x_423 = lean_ctor_get(x_417, 1);
lean_inc(x_423);
if (lean_is_exclusive(x_417)) {
 lean_ctor_release(x_417, 0);
 lean_ctor_release(x_417, 1);
 x_424 = x_417;
} else {
 lean_dec_ref(x_417);
 x_424 = lean_box(0);
}
x_425 = lean_ctor_get(x_418, 0);
lean_inc(x_425);
if (lean_is_exclusive(x_418)) {
 lean_ctor_release(x_418, 0);
 x_426 = x_418;
} else {
 lean_dec_ref(x_418);
 x_426 = lean_box(0);
}
x_427 = lean_array_get_size(x_392);
x_428 = l_Lean_Compiler_LCNF_Decl_getArity(x_425);
lean_dec(x_425);
x_429 = lean_nat_dec_lt(x_427, x_428);
lean_dec(x_428);
lean_dec(x_427);
if (x_429 == 0)
{
lean_object* x_430; lean_object* x_431; 
lean_dec(x_426);
lean_dec(x_404);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_430 = lean_box(0);
if (lean_is_scalar(x_424)) {
 x_431 = lean_alloc_ctor(0, 2, 0);
} else {
 x_431 = x_424;
}
lean_ctor_set(x_431, 0, x_430);
lean_ctor_set(x_431, 1, x_423);
return x_431;
}
else
{
lean_object* x_432; lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; size_t x_437; lean_object* x_438; size_t x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; 
lean_dec(x_424);
x_432 = lean_ctor_get(x_1, 2);
lean_inc(x_432);
x_433 = l_Lean_Compiler_LCNF_mkNewParams(x_432, x_5, x_6, x_7, x_8, x_423);
x_434 = lean_ctor_get(x_433, 0);
lean_inc(x_434);
x_435 = lean_ctor_get(x_433, 1);
lean_inc(x_435);
if (lean_is_exclusive(x_433)) {
 lean_ctor_release(x_433, 0);
 lean_ctor_release(x_433, 1);
 x_436 = x_433;
} else {
 lean_dec_ref(x_433);
 x_436 = lean_box(0);
}
x_437 = lean_array_size(x_434);
x_438 = lean_unsigned_to_nat(0u);
x_439 = lean_usize_of_nat(x_438);
lean_inc(x_434);
x_440 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx_spec__3(x_437, x_439, x_434);
x_441 = l_Array_append(lean_box(0), x_392, x_440);
lean_dec(x_440);
x_442 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_442, 0, x_390);
lean_ctor_set(x_442, 1, x_391);
lean_ctor_set(x_442, 2, x_441);
x_443 = lean_mk_string_unchecked("_x", 2, 2);
x_444 = l_Lean_Name_mkStr1(x_443);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_445 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_442, x_444, x_5, x_6, x_7, x_8, x_435);
if (lean_obj_tag(x_445) == 0)
{
lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; lean_object* x_451; lean_object* x_452; lean_object* x_453; 
x_446 = lean_ctor_get(x_445, 0);
lean_inc(x_446);
x_447 = lean_ctor_get(x_445, 1);
lean_inc(x_447);
lean_dec(x_445);
x_448 = lean_ctor_get(x_446, 0);
lean_inc(x_448);
if (lean_is_scalar(x_404)) {
 x_449 = lean_alloc_ctor(5, 1, 0);
} else {
 x_449 = x_404;
 lean_ctor_set_tag(x_449, 5);
}
lean_ctor_set(x_449, 0, x_448);
if (lean_is_scalar(x_436)) {
 x_450 = lean_alloc_ctor(0, 2, 0);
} else {
 x_450 = x_436;
}
lean_ctor_set(x_450, 0, x_446);
lean_ctor_set(x_450, 1, x_449);
x_451 = lean_mk_string_unchecked("_f", 2, 2);
x_452 = l_Lean_Name_mkStr1(x_451);
x_453 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_434, x_450, x_452, x_5, x_6, x_7, x_8, x_447);
if (lean_obj_tag(x_453) == 0)
{
lean_object* x_454; lean_object* x_455; lean_object* x_456; lean_object* x_457; lean_object* x_458; 
x_454 = lean_ctor_get(x_453, 0);
lean_inc(x_454);
x_455 = lean_ctor_get(x_453, 1);
lean_inc(x_455);
lean_dec(x_453);
x_456 = lean_ctor_get(x_1, 0);
lean_inc(x_456);
x_457 = lean_ctor_get(x_454, 0);
lean_inc(x_457);
x_458 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_456, x_457, x_3, x_6, x_7, x_8, x_455);
if (lean_obj_tag(x_458) == 0)
{
lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; lean_object* x_464; 
x_459 = lean_ctor_get(x_458, 1);
lean_inc(x_459);
lean_dec(x_458);
x_460 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_459);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_461 = lean_ctor_get(x_460, 1);
lean_inc(x_461);
if (lean_is_exclusive(x_460)) {
 lean_ctor_release(x_460, 0);
 lean_ctor_release(x_460, 1);
 x_462 = x_460;
} else {
 lean_dec_ref(x_460);
 x_462 = lean_box(0);
}
if (lean_is_scalar(x_426)) {
 x_463 = lean_alloc_ctor(1, 1, 0);
} else {
 x_463 = x_426;
}
lean_ctor_set(x_463, 0, x_454);
if (lean_is_scalar(x_462)) {
 x_464 = lean_alloc_ctor(0, 2, 0);
} else {
 x_464 = x_462;
}
lean_ctor_set(x_464, 0, x_463);
lean_ctor_set(x_464, 1, x_461);
return x_464;
}
else
{
lean_object* x_465; lean_object* x_466; lean_object* x_467; lean_object* x_468; 
lean_dec(x_454);
lean_dec(x_426);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_465 = lean_ctor_get(x_458, 0);
lean_inc(x_465);
x_466 = lean_ctor_get(x_458, 1);
lean_inc(x_466);
if (lean_is_exclusive(x_458)) {
 lean_ctor_release(x_458, 0);
 lean_ctor_release(x_458, 1);
 x_467 = x_458;
} else {
 lean_dec_ref(x_458);
 x_467 = lean_box(0);
}
if (lean_is_scalar(x_467)) {
 x_468 = lean_alloc_ctor(1, 2, 0);
} else {
 x_468 = x_467;
}
lean_ctor_set(x_468, 0, x_465);
lean_ctor_set(x_468, 1, x_466);
return x_468;
}
}
else
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; 
lean_dec(x_426);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_469 = lean_ctor_get(x_453, 0);
lean_inc(x_469);
x_470 = lean_ctor_get(x_453, 1);
lean_inc(x_470);
if (lean_is_exclusive(x_453)) {
 lean_ctor_release(x_453, 0);
 lean_ctor_release(x_453, 1);
 x_471 = x_453;
} else {
 lean_dec_ref(x_453);
 x_471 = lean_box(0);
}
if (lean_is_scalar(x_471)) {
 x_472 = lean_alloc_ctor(1, 2, 0);
} else {
 x_472 = x_471;
}
lean_ctor_set(x_472, 0, x_469);
lean_ctor_set(x_472, 1, x_470);
return x_472;
}
}
else
{
lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; 
lean_dec(x_436);
lean_dec(x_434);
lean_dec(x_426);
lean_dec(x_404);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_473 = lean_ctor_get(x_445, 0);
lean_inc(x_473);
x_474 = lean_ctor_get(x_445, 1);
lean_inc(x_474);
if (lean_is_exclusive(x_445)) {
 lean_ctor_release(x_445, 0);
 lean_ctor_release(x_445, 1);
 x_475 = x_445;
} else {
 lean_dec_ref(x_445);
 x_475 = lean_box(0);
}
if (lean_is_scalar(x_475)) {
 x_476 = lean_alloc_ctor(1, 2, 0);
} else {
 x_476 = x_475;
}
lean_ctor_set(x_476, 0, x_473);
lean_ctor_set(x_476, 1, x_474);
return x_476;
}
}
}
}
}
else
{
lean_dec(x_404);
lean_dec(x_392);
lean_dec(x_391);
lean_dec(x_390);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
goto block_415;
}
block_415:
{
lean_object* x_413; lean_object* x_414; 
x_413 = lean_box(0);
if (lean_is_scalar(x_412)) {
 x_414 = lean_alloc_ctor(0, 2, 0);
} else {
 x_414 = x_412;
}
lean_ctor_set(x_414, 0, x_413);
lean_ctor_set(x_414, 1, x_411);
return x_414;
}
}
}
}
}
else
{
lean_object* x_477; lean_object* x_478; 
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_477 = lean_box(0);
x_478 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_9);
return x_478;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 5)
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = lean_st_ref_get(x_3, x_4);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_box(0);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unbox(x_9);
x_12 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_10, x_5, x_11);
lean_dec(x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
lean_dec(x_12);
x_14 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_13, x_2);
lean_dec(x_13);
x_15 = lean_box(x_14);
lean_ctor_set(x_6, 0, x_15);
return x_6;
}
else
{
lean_ctor_set(x_6, 0, x_9);
return x_6;
}
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; lean_object* x_21; 
x_16 = lean_ctor_get(x_6, 0);
x_17 = lean_ctor_get(x_6, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_6);
x_18 = lean_box(0);
x_19 = lean_ctor_get(x_16, 0);
lean_inc(x_19);
lean_dec(x_16);
x_20 = lean_unbox(x_18);
x_21 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_19, x_5, x_20);
lean_dec(x_19);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec(x_21);
x_23 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_22, x_2);
lean_dec(x_22);
x_24 = lean_box(x_23);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_24);
lean_ctor_set(x_25, 1, x_17);
return x_25;
}
else
{
lean_object* x_26; 
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_18);
lean_ctor_set(x_26, 1, x_17);
return x_26;
}
}
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_1);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_4);
return x_28;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_Simp_isReturnOf___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_isReturnOf___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Simp_isReturnOf(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
if (lean_obj_tag(x_1) == 4)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_1);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_1, 1);
x_10 = lean_array_get_size(x_9);
lean_dec(x_9);
x_11 = lean_unsigned_to_nat(0u);
x_12 = lean_nat_dec_eq(x_10, x_11);
lean_dec(x_10);
if (x_12 == 0)
{
lean_free_object(x_1);
lean_dec(x_8);
x_3 = x_2;
goto block_6;
}
else
{
lean_object* x_13; 
x_13 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_2);
lean_ctor_set(x_1, 0, x_13);
return x_1;
}
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_14 = lean_ctor_get(x_1, 0);
x_15 = lean_ctor_get(x_1, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_1);
x_16 = lean_array_get_size(x_15);
lean_dec(x_15);
x_17 = lean_unsigned_to_nat(0u);
x_18 = lean_nat_dec_eq(x_16, x_17);
lean_dec(x_16);
if (x_18 == 0)
{
lean_dec(x_14);
x_3 = x_2;
goto block_6;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_2);
return x_20;
}
}
}
else
{
lean_dec(x_1);
x_3 = x_2;
goto block_6;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_box(0);
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_4);
lean_ctor_set(x_5, 1, x_3);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_1, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_elimVar_x3f___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14) {
_start:
{
uint8_t x_15; 
x_15 = lean_nat_dec_lt(x_1, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_6, x_8, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_16, 1);
lean_inc(x_17);
lean_dec(x_16);
x_18 = l_Lean_Compiler_LCNF_Simp_simp(x_4, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_17);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_19 = !lean_is_exclusive(x_16);
if (x_19 == 0)
{
return x_16;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_16, 0);
x_21 = lean_ctor_get(x_16, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_16);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_23 = l_Array_toSubarray___redArg(x_5, x_1, x_2);
x_24 = l_Array_ofSubarray___redArg(x_23);
lean_dec(x_23);
x_25 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_25, 0, x_6);
lean_ctor_set(x_25, 1, x_24);
x_26 = lean_mk_string_unchecked("_x", 2, 2);
x_27 = l_Lean_Name_mkStr1(x_26);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
x_28 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_25, x_27, x_10, x_11, x_12, x_13, x_14);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
x_32 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_3, x_31, x_8, x_11, x_12, x_13, x_30);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_29);
lean_ctor_set(x_34, 1, x_4);
x_35 = l_Lean_Compiler_LCNF_Simp_simp(x_34, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_33);
return x_35;
}
else
{
uint8_t x_36; 
lean_dec(x_29);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
x_36 = !lean_is_exclusive(x_32);
if (x_36 == 0)
{
return x_32;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_32, 0);
x_38 = lean_ctor_get(x_32, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_32);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
else
{
uint8_t x_40; 
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
x_40 = !lean_is_exclusive(x_28);
if (x_40 == 0)
{
return x_28;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_28, 0);
x_42 = lean_ctor_get(x_28, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_28);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_9 = lean_ctor_get(x_1, 0);
x_10 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_10, 0, x_3);
x_11 = lean_mk_empty_array_with_capacity(x_2);
x_12 = lean_array_push(x_11, x_10);
lean_inc(x_9);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_9);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_8);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_inc(x_5);
x_11 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_5, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_10);
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_apply_9(x_4, x_5, x_1, x_2, x_3, x_6, x_7, x_8, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 3);
lean_inc(x_11);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_11);
x_12 = l_Lean_Compiler_LCNF_Simp_inlineCandidate_x3f(x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_14 = !lean_is_exclusive(x_12);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_12, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_12, 0, x_16);
return x_12;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_12, 1);
lean_inc(x_17);
lean_dec(x_12);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; 
x_20 = lean_ctor_get(x_12, 1);
lean_inc(x_20);
lean_dec(x_12);
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
if (lean_is_exclusive(x_13)) {
 lean_ctor_release(x_13, 0);
 x_22 = x_13;
} else {
 lean_dec_ref(x_13);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
x_24 = lean_array_get_size(x_23);
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
lean_dec(x_1);
x_26 = l_Lean_Compiler_LCNF_Simp_InlineCandidateInfo_arity(x_21);
lean_inc(x_23);
lean_inc(x_2);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0), 14, 5);
lean_closure_set(x_27, 0, x_26);
lean_closure_set(x_27, 1, x_24);
lean_closure_set(x_27, 2, x_25);
lean_closure_set(x_27, 3, x_2);
lean_closure_set(x_27, 4, x_23);
x_28 = lean_nat_dec_lt(x_24, x_26);
if (lean_obj_tag(x_11) == 3)
{
lean_object* x_260; uint8_t x_261; lean_object* x_262; 
x_260 = lean_ctor_get(x_11, 0);
lean_inc(x_260);
lean_dec(x_11);
x_261 = lean_ctor_get_uint8(x_21, sizeof(void*)*4 + 2);
lean_inc(x_3);
lean_inc(x_260);
x_262 = l_Lean_Compiler_LCNF_Simp_withInlining_check(x_261, x_260, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_20);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
x_264 = lean_ctor_get(x_262, 1);
lean_inc(x_264);
lean_dec(x_262);
x_265 = lean_ctor_get(x_3, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_3, 1);
lean_inc(x_266);
x_267 = lean_ctor_get(x_3, 2);
lean_inc(x_267);
lean_inc(x_260);
x_268 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_268, 0, x_260);
lean_ctor_set(x_268, 1, x_267);
x_269 = lean_ctor_get(x_3, 3);
lean_inc(x_269);
lean_dec(x_3);
x_270 = l_Lean_PersistentHashMap_insert___at___Lean_SMap_insert___at_____private_Lean_Environment_0__Lean_Kernel_Environment_add_spec__0_spec__0(lean_box(0), x_269, x_260, x_263);
x_271 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_271, 0, x_265);
lean_ctor_set(x_271, 1, x_266);
lean_ctor_set(x_271, 2, x_268);
lean_ctor_set(x_271, 3, x_270);
x_180 = x_271;
x_181 = x_4;
x_182 = x_5;
x_183 = x_6;
x_184 = x_7;
x_185 = x_8;
x_186 = x_9;
x_187 = x_264;
goto block_259;
}
else
{
uint8_t x_272; 
lean_dec(x_260);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_272 = !lean_is_exclusive(x_262);
if (x_272 == 0)
{
return x_262;
}
else
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_262, 0);
x_274 = lean_ctor_get(x_262, 1);
lean_inc(x_274);
lean_inc(x_273);
lean_dec(x_262);
x_275 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_275, 0, x_273);
lean_ctor_set(x_275, 1, x_274);
return x_275;
}
}
}
else
{
lean_dec(x_11);
x_180 = x_3;
x_181 = x_4;
x_182 = x_5;
x_183 = x_6;
x_184 = x_7;
x_185 = x_8;
x_186 = x_9;
x_187 = x_20;
goto block_259;
}
block_179:
{
lean_object* x_41; 
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_31);
lean_inc(x_32);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
x_41 = l_Lean_Compiler_LCNF_Simp_simp(x_39, x_33, x_34, x_36, x_32, x_31, x_40, x_38, x_30);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
lean_inc(x_42);
x_44 = l___private_Lean_Compiler_LCNF_Simp_Main_0__Lean_Compiler_LCNF_Simp_oneExitPointQuick_go(x_42);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
lean_dec(x_37);
x_45 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_34, x_43);
x_46 = lean_ctor_get(x_45, 1);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_ctor_get(x_21, 2);
lean_inc(x_47);
lean_dec(x_21);
x_48 = l_Lean_Compiler_LCNF_inferAppType(x_47, x_35, x_32, x_31, x_40, x_38, x_46);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
lean_inc(x_49);
x_51 = l_Lean_Expr_headBeta(x_49);
x_52 = l_Lean_Expr_isForall(x_51);
lean_dec(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
lean_dec(x_29);
x_53 = l_Lean_Compiler_LCNF_mkAuxParam(x_49, x_28, x_32, x_31, x_40, x_38, x_50);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_53, 1);
x_57 = lean_ctor_get(x_55, 0);
lean_inc(x_57);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_31);
lean_inc(x_32);
x_58 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_26, x_24, x_25, x_2, x_23, x_57, x_33, x_34, x_36, x_32, x_31, x_40, x_38, x_56);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_unsigned_to_nat(1u);
x_62 = lean_mk_empty_array_with_capacity(x_61);
x_63 = lean_array_push(x_62, x_55);
x_64 = lean_mk_string_unchecked("_jp", 3, 3);
x_65 = l_Lean_Name_mkStr1(x_64);
x_66 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_63, x_59, x_65, x_32, x_31, x_40, x_38, x_60);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_66, 1);
lean_inc(x_68);
lean_dec(x_66);
lean_inc(x_67);
x_69 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_69, 0, x_67);
lean_closure_set(x_69, 1, x_61);
x_70 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_42, x_69, x_32, x_31, x_40, x_38, x_68);
if (lean_obj_tag(x_70) == 0)
{
uint8_t x_71; 
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
lean_ctor_set_tag(x_53, 2);
lean_ctor_set(x_53, 1, x_72);
lean_ctor_set(x_53, 0, x_67);
if (lean_is_scalar(x_22)) {
 x_73 = lean_alloc_ctor(1, 1, 0);
} else {
 x_73 = x_22;
}
lean_ctor_set(x_73, 0, x_53);
lean_ctor_set(x_70, 0, x_73);
return x_70;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
lean_ctor_set_tag(x_53, 2);
lean_ctor_set(x_53, 1, x_74);
lean_ctor_set(x_53, 0, x_67);
if (lean_is_scalar(x_22)) {
 x_76 = lean_alloc_ctor(1, 1, 0);
} else {
 x_76 = x_22;
}
lean_ctor_set(x_76, 0, x_53);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_dec(x_67);
lean_free_object(x_53);
lean_dec(x_22);
x_78 = !lean_is_exclusive(x_70);
if (x_78 == 0)
{
return x_70;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_70, 0);
x_80 = lean_ctor_get(x_70, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_70);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
uint8_t x_82; 
lean_free_object(x_53);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_22);
x_82 = !lean_is_exclusive(x_66);
if (x_82 == 0)
{
return x_66;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_83 = lean_ctor_get(x_66, 0);
x_84 = lean_ctor_get(x_66, 1);
lean_inc(x_84);
lean_inc(x_83);
lean_dec(x_66);
x_85 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_85, 0, x_83);
lean_ctor_set(x_85, 1, x_84);
return x_85;
}
}
}
else
{
uint8_t x_86; 
lean_free_object(x_53);
lean_dec(x_55);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_22);
x_86 = !lean_is_exclusive(x_58);
if (x_86 == 0)
{
return x_58;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_58, 0);
x_88 = lean_ctor_get(x_58, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_58);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_90 = lean_ctor_get(x_53, 0);
x_91 = lean_ctor_get(x_53, 1);
lean_inc(x_91);
lean_inc(x_90);
lean_dec(x_53);
x_92 = lean_ctor_get(x_90, 0);
lean_inc(x_92);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_31);
lean_inc(x_32);
x_93 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_26, x_24, x_25, x_2, x_23, x_92, x_33, x_34, x_36, x_32, x_31, x_40, x_38, x_91);
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
x_98 = lean_array_push(x_97, x_90);
x_99 = lean_mk_string_unchecked("_jp", 3, 3);
x_100 = l_Lean_Name_mkStr1(x_99);
x_101 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_98, x_94, x_100, x_32, x_31, x_40, x_38, x_95);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
lean_inc(x_102);
x_104 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed), 8, 2);
lean_closure_set(x_104, 0, x_102);
lean_closure_set(x_104, 1, x_96);
x_105 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_42, x_104, x_32, x_31, x_40, x_38, x_103);
if (lean_obj_tag(x_105) == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; 
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
x_109 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_109, 0, x_102);
lean_ctor_set(x_109, 1, x_106);
if (lean_is_scalar(x_22)) {
 x_110 = lean_alloc_ctor(1, 1, 0);
} else {
 x_110 = x_22;
}
lean_ctor_set(x_110, 0, x_109);
if (lean_is_scalar(x_108)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_108;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_107);
return x_111;
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_102);
lean_dec(x_22);
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
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_22);
x_116 = lean_ctor_get(x_101, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_101, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_118 = x_101;
} else {
 lean_dec_ref(x_101);
 x_118 = lean_box(0);
}
if (lean_is_scalar(x_118)) {
 x_119 = lean_alloc_ctor(1, 2, 0);
} else {
 x_119 = x_118;
}
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_117);
return x_119;
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
lean_dec(x_90);
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_22);
x_120 = lean_ctor_get(x_93, 0);
lean_inc(x_120);
x_121 = lean_ctor_get(x_93, 1);
lean_inc(x_121);
if (lean_is_exclusive(x_93)) {
 lean_ctor_release(x_93, 0);
 lean_ctor_release(x_93, 1);
 x_122 = x_93;
} else {
 lean_dec_ref(x_93);
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
}
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_49);
x_124 = lean_mk_empty_array_with_capacity(x_29);
lean_dec(x_29);
x_125 = lean_mk_string_unchecked("_f", 2, 2);
x_126 = l_Lean_Name_mkStr1(x_125);
x_127 = l_Lean_Compiler_LCNF_mkAuxFunDecl(x_124, x_42, x_126, x_32, x_31, x_40, x_38, x_50);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_128 = lean_ctor_get(x_127, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_127, 1);
lean_inc(x_129);
lean_dec(x_127);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_31);
lean_inc(x_32);
x_130 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_128, x_32, x_31, x_40, x_38, x_129);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
x_132 = lean_ctor_get(x_130, 1);
lean_inc(x_132);
lean_dec(x_130);
x_133 = lean_ctor_get(x_131, 0);
lean_inc(x_133);
lean_inc(x_38);
lean_inc(x_40);
lean_inc(x_31);
lean_inc(x_32);
lean_inc(x_36);
lean_inc(x_34);
lean_inc(x_33);
x_134 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__0(x_26, x_24, x_25, x_2, x_23, x_133, x_33, x_34, x_36, x_32, x_31, x_40, x_38, x_132);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint8_t x_142; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_131);
x_138 = lean_unsigned_to_nat(1u);
x_139 = lean_mk_empty_array_with_capacity(x_138);
x_140 = lean_array_push(x_139, x_137);
x_141 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_140, x_135, x_33, x_34, x_36, x_32, x_31, x_40, x_38, x_136);
lean_dec(x_38);
lean_dec(x_40);
lean_dec(x_31);
lean_dec(x_32);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_140);
x_142 = !lean_is_exclusive(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_141, 0);
if (lean_is_scalar(x_22)) {
 x_144 = lean_alloc_ctor(1, 1, 0);
} else {
 x_144 = x_22;
}
lean_ctor_set(x_144, 0, x_143);
lean_ctor_set(x_141, 0, x_144);
return x_141;
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
x_145 = lean_ctor_get(x_141, 0);
x_146 = lean_ctor_get(x_141, 1);
lean_inc(x_146);
lean_inc(x_145);
lean_dec(x_141);
if (lean_is_scalar(x_22)) {
 x_147 = lean_alloc_ctor(1, 1, 0);
} else {
 x_147 = x_22;
}
lean_ctor_set(x_147, 0, x_145);
x_148 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_148, 0, x_147);
lean_ctor_set(x_148, 1, x_146);
return x_148;
}
}
else
{
uint8_t x_149; 
lean_dec(x_131);
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_22);
x_149 = !lean_is_exclusive(x_134);
if (x_149 == 0)
{
return x_134;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = lean_ctor_get(x_134, 0);
x_151 = lean_ctor_get(x_134, 1);
lean_inc(x_151);
lean_inc(x_150);
lean_dec(x_134);
x_152 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_152, 0, x_150);
lean_ctor_set(x_152, 1, x_151);
return x_152;
}
}
}
else
{
uint8_t x_153; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_153 = !lean_is_exclusive(x_130);
if (x_153 == 0)
{
return x_130;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_154 = lean_ctor_get(x_130, 0);
x_155 = lean_ctor_get(x_130, 1);
lean_inc(x_155);
lean_inc(x_154);
lean_dec(x_130);
x_156 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
return x_156;
}
}
}
else
{
uint8_t x_157; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_36);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_2);
x_157 = !lean_is_exclusive(x_127);
if (x_157 == 0)
{
return x_127;
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; 
x_158 = lean_ctor_get(x_127, 0);
x_159 = lean_ctor_get(x_127, 1);
lean_inc(x_159);
lean_inc(x_158);
lean_dec(x_127);
x_160 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
return x_160;
}
}
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; 
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_33);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_21);
lean_dec(x_2);
x_161 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_34, x_43);
lean_dec(x_34);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
x_163 = l_Lean_Compiler_LCNF_CompilerM_codeBind(x_42, x_37, x_32, x_31, x_40, x_38, x_162);
if (lean_obj_tag(x_163) == 0)
{
uint8_t x_164; 
x_164 = !lean_is_exclusive(x_163);
if (x_164 == 0)
{
lean_object* x_165; lean_object* x_166; 
x_165 = lean_ctor_get(x_163, 0);
if (lean_is_scalar(x_22)) {
 x_166 = lean_alloc_ctor(1, 1, 0);
} else {
 x_166 = x_22;
}
lean_ctor_set(x_166, 0, x_165);
lean_ctor_set(x_163, 0, x_166);
return x_163;
}
else
{
lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_167 = lean_ctor_get(x_163, 0);
x_168 = lean_ctor_get(x_163, 1);
lean_inc(x_168);
lean_inc(x_167);
lean_dec(x_163);
if (lean_is_scalar(x_22)) {
 x_169 = lean_alloc_ctor(1, 1, 0);
} else {
 x_169 = x_22;
}
lean_ctor_set(x_169, 0, x_167);
x_170 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_170, 0, x_169);
lean_ctor_set(x_170, 1, x_168);
return x_170;
}
}
else
{
uint8_t x_171; 
lean_dec(x_22);
x_171 = !lean_is_exclusive(x_163);
if (x_171 == 0)
{
return x_163;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_163, 0);
x_173 = lean_ctor_get(x_163, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_163);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
}
else
{
uint8_t x_175; 
lean_dec(x_40);
lean_dec(x_38);
lean_dec(x_37);
lean_dec(x_36);
lean_dec(x_35);
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_29);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_175 = !lean_is_exclusive(x_41);
if (x_175 == 0)
{
return x_41;
}
else
{
lean_object* x_176; lean_object* x_177; lean_object* x_178; 
x_176 = lean_ctor_get(x_41, 0);
x_177 = lean_ctor_get(x_41, 1);
lean_inc(x_177);
lean_inc(x_176);
lean_dec(x_41);
x_178 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_178, 0, x_176);
lean_ctor_set(x_178, 1, x_177);
return x_178;
}
}
}
block_259:
{
if (x_28 == 0)
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; 
x_188 = lean_ctor_get(x_21, 0);
lean_inc(x_188);
x_189 = lean_ctor_get(x_21, 1);
lean_inc(x_189);
x_190 = lean_unsigned_to_nat(0u);
lean_inc(x_26);
lean_inc(x_23);
x_191 = l_Array_toSubarray___redArg(x_23, x_190, x_26);
x_192 = l_Array_ofSubarray___redArg(x_191);
lean_dec(x_191);
lean_inc(x_192);
x_193 = l_Lean_Compiler_LCNF_Simp_betaReduce(x_188, x_189, x_192, x_28, x_180, x_181, x_182, x_183, x_184, x_185, x_186, x_187);
lean_dec(x_188);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; uint8_t x_197; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
lean_inc(x_182);
lean_inc(x_181);
lean_inc(x_180);
x_196 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__2), 10, 4);
lean_closure_set(x_196, 0, x_180);
lean_closure_set(x_196, 1, x_181);
lean_closure_set(x_196, 2, x_182);
lean_closure_set(x_196, 3, x_27);
x_197 = l_Lean_Compiler_LCNF_Code_isReturnOf(x_2, x_25);
if (x_197 == 0)
{
x_29 = x_190;
x_30 = x_195;
x_31 = x_184;
x_32 = x_183;
x_33 = x_180;
x_34 = x_181;
x_35 = x_192;
x_36 = x_182;
x_37 = x_196;
x_38 = x_186;
x_39 = x_194;
x_40 = x_185;
goto block_179;
}
else
{
uint8_t x_198; 
x_198 = lean_nat_dec_eq(x_24, x_26);
if (x_198 == 0)
{
x_29 = x_190;
x_30 = x_195;
x_31 = x_184;
x_32 = x_183;
x_33 = x_180;
x_34 = x_181;
x_35 = x_192;
x_36 = x_182;
x_37 = x_196;
x_38 = x_186;
x_39 = x_194;
x_40 = x_185;
goto block_179;
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
lean_dec(x_196);
lean_dec(x_192);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_199 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_181, x_195);
x_200 = lean_ctor_get(x_199, 1);
lean_inc(x_200);
lean_dec(x_199);
x_201 = l_Lean_Compiler_LCNF_Simp_simp(x_194, x_180, x_181, x_182, x_183, x_184, x_185, x_186, x_200);
if (lean_obj_tag(x_201) == 0)
{
uint8_t x_202; 
x_202 = !lean_is_exclusive(x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; 
x_203 = lean_ctor_get(x_201, 0);
x_204 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_204, 0, x_203);
lean_ctor_set(x_201, 0, x_204);
return x_201;
}
else
{
lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_205 = lean_ctor_get(x_201, 0);
x_206 = lean_ctor_get(x_201, 1);
lean_inc(x_206);
lean_inc(x_205);
lean_dec(x_201);
x_207 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_207, 0, x_205);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_206);
return x_208;
}
}
else
{
uint8_t x_209; 
x_209 = !lean_is_exclusive(x_201);
if (x_209 == 0)
{
return x_201;
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; 
x_210 = lean_ctor_get(x_201, 0);
x_211 = lean_ctor_get(x_201, 1);
lean_inc(x_211);
lean_inc(x_210);
lean_dec(x_201);
x_212 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_212, 0, x_210);
lean_ctor_set(x_212, 1, x_211);
return x_212;
}
}
}
}
}
else
{
uint8_t x_213; 
lean_dec(x_192);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
x_213 = !lean_is_exclusive(x_193);
if (x_213 == 0)
{
return x_193;
}
else
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; 
x_214 = lean_ctor_get(x_193, 0);
x_215 = lean_ctor_get(x_193, 1);
lean_inc(x_215);
lean_inc(x_214);
lean_dec(x_193);
x_216 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_216, 0, x_214);
lean_ctor_set(x_216, 1, x_215);
return x_216;
}
}
}
else
{
lean_object* x_217; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_22);
x_217 = l_Lean_Compiler_LCNF_Simp_specializePartialApp(x_21, x_180, x_181, x_182, x_183, x_184, x_185, x_186, x_187);
if (lean_obj_tag(x_217) == 0)
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; 
x_218 = lean_ctor_get(x_217, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_217, 1);
lean_inc(x_219);
lean_dec(x_217);
x_220 = lean_ctor_get(x_218, 0);
lean_inc(x_220);
x_221 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_25, x_220, x_181, x_184, x_185, x_186, x_219);
if (lean_obj_tag(x_221) == 0)
{
lean_object* x_222; lean_object* x_223; uint8_t x_224; 
x_222 = lean_ctor_get(x_221, 1);
lean_inc(x_222);
lean_dec(x_221);
x_223 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_181, x_222);
x_224 = !lean_is_exclusive(x_223);
if (x_224 == 0)
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; 
x_225 = lean_ctor_get(x_223, 1);
x_226 = lean_ctor_get(x_223, 0);
lean_dec(x_226);
lean_ctor_set_tag(x_223, 1);
lean_ctor_set(x_223, 1, x_2);
lean_ctor_set(x_223, 0, x_218);
x_227 = l_Lean_Compiler_LCNF_Simp_simp(x_223, x_180, x_181, x_182, x_183, x_184, x_185, x_186, x_225);
if (lean_obj_tag(x_227) == 0)
{
uint8_t x_228; 
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_227, 0);
x_230 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_230, 0, x_229);
lean_ctor_set(x_227, 0, x_230);
return x_227;
}
else
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_231 = lean_ctor_get(x_227, 0);
x_232 = lean_ctor_get(x_227, 1);
lean_inc(x_232);
lean_inc(x_231);
lean_dec(x_227);
x_233 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_233, 0, x_231);
x_234 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_232);
return x_234;
}
}
else
{
uint8_t x_235; 
x_235 = !lean_is_exclusive(x_227);
if (x_235 == 0)
{
return x_227;
}
else
{
lean_object* x_236; lean_object* x_237; lean_object* x_238; 
x_236 = lean_ctor_get(x_227, 0);
x_237 = lean_ctor_get(x_227, 1);
lean_inc(x_237);
lean_inc(x_236);
lean_dec(x_227);
x_238 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_238, 0, x_236);
lean_ctor_set(x_238, 1, x_237);
return x_238;
}
}
}
else
{
lean_object* x_239; lean_object* x_240; lean_object* x_241; 
x_239 = lean_ctor_get(x_223, 1);
lean_inc(x_239);
lean_dec(x_223);
x_240 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_240, 0, x_218);
lean_ctor_set(x_240, 1, x_2);
x_241 = l_Lean_Compiler_LCNF_Simp_simp(x_240, x_180, x_181, x_182, x_183, x_184, x_185, x_186, x_239);
if (lean_obj_tag(x_241) == 0)
{
lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_242 = lean_ctor_get(x_241, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_241, 1);
lean_inc(x_243);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_244 = x_241;
} else {
 lean_dec_ref(x_241);
 x_244 = lean_box(0);
}
x_245 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_245, 0, x_242);
if (lean_is_scalar(x_244)) {
 x_246 = lean_alloc_ctor(0, 2, 0);
} else {
 x_246 = x_244;
}
lean_ctor_set(x_246, 0, x_245);
lean_ctor_set(x_246, 1, x_243);
return x_246;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_247 = lean_ctor_get(x_241, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_241, 1);
lean_inc(x_248);
if (lean_is_exclusive(x_241)) {
 lean_ctor_release(x_241, 0);
 lean_ctor_release(x_241, 1);
 x_249 = x_241;
} else {
 lean_dec_ref(x_241);
 x_249 = lean_box(0);
}
if (lean_is_scalar(x_249)) {
 x_250 = lean_alloc_ctor(1, 2, 0);
} else {
 x_250 = x_249;
}
lean_ctor_set(x_250, 0, x_247);
lean_ctor_set(x_250, 1, x_248);
return x_250;
}
}
}
else
{
uint8_t x_251; 
lean_dec(x_218);
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_2);
x_251 = !lean_is_exclusive(x_221);
if (x_251 == 0)
{
return x_221;
}
else
{
lean_object* x_252; lean_object* x_253; lean_object* x_254; 
x_252 = lean_ctor_get(x_221, 0);
x_253 = lean_ctor_get(x_221, 1);
lean_inc(x_253);
lean_inc(x_252);
lean_dec(x_221);
x_254 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_254, 0, x_252);
lean_ctor_set(x_254, 1, x_253);
return x_254;
}
}
}
else
{
uint8_t x_255; 
lean_dec(x_186);
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_183);
lean_dec(x_182);
lean_dec(x_181);
lean_dec(x_180);
lean_dec(x_25);
lean_dec(x_2);
x_255 = !lean_is_exclusive(x_217);
if (x_255 == 0)
{
return x_217;
}
else
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; 
x_256 = lean_ctor_get(x_217, 0);
x_257 = lean_ctor_get(x_217, 1);
lean_inc(x_257);
lean_inc(x_256);
lean_dec(x_217);
x_258 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_258, 0, x_256);
lean_ctor_set(x_258, 1, x_257);
return x_258;
}
}
}
}
}
}
else
{
uint8_t x_276; 
lean_dec(x_11);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_276 = !lean_is_exclusive(x_12);
if (x_276 == 0)
{
return x_12;
}
else
{
lean_object* x_277; lean_object* x_278; lean_object* x_279; 
x_277 = lean_ctor_get(x_12, 0);
x_278 = lean_ctor_get(x_12, 1);
lean_inc(x_278);
lean_inc(x_277);
lean_dec(x_12);
x_279 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_279, 0, x_277);
lean_ctor_set(x_279, 1, x_278);
return x_279;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_6 = lean_st_ref_get(x_3, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_st_ref_get(x_3, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_2, 2);
lean_inc(x_12);
x_13 = lean_ctor_get(x_7, 0);
lean_inc(x_13);
lean_dec(x_7);
x_14 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_13, x_1, x_12);
lean_dec(x_13);
x_15 = lean_ctor_get(x_2, 3);
lean_inc(x_15);
x_16 = lean_ctor_get(x_10, 0);
lean_inc(x_16);
lean_dec(x_10);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normLetValueImp(x_16, x_15, x_1);
lean_dec(x_16);
x_18 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateLetDeclImp___redArg(x_2, x_14, x_17, x_4, x_11);
return x_18;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_1, x_2, x_4, x_7, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_8, x_2, x_1);
lean_dec(x_8);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_5, 0);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_inc(x_10);
lean_dec(x_5);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normArgsImp(x_12, x_2, x_1);
lean_dec(x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_1, x_2, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_7 = lean_array_uget(x_1, x_2);
x_8 = lean_ctor_get(x_7, 2);
lean_inc(x_8);
lean_dec(x_7);
x_9 = l_Lean_Compiler_LCNF_isInductiveWithNoCtors___redArg(x_8, x_4, x_5);
lean_dec(x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_unbox(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_10);
x_12 = lean_ctor_get(x_9, 1);
lean_inc(x_12);
lean_dec(x_9);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_5 = x_12;
goto _start;
}
else
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_9);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = lean_ctor_get(x_9, 0);
lean_dec(x_18);
return x_9;
}
else
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_10);
lean_ctor_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_5);
return x_22;
}
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_2, x_3, x_10, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_array_get_size(x_4);
x_14 = lean_nat_dec_lt(x_3, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_12);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_16 = lean_array_fget(x_4, x_3);
if (lean_obj_tag(x_16) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; lean_object* x_64; lean_object* x_65; uint8_t x_66; lean_object* x_67; uint8_t x_68; uint8_t x_70; lean_object* x_71; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
x_30 = lean_ctor_get(x_16, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_16, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_16, 2);
lean_inc(x_32);
x_64 = lean_ctor_get(x_2, 3);
x_65 = lean_ctor_get(x_2, 4);
x_66 = lean_nat_dec_eq(x_64, x_65);
x_73 = lean_unsigned_to_nat(0u);
x_74 = lean_array_get_size(x_31);
x_75 = lean_nat_dec_lt(x_73, x_74);
if (x_75 == 0)
{
lean_dec(x_74);
x_70 = x_66;
x_71 = x_12;
goto block_72;
}
else
{
if (x_75 == 0)
{
lean_dec(x_74);
x_70 = x_66;
x_71 = x_12;
goto block_72;
}
else
{
size_t x_76; size_t x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; uint8_t x_81; 
x_76 = lean_usize_of_nat(x_73);
x_77 = lean_usize_of_nat(x_74);
lean_dec(x_74);
x_78 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_31, x_76, x_77, x_11, x_12);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_unbox(x_79);
lean_dec(x_79);
x_70 = x_81;
x_71 = x_80;
goto block_72;
}
}
block_63:
{
if (x_34 == 0)
{
lean_object* x_35; 
lean_inc(x_7);
lean_inc(x_1);
x_35 = l_Lean_Compiler_LCNF_Simp_withDiscrCtorImp_updateCtx(x_1, x_30, x_31, x_7, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_35) == 0)
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
lean_inc(x_5);
x_38 = l_Lean_Compiler_LCNF_Simp_simp(x_32, x_5, x_6, x_36, x_8, x_9, x_10, x_11, x_37);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
lean_inc(x_16);
x_41 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_39);
x_17 = x_41;
x_18 = x_40;
goto block_29;
}
else
{
uint8_t x_42; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_42 = !lean_is_exclusive(x_38);
if (x_42 == 0)
{
return x_38;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_38, 0);
x_44 = lean_ctor_get(x_38, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_38);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
else
{
uint8_t x_46; 
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_46 = !lean_is_exclusive(x_35);
if (x_46 == 0)
{
return x_35;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_35, 0);
x_48 = lean_ctor_get(x_35, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_35);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; 
lean_dec(x_31);
lean_dec(x_30);
lean_inc(x_32);
x_50 = l_Lean_Compiler_LCNF_Code_inferType(x_32, x_8, x_9, x_10, x_11, x_33);
if (lean_obj_tag(x_50) == 0)
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
lean_dec(x_50);
x_53 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_32, x_9, x_52);
lean_dec(x_32);
x_54 = lean_ctor_get(x_53, 1);
lean_inc(x_54);
lean_dec(x_53);
x_55 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_6, x_54);
x_56 = lean_ctor_get(x_55, 1);
lean_inc(x_56);
lean_dec(x_55);
x_57 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_57, 0, x_51);
lean_inc(x_16);
x_58 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_57);
x_17 = x_58;
x_18 = x_56;
goto block_29;
}
else
{
uint8_t x_59; 
lean_dec(x_32);
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_50);
if (x_59 == 0)
{
return x_50;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_50, 0);
x_61 = lean_ctor_get(x_50, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_50);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
}
block_69:
{
if (x_66 == 0)
{
x_33 = x_67;
x_34 = x_66;
goto block_63;
}
else
{
x_33 = x_67;
x_34 = x_68;
goto block_63;
}
}
block_72:
{
if (lean_obj_tag(x_32) == 6)
{
x_67 = x_71;
x_68 = x_70;
goto block_69;
}
else
{
if (x_66 == 0)
{
x_33 = x_71;
x_34 = x_70;
goto block_63;
}
else
{
x_67 = x_71;
x_68 = x_70;
goto block_69;
}
}
}
}
else
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_16, 0);
lean_inc(x_82);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_83 = l_Lean_Compiler_LCNF_Simp_simp(x_82, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_83, 1);
lean_inc(x_85);
lean_dec(x_83);
lean_inc(x_16);
x_86 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_16, x_84);
x_17 = x_86;
x_18 = x_85;
goto block_29;
}
else
{
uint8_t x_87; 
lean_dec(x_16);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_83);
if (x_87 == 0)
{
return x_83;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_83, 0);
x_89 = lean_ctor_get(x_83, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_83);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
block_29:
{
size_t x_19; size_t x_20; uint8_t x_21; 
x_19 = lean_ptr_addr(x_16);
lean_dec(x_16);
x_20 = lean_ptr_addr(x_17);
x_21 = lean_usize_dec_eq(x_19, x_20);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_22 = lean_unsigned_to_nat(1u);
x_23 = lean_nat_add(x_3, x_22);
x_24 = lean_array_fset(x_4, x_3, x_17);
lean_dec(x_3);
x_3 = x_23;
x_4 = x_24;
x_12 = x_18;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_17);
x_26 = lean_unsigned_to_nat(1u);
x_27 = lean_nat_add(x_3, x_26);
lean_dec(x_3);
x_3 = x_27;
x_12 = x_18;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
x_14 = l_Lean_Compiler_LCNF_Simp_simp(x_1, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; uint8_t x_25; lean_object* x_30; lean_object* x_56; lean_object* x_57; lean_object* x_58; uint8_t x_59; 
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
x_56 = lean_ctor_get(x_4, 0);
lean_inc(x_56);
x_57 = l_Lean_Compiler_LCNF_Simp_isUsed(x_56, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_16);
lean_dec(x_56);
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_unbox(x_58);
lean_dec(x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; uint8_t x_62; 
lean_dec(x_17);
lean_dec(x_2);
x_60 = lean_ctor_get(x_57, 1);
lean_inc(x_60);
lean_dec(x_57);
x_61 = l_Lean_Compiler_LCNF_Simp_eraseFunDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_60);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_61, 0);
lean_dec(x_63);
lean_ctor_set(x_61, 0, x_15);
return x_61;
}
else
{
lean_object* x_64; lean_object* x_65; 
x_64 = lean_ctor_get(x_61, 1);
lean_inc(x_64);
lean_dec(x_61);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_15);
lean_ctor_set(x_65, 1, x_64);
return x_65;
}
}
else
{
if (x_3 == 0)
{
lean_object* x_66; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_66 = lean_ctor_get(x_57, 1);
lean_inc(x_66);
lean_dec(x_57);
x_30 = x_66;
goto block_55;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_57, 1);
lean_inc(x_67);
lean_dec(x_57);
lean_inc(x_4);
x_68 = l_Lean_Compiler_LCNF_Simp_markUsedFunDecl(x_4, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_67);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
x_69 = lean_ctor_get(x_68, 1);
lean_inc(x_69);
lean_dec(x_68);
x_30 = x_69;
goto block_55;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_2);
x_20 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_15);
if (lean_is_scalar(x_17)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_17;
}
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_18);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_15);
lean_dec(x_4);
if (lean_is_scalar(x_17)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_17;
}
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_18);
return x_22;
}
}
block_29:
{
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; 
lean_dec(x_2);
x_26 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_26, 0, x_4);
lean_ctor_set(x_26, 1, x_15);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_24);
return x_27;
}
else
{
lean_object* x_28; 
lean_dec(x_15);
lean_dec(x_4);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_2);
lean_ctor_set(x_28, 1, x_24);
return x_28;
}
}
block_55:
{
switch (lean_obj_tag(x_2)) {
case 1:
{
lean_object* x_31; lean_object* x_32; size_t x_33; size_t x_34; uint8_t x_35; 
x_31 = lean_ctor_get(x_2, 0);
lean_inc(x_31);
x_32 = lean_ctor_get(x_2, 1);
lean_inc(x_32);
x_33 = lean_ptr_addr(x_32);
lean_dec(x_32);
x_34 = lean_ptr_addr(x_15);
x_35 = lean_usize_dec_eq(x_33, x_34);
if (x_35 == 0)
{
lean_dec(x_31);
x_18 = x_30;
x_19 = x_35;
goto block_23;
}
else
{
size_t x_36; size_t x_37; uint8_t x_38; 
x_36 = lean_ptr_addr(x_31);
lean_dec(x_31);
x_37 = lean_ptr_addr(x_4);
x_38 = lean_usize_dec_eq(x_36, x_37);
x_18 = x_30;
x_19 = x_38;
goto block_23;
}
}
case 2:
{
lean_object* x_39; lean_object* x_40; size_t x_41; size_t x_42; uint8_t x_43; 
lean_dec(x_17);
x_39 = lean_ctor_get(x_2, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_2, 1);
lean_inc(x_40);
x_41 = lean_ptr_addr(x_40);
lean_dec(x_40);
x_42 = lean_ptr_addr(x_15);
x_43 = lean_usize_dec_eq(x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_39);
x_24 = x_30;
x_25 = x_43;
goto block_29;
}
else
{
size_t x_44; size_t x_45; uint8_t x_46; 
x_44 = lean_ptr_addr(x_39);
lean_dec(x_39);
x_45 = lean_ptr_addr(x_4);
x_46 = lean_usize_dec_eq(x_44, x_45);
x_24 = x_30;
x_25 = x_46;
goto block_29;
}
}
default: 
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_17);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_2);
x_47 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_48 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_49 = lean_unsigned_to_nat(305u);
x_50 = lean_unsigned_to_nat(9u);
x_51 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_52 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_47, x_48, x_49, x_50, x_51);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_47);
x_53 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_30);
return x_54;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_2);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_30; lean_object* x_31; lean_object* x_32; uint8_t x_33; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = lean_ctor_get(x_7, 3);
lean_inc(x_38);
x_39 = lean_ctor_get(x_7, 4);
lean_inc(x_39);
x_40 = lean_nat_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; lean_object* x_53; uint8_t x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; 
x_41 = lean_unsigned_to_nat(1u);
x_42 = lean_nat_add(x_38, x_41);
lean_dec(x_38);
x_43 = lean_ctor_get(x_7, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_7, 1);
lean_inc(x_44);
x_45 = lean_ctor_get(x_7, 2);
lean_inc(x_45);
x_46 = lean_ctor_get(x_7, 5);
lean_inc(x_46);
x_47 = lean_ctor_get(x_7, 6);
lean_inc(x_47);
x_48 = lean_ctor_get(x_7, 7);
lean_inc(x_48);
x_49 = lean_ctor_get(x_7, 8);
lean_inc(x_49);
x_50 = lean_ctor_get(x_7, 9);
lean_inc(x_50);
x_51 = lean_ctor_get(x_7, 10);
lean_inc(x_51);
x_52 = lean_ctor_get_uint8(x_7, sizeof(void*)*13);
x_53 = lean_ctor_get(x_7, 11);
lean_inc(x_53);
x_54 = lean_ctor_get_uint8(x_7, sizeof(void*)*13 + 1);
x_55 = lean_ctor_get(x_7, 12);
lean_inc(x_55);
x_56 = lean_alloc_ctor(0, 13, 2);
lean_ctor_set(x_56, 0, x_43);
lean_ctor_set(x_56, 1, x_44);
lean_ctor_set(x_56, 2, x_45);
lean_ctor_set(x_56, 3, x_42);
lean_ctor_set(x_56, 4, x_39);
lean_ctor_set(x_56, 5, x_46);
lean_ctor_set(x_56, 6, x_47);
lean_ctor_set(x_56, 7, x_48);
lean_ctor_set(x_56, 8, x_49);
lean_ctor_set(x_56, 9, x_50);
lean_ctor_set(x_56, 10, x_51);
lean_ctor_set(x_56, 11, x_53);
lean_ctor_set(x_56, 12, x_55);
lean_ctor_set_uint8(x_56, sizeof(void*)*13, x_52);
lean_ctor_set_uint8(x_56, sizeof(void*)*13 + 1, x_54);
x_57 = l_Lean_Compiler_LCNF_Simp_incVisited(x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_9);
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; uint8_t x_255; 
lean_dec(x_7);
x_105 = lean_ctor_get(x_1, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_1, 1);
lean_inc(x_106);
lean_inc(x_105);
x_225 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_40, x_105, x_3, x_6, x_58);
x_226 = lean_ctor_get(x_225, 0);
lean_inc(x_226);
x_227 = lean_ctor_get(x_225, 1);
lean_inc(x_227);
lean_dec(x_225);
x_255 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(x_105, x_226);
if (x_255 == 0)
{
goto block_254;
}
else
{
if (x_40 == 0)
{
x_228 = x_2;
x_229 = x_3;
x_230 = x_4;
x_231 = x_5;
x_232 = x_6;
x_233 = x_56;
x_234 = x_8;
x_235 = x_227;
goto block_251;
}
else
{
goto block_254;
}
}
block_224:
{
lean_object* x_116; 
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_107);
x_116 = l_Lean_Compiler_LCNF_Simp_ConstantFold_foldConstants(x_107, x_111, x_112, x_113, x_114, x_115);
if (lean_obj_tag(x_116) == 0)
{
lean_object* x_117; 
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
if (lean_obj_tag(x_117) == 0)
{
lean_object* x_118; lean_object* x_119; 
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_107);
x_119 = l_Lean_Compiler_LCNF_Simp_etaPolyApp_x3f(x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_118);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; 
x_120 = lean_ctor_get(x_119, 0);
lean_inc(x_120);
if (lean_obj_tag(x_120) == 0)
{
lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_121 = lean_ctor_get(x_119, 1);
lean_inc(x_121);
lean_dec(x_119);
x_122 = lean_ctor_get(x_107, 3);
lean_inc(x_122);
lean_inc(x_122);
x_123 = l_Lean_Compiler_LCNF_Simp_elimVar_x3f___redArg(x_122, x_121);
x_124 = lean_ctor_get(x_123, 0);
lean_inc(x_124);
if (lean_obj_tag(x_124) == 0)
{
lean_object* x_125; lean_object* x_126; 
x_125 = lean_ctor_get(x_123, 1);
lean_inc(x_125);
lean_dec(x_123);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_106);
lean_inc(x_107);
x_126 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f(x_107, x_106, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_125);
if (lean_obj_tag(x_126) == 0)
{
lean_object* x_127; 
x_127 = lean_ctor_get(x_126, 0);
lean_inc(x_127);
if (lean_obj_tag(x_127) == 0)
{
lean_object* x_128; lean_object* x_129; 
x_128 = lean_ctor_get(x_126, 1);
lean_inc(x_128);
lean_dec(x_126);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
x_129 = l_Lean_Compiler_LCNF_Simp_inlineProjInst_x3f(x_122, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_128);
if (lean_obj_tag(x_129) == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_129, 0);
lean_inc(x_130);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; 
x_131 = lean_ctor_get(x_129, 1);
lean_inc(x_131);
lean_dec(x_129);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
lean_inc(x_106);
x_132 = l_Lean_Compiler_LCNF_Simp_simp(x_106, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_131);
if (lean_obj_tag(x_132) == 0)
{
lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
lean_dec(x_132);
x_135 = lean_ctor_get(x_107, 0);
lean_inc(x_135);
x_136 = l_Lean_Compiler_LCNF_Simp_isUsed(x_135, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_134);
lean_dec(x_135);
x_137 = lean_ctor_get(x_136, 0);
lean_inc(x_137);
x_138 = lean_unbox(x_137);
lean_dec(x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; uint8_t x_141; 
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_139 = lean_ctor_get(x_136, 1);
lean_inc(x_139);
lean_dec(x_136);
x_140 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_139);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
x_141 = !lean_is_exclusive(x_140);
if (x_141 == 0)
{
lean_object* x_142; 
x_142 = lean_ctor_get(x_140, 0);
lean_dec(x_142);
lean_ctor_set(x_140, 0, x_133);
return x_140;
}
else
{
lean_object* x_143; lean_object* x_144; 
x_143 = lean_ctor_get(x_140, 1);
lean_inc(x_143);
lean_dec(x_140);
x_144 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_144, 0, x_133);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
else
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; size_t x_148; size_t x_149; uint8_t x_150; 
x_145 = lean_ctor_get(x_136, 1);
lean_inc(x_145);
lean_dec(x_136);
lean_inc(x_107);
x_146 = l_Lean_Compiler_LCNF_Simp_markUsedLetDecl(x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_145);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
lean_dec(x_146);
x_148 = lean_ptr_addr(x_106);
lean_dec(x_106);
x_149 = lean_ptr_addr(x_133);
x_150 = lean_usize_dec_eq(x_148, x_149);
if (x_150 == 0)
{
lean_dec(x_105);
x_30 = x_147;
x_31 = x_133;
x_32 = x_107;
x_33 = x_40;
goto block_37;
}
else
{
size_t x_151; size_t x_152; uint8_t x_153; 
x_151 = lean_ptr_addr(x_105);
lean_dec(x_105);
x_152 = lean_ptr_addr(x_107);
x_153 = lean_usize_dec_eq(x_151, x_152);
x_30 = x_147;
x_31 = x_133;
x_32 = x_107;
x_33 = x_153;
goto block_37;
}
}
}
else
{
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
return x_132;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_105);
lean_dec(x_1);
x_154 = lean_ctor_get(x_130, 0);
lean_inc(x_154);
lean_dec(x_130);
x_155 = lean_ctor_get(x_129, 1);
lean_inc(x_155);
lean_dec(x_129);
x_156 = lean_ctor_get(x_154, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_154, 1);
lean_inc(x_157);
lean_dec(x_154);
x_158 = lean_ctor_get(x_107, 0);
lean_inc(x_158);
x_159 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_158, x_157, x_109, x_112, x_113, x_114, x_155);
if (lean_obj_tag(x_159) == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; 
x_160 = lean_ctor_get(x_159, 1);
lean_inc(x_160);
lean_dec(x_159);
x_161 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_160);
lean_dec(x_107);
x_162 = lean_ctor_get(x_161, 1);
lean_inc(x_162);
lean_dec(x_161);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
x_163 = l_Lean_Compiler_LCNF_Simp_simp(x_106, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_162);
if (lean_obj_tag(x_163) == 0)
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
x_165 = lean_ctor_get(x_163, 1);
lean_inc(x_165);
lean_dec(x_163);
x_166 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_156, x_164, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_165);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_156);
return x_166;
}
else
{
lean_dec(x_156);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
return x_163;
}
}
else
{
uint8_t x_167; 
lean_dec(x_156);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
x_167 = !lean_is_exclusive(x_159);
if (x_167 == 0)
{
return x_159;
}
else
{
lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_168 = lean_ctor_get(x_159, 0);
x_169 = lean_ctor_get(x_159, 1);
lean_inc(x_169);
lean_inc(x_168);
lean_dec(x_159);
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
uint8_t x_171; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_171 = !lean_is_exclusive(x_129);
if (x_171 == 0)
{
return x_129;
}
else
{
lean_object* x_172; lean_object* x_173; lean_object* x_174; 
x_172 = lean_ctor_get(x_129, 0);
x_173 = lean_ctor_get(x_129, 1);
lean_inc(x_173);
lean_inc(x_172);
lean_dec(x_129);
x_174 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_174, 0, x_172);
lean_ctor_set(x_174, 1, x_173);
return x_174;
}
}
}
else
{
lean_object* x_175; lean_object* x_176; lean_object* x_177; uint8_t x_178; 
lean_dec(x_122);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_175 = lean_ctor_get(x_126, 1);
lean_inc(x_175);
lean_dec(x_126);
x_176 = lean_ctor_get(x_127, 0);
lean_inc(x_176);
lean_dec(x_127);
x_177 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_175);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
x_178 = !lean_is_exclusive(x_177);
if (x_178 == 0)
{
lean_object* x_179; 
x_179 = lean_ctor_get(x_177, 0);
lean_dec(x_179);
lean_ctor_set(x_177, 0, x_176);
return x_177;
}
else
{
lean_object* x_180; lean_object* x_181; 
x_180 = lean_ctor_get(x_177, 1);
lean_inc(x_180);
lean_dec(x_177);
x_181 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_181, 0, x_176);
lean_ctor_set(x_181, 1, x_180);
return x_181;
}
}
}
else
{
uint8_t x_182; 
lean_dec(x_122);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_182 = !lean_is_exclusive(x_126);
if (x_182 == 0)
{
return x_126;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_183 = lean_ctor_get(x_126, 0);
x_184 = lean_ctor_get(x_126, 1);
lean_inc(x_184);
lean_inc(x_183);
lean_dec(x_126);
x_185 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_185, 0, x_183);
lean_ctor_set(x_185, 1, x_184);
return x_185;
}
}
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_122);
lean_dec(x_105);
lean_dec(x_1);
x_186 = lean_ctor_get(x_123, 1);
lean_inc(x_186);
lean_dec(x_123);
x_187 = lean_ctor_get(x_124, 0);
lean_inc(x_187);
lean_dec(x_124);
x_188 = lean_ctor_get(x_107, 0);
lean_inc(x_188);
x_189 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_188, x_187, x_109, x_112, x_113, x_114, x_186);
if (lean_obj_tag(x_189) == 0)
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; 
x_190 = lean_ctor_get(x_189, 1);
lean_inc(x_190);
lean_dec(x_189);
x_191 = l_Lean_Compiler_LCNF_Simp_eraseLetDecl(x_107, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_190);
lean_dec(x_107);
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
x_1 = x_106;
x_2 = x_108;
x_3 = x_109;
x_4 = x_110;
x_5 = x_111;
x_6 = x_112;
x_7 = x_113;
x_8 = x_114;
x_9 = x_192;
goto _start;
}
else
{
uint8_t x_194; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
x_194 = !lean_is_exclusive(x_189);
if (x_194 == 0)
{
return x_189;
}
else
{
lean_object* x_195; lean_object* x_196; lean_object* x_197; 
x_195 = lean_ctor_get(x_189, 0);
x_196 = lean_ctor_get(x_189, 1);
lean_inc(x_196);
lean_inc(x_195);
lean_dec(x_189);
x_197 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_197, 0, x_195);
lean_ctor_set(x_197, 1, x_196);
return x_197;
}
}
}
}
else
{
uint8_t x_198; 
lean_dec(x_107);
lean_dec(x_105);
x_198 = !lean_is_exclusive(x_1);
if (x_198 == 0)
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; 
x_199 = lean_ctor_get(x_1, 1);
lean_dec(x_199);
x_200 = lean_ctor_get(x_1, 0);
lean_dec(x_200);
x_201 = lean_ctor_get(x_119, 1);
lean_inc(x_201);
lean_dec(x_119);
x_202 = lean_ctor_get(x_120, 0);
lean_inc(x_202);
lean_dec(x_120);
lean_ctor_set_tag(x_1, 1);
lean_ctor_set(x_1, 0, x_202);
x_2 = x_108;
x_3 = x_109;
x_4 = x_110;
x_5 = x_111;
x_6 = x_112;
x_7 = x_113;
x_8 = x_114;
x_9 = x_201;
goto _start;
}
else
{
lean_object* x_204; lean_object* x_205; lean_object* x_206; 
lean_dec(x_1);
x_204 = lean_ctor_get(x_119, 1);
lean_inc(x_204);
lean_dec(x_119);
x_205 = lean_ctor_get(x_120, 0);
lean_inc(x_205);
lean_dec(x_120);
x_206 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_206, 0, x_205);
lean_ctor_set(x_206, 1, x_106);
x_1 = x_206;
x_2 = x_108;
x_3 = x_109;
x_4 = x_110;
x_5 = x_111;
x_6 = x_112;
x_7 = x_113;
x_8 = x_114;
x_9 = x_204;
goto _start;
}
}
}
else
{
uint8_t x_208; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_208 = !lean_is_exclusive(x_119);
if (x_208 == 0)
{
return x_119;
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; 
x_209 = lean_ctor_get(x_119, 0);
x_210 = lean_ctor_get(x_119, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_119);
x_211 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_211, 0, x_209);
lean_ctor_set(x_211, 1, x_210);
return x_211;
}
}
}
else
{
lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; 
lean_dec(x_107);
lean_dec(x_105);
lean_dec(x_1);
x_212 = lean_ctor_get(x_116, 1);
lean_inc(x_212);
lean_dec(x_116);
x_213 = lean_ctor_get(x_117, 0);
lean_inc(x_213);
lean_dec(x_117);
x_214 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_109, x_212);
x_215 = lean_ctor_get(x_214, 1);
lean_inc(x_215);
lean_dec(x_214);
lean_inc(x_114);
lean_inc(x_113);
lean_inc(x_112);
lean_inc(x_111);
lean_inc(x_110);
lean_inc(x_109);
lean_inc(x_108);
x_216 = l_Lean_Compiler_LCNF_Simp_simp(x_106, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_215);
if (lean_obj_tag(x_216) == 0)
{
lean_object* x_217; lean_object* x_218; lean_object* x_219; 
x_217 = lean_ctor_get(x_216, 0);
lean_inc(x_217);
x_218 = lean_ctor_get(x_216, 1);
lean_inc(x_218);
lean_dec(x_216);
x_219 = l_Lean_Compiler_LCNF_Simp_attachCodeDecls(x_213, x_217, x_108, x_109, x_110, x_111, x_112, x_113, x_114, x_218);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_213);
return x_219;
}
else
{
lean_dec(x_213);
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
return x_216;
}
}
}
else
{
uint8_t x_220; 
lean_dec(x_114);
lean_dec(x_113);
lean_dec(x_112);
lean_dec(x_111);
lean_dec(x_110);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_107);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_220 = !lean_is_exclusive(x_116);
if (x_220 == 0)
{
return x_116;
}
else
{
lean_object* x_221; lean_object* x_222; lean_object* x_223; 
x_221 = lean_ctor_get(x_116, 0);
x_222 = lean_ctor_get(x_116, 1);
lean_inc(x_222);
lean_inc(x_221);
lean_dec(x_116);
x_223 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
return x_223;
}
}
}
block_251:
{
lean_object* x_236; lean_object* x_237; 
x_236 = lean_ctor_get(x_226, 3);
lean_inc(x_236);
lean_inc(x_234);
lean_inc(x_233);
lean_inc(x_232);
lean_inc(x_231);
lean_inc(x_230);
x_237 = l_Lean_Compiler_LCNF_Simp_simpValue_x3f(x_236, x_228, x_229, x_230, x_231, x_232, x_233, x_234, x_235);
if (lean_obj_tag(x_237) == 0)
{
lean_object* x_238; 
x_238 = lean_ctor_get(x_237, 0);
lean_inc(x_238);
if (lean_obj_tag(x_238) == 0)
{
lean_object* x_239; 
x_239 = lean_ctor_get(x_237, 1);
lean_inc(x_239);
lean_dec(x_237);
x_107 = x_226;
x_108 = x_228;
x_109 = x_229;
x_110 = x_230;
x_111 = x_231;
x_112 = x_232;
x_113 = x_233;
x_114 = x_234;
x_115 = x_239;
goto block_224;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
lean_dec(x_237);
x_241 = lean_ctor_get(x_238, 0);
lean_inc(x_241);
lean_dec(x_238);
x_242 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_229, x_240);
x_243 = lean_ctor_get(x_242, 1);
lean_inc(x_243);
lean_dec(x_242);
x_244 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_226, x_241, x_231, x_232, x_233, x_234, x_243);
x_245 = lean_ctor_get(x_244, 0);
lean_inc(x_245);
x_246 = lean_ctor_get(x_244, 1);
lean_inc(x_246);
lean_dec(x_244);
x_107 = x_245;
x_108 = x_228;
x_109 = x_229;
x_110 = x_230;
x_111 = x_231;
x_112 = x_232;
x_113 = x_233;
x_114 = x_234;
x_115 = x_246;
goto block_224;
}
}
else
{
uint8_t x_247; 
lean_dec(x_234);
lean_dec(x_233);
lean_dec(x_232);
lean_dec(x_231);
lean_dec(x_230);
lean_dec(x_229);
lean_dec(x_228);
lean_dec(x_226);
lean_dec(x_106);
lean_dec(x_105);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_237);
if (x_247 == 0)
{
return x_237;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_237, 0);
x_249 = lean_ctor_get(x_237, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_237);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
block_254:
{
lean_object* x_252; lean_object* x_253; 
x_252 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_227);
x_253 = lean_ctor_get(x_252, 1);
lean_inc(x_253);
lean_dec(x_252);
x_228 = x_2;
x_229 = x_3;
x_230 = x_4;
x_231 = x_5;
x_232 = x_6;
x_233 = x_56;
x_234 = x_8;
x_235 = x_253;
goto block_251;
}
}
case 3:
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
lean_dec(x_7);
x_256 = lean_ctor_get(x_1, 0);
lean_inc(x_256);
x_257 = lean_ctor_get(x_1, 1);
lean_inc(x_257);
x_258 = lean_st_ref_get(x_3, x_58);
x_259 = lean_ctor_get(x_258, 0);
lean_inc(x_259);
x_260 = lean_ctor_get(x_258, 1);
lean_inc(x_260);
lean_dec(x_258);
x_261 = lean_ctor_get(x_259, 0);
lean_inc(x_261);
lean_dec(x_259);
lean_inc(x_256);
x_262 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_261, x_256, x_40);
lean_dec(x_261);
if (lean_obj_tag(x_262) == 0)
{
lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; uint8_t x_269; lean_object* x_278; lean_object* x_284; 
x_263 = lean_ctor_get(x_262, 0);
lean_inc(x_263);
lean_dec(x_262);
lean_inc(x_257);
x_264 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_40, x_257, x_3, x_260);
x_265 = lean_ctor_get(x_264, 0);
lean_inc(x_265);
x_266 = lean_ctor_get(x_264, 1);
lean_inc(x_266);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_267 = x_264;
} else {
 lean_dec_ref(x_264);
 x_267 = lean_box(0);
}
lean_inc(x_265);
x_284 = l_Lean_Compiler_LCNF_Simp_inlineJp_x3f(x_263, x_265, x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_266);
if (lean_obj_tag(x_284) == 0)
{
lean_object* x_285; 
x_285 = lean_ctor_get(x_284, 0);
lean_inc(x_285);
if (lean_obj_tag(x_285) == 0)
{
lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; uint8_t x_291; 
x_286 = lean_ctor_get(x_284, 1);
lean_inc(x_286);
lean_dec(x_284);
lean_inc(x_263);
x_287 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_263, x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_286);
lean_dec(x_8);
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_288 = lean_ctor_get(x_287, 1);
lean_inc(x_288);
lean_dec(x_287);
x_289 = lean_unsigned_to_nat(0u);
x_290 = lean_array_get_size(x_265);
x_291 = lean_nat_dec_lt(x_289, x_290);
if (x_291 == 0)
{
lean_dec(x_290);
lean_dec(x_3);
x_278 = x_288;
goto block_283;
}
else
{
uint8_t x_292; 
x_292 = lean_nat_dec_le(x_290, x_290);
if (x_292 == 0)
{
lean_dec(x_290);
lean_dec(x_3);
x_278 = x_288;
goto block_283;
}
else
{
lean_object* x_293; size_t x_294; size_t x_295; lean_object* x_296; lean_object* x_297; 
x_293 = lean_box(0);
x_294 = lean_usize_of_nat(x_289);
x_295 = lean_usize_of_nat(x_290);
lean_dec(x_290);
x_296 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Simp_markUsedLetValue_spec__0___redArg(x_265, x_294, x_295, x_293, x_3, x_288);
lean_dec(x_3);
x_297 = lean_ctor_get(x_296, 1);
lean_inc(x_297);
lean_dec(x_296);
x_278 = x_297;
goto block_283;
}
}
}
else
{
lean_object* x_298; lean_object* x_299; 
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_1);
x_298 = lean_ctor_get(x_284, 1);
lean_inc(x_298);
lean_dec(x_284);
x_299 = lean_ctor_get(x_285, 0);
lean_inc(x_299);
lean_dec(x_285);
x_1 = x_299;
x_7 = x_56;
x_9 = x_298;
goto _start;
}
}
else
{
uint8_t x_301; 
lean_dec(x_267);
lean_dec(x_265);
lean_dec(x_263);
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_301 = !lean_is_exclusive(x_284);
if (x_301 == 0)
{
return x_284;
}
else
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; 
x_302 = lean_ctor_get(x_284, 0);
x_303 = lean_ctor_get(x_284, 1);
lean_inc(x_303);
lean_inc(x_302);
lean_dec(x_284);
x_304 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_304, 0, x_302);
lean_ctor_set(x_304, 1, x_303);
return x_304;
}
}
block_277:
{
if (x_269 == 0)
{
uint8_t x_270; 
x_270 = !lean_is_exclusive(x_1);
if (x_270 == 0)
{
lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_271 = lean_ctor_get(x_1, 1);
lean_dec(x_271);
x_272 = lean_ctor_get(x_1, 0);
lean_dec(x_272);
lean_ctor_set(x_1, 1, x_265);
lean_ctor_set(x_1, 0, x_263);
if (lean_is_scalar(x_267)) {
 x_273 = lean_alloc_ctor(0, 2, 0);
} else {
 x_273 = x_267;
}
lean_ctor_set(x_273, 0, x_1);
lean_ctor_set(x_273, 1, x_268);
return x_273;
}
else
{
lean_object* x_274; lean_object* x_275; 
lean_dec(x_1);
x_274 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_274, 0, x_263);
lean_ctor_set(x_274, 1, x_265);
if (lean_is_scalar(x_267)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_267;
}
lean_ctor_set(x_275, 0, x_274);
lean_ctor_set(x_275, 1, x_268);
return x_275;
}
}
else
{
lean_object* x_276; 
lean_dec(x_265);
lean_dec(x_263);
if (lean_is_scalar(x_267)) {
 x_276 = lean_alloc_ctor(0, 2, 0);
} else {
 x_276 = x_267;
}
lean_ctor_set(x_276, 0, x_1);
lean_ctor_set(x_276, 1, x_268);
return x_276;
}
}
block_283:
{
uint8_t x_279; 
x_279 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_256, x_263);
lean_dec(x_256);
if (x_279 == 0)
{
lean_dec(x_257);
x_268 = x_278;
x_269 = x_40;
goto block_277;
}
else
{
size_t x_280; size_t x_281; uint8_t x_282; 
x_280 = lean_ptr_addr(x_257);
lean_dec(x_257);
x_281 = lean_ptr_addr(x_265);
x_282 = lean_usize_dec_eq(x_280, x_281);
x_268 = x_278;
x_269 = x_282;
goto block_277;
}
}
}
else
{
lean_object* x_305; 
lean_dec(x_257);
lean_dec(x_256);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_305 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_56, x_8, x_260);
lean_dec(x_8);
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
return x_305;
}
}
case 4:
{
lean_object* x_306; lean_object* x_307; 
x_306 = lean_ctor_get(x_1, 0);
lean_inc(x_306);
lean_inc(x_8);
lean_inc(x_56);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_306);
x_307 = l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(x_306, x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_58);
if (lean_obj_tag(x_307) == 0)
{
lean_object* x_308; 
x_308 = lean_ctor_get(x_307, 0);
lean_inc(x_308);
if (lean_obj_tag(x_308) == 0)
{
lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; 
x_309 = lean_ctor_get(x_307, 1);
lean_inc(x_309);
lean_dec(x_307);
x_310 = lean_st_ref_get(x_3, x_309);
x_311 = lean_ctor_get(x_310, 0);
lean_inc(x_311);
x_312 = lean_ctor_get(x_310, 1);
lean_inc(x_312);
lean_dec(x_310);
x_313 = lean_ctor_get(x_306, 2);
lean_inc(x_313);
x_314 = lean_ctor_get(x_311, 0);
lean_inc(x_314);
lean_dec(x_311);
lean_inc(x_313);
x_315 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_314, x_313, x_40);
lean_dec(x_314);
if (lean_obj_tag(x_315) == 0)
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; 
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_is_exclusive(x_315)) {
 lean_ctor_release(x_315, 0);
 x_317 = x_315;
} else {
 lean_dec_ref(x_315);
 x_317 = lean_box(0);
}
x_318 = lean_st_ref_get(x_3, x_312);
x_319 = lean_ctor_get(x_318, 0);
lean_inc(x_319);
x_320 = lean_ctor_get(x_318, 1);
lean_inc(x_320);
lean_dec(x_318);
lean_inc(x_316);
x_321 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_316, x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_320);
x_322 = lean_ctor_get(x_321, 1);
lean_inc(x_322);
lean_dec(x_321);
x_323 = lean_ctor_get(x_306, 3);
lean_inc(x_323);
x_324 = lean_unsigned_to_nat(0u);
lean_inc(x_8);
lean_inc(x_56);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_323);
lean_inc(x_316);
x_325 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_316, x_7, x_324, x_323, x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_322);
lean_dec(x_7);
if (lean_obj_tag(x_325) == 0)
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; lean_object* x_329; 
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
x_329 = l_Lean_Compiler_LCNF_Simp_addDefaultAlt(x_326, x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_327);
if (lean_obj_tag(x_329) == 0)
{
lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; uint8_t x_343; lean_object* x_358; uint8_t x_359; 
x_330 = lean_ctor_get(x_329, 0);
lean_inc(x_330);
x_331 = lean_ctor_get(x_329, 1);
lean_inc(x_331);
if (lean_is_exclusive(x_329)) {
 lean_ctor_release(x_329, 0);
 lean_ctor_release(x_329, 1);
 x_332 = x_329;
} else {
 lean_dec_ref(x_329);
 x_332 = lean_box(0);
}
x_333 = l_Lean_Compiler_LCNF_instInhabitedCode;
x_334 = l_Lean_Compiler_LCNF_instInhabitedAltCore(lean_box(0), x_333);
x_335 = lean_ctor_get(x_306, 1);
lean_inc(x_335);
x_336 = lean_ctor_get(x_319, 0);
lean_inc(x_336);
lean_dec(x_319);
lean_inc(x_335);
x_337 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_336, x_40, x_335);
lean_dec(x_336);
x_358 = lean_array_get_size(x_330);
x_359 = lean_nat_dec_eq(x_358, x_41);
lean_dec(x_358);
if (x_359 == 0)
{
x_343 = x_40;
goto block_357;
}
else
{
lean_object* x_360; 
lean_inc(x_334);
x_360 = lean_array_get(x_334, x_330, x_324);
if (lean_obj_tag(x_360) == 0)
{
lean_dec(x_360);
x_343 = x_40;
goto block_357;
}
else
{
lean_dec(x_360);
x_343 = x_359;
goto block_357;
}
}
block_342:
{
lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_338 = lean_ctor_get(x_306, 0);
lean_inc(x_338);
lean_dec(x_306);
x_339 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_339, 0, x_338);
lean_ctor_set(x_339, 1, x_337);
lean_ctor_set(x_339, 2, x_316);
lean_ctor_set(x_339, 3, x_330);
if (lean_is_scalar(x_317)) {
 x_340 = lean_alloc_ctor(4, 1, 0);
} else {
 x_340 = x_317;
 lean_ctor_set_tag(x_340, 4);
}
lean_ctor_set(x_340, 0, x_339);
if (lean_is_scalar(x_332)) {
 x_341 = lean_alloc_ctor(0, 2, 0);
} else {
 x_341 = x_332;
}
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_331);
return x_341;
}
block_357:
{
if (x_343 == 0)
{
size_t x_344; size_t x_345; uint8_t x_346; 
lean_dec(x_334);
x_344 = lean_ptr_addr(x_323);
lean_dec(x_323);
x_345 = lean_ptr_addr(x_330);
x_346 = lean_usize_dec_eq(x_344, x_345);
if (x_346 == 0)
{
lean_dec(x_335);
lean_dec(x_328);
lean_dec(x_313);
lean_dec(x_1);
goto block_342;
}
else
{
size_t x_347; size_t x_348; uint8_t x_349; 
x_347 = lean_ptr_addr(x_335);
lean_dec(x_335);
x_348 = lean_ptr_addr(x_337);
x_349 = lean_usize_dec_eq(x_347, x_348);
if (x_349 == 0)
{
lean_dec(x_328);
lean_dec(x_313);
lean_dec(x_1);
goto block_342;
}
else
{
uint8_t x_350; 
x_350 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_313, x_316);
lean_dec(x_313);
if (x_350 == 0)
{
lean_dec(x_328);
lean_dec(x_1);
goto block_342;
}
else
{
lean_object* x_351; 
lean_dec(x_337);
lean_dec(x_332);
lean_dec(x_330);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_306);
if (lean_is_scalar(x_328)) {
 x_351 = lean_alloc_ctor(0, 2, 0);
} else {
 x_351 = x_328;
}
lean_ctor_set(x_351, 0, x_1);
lean_ctor_set(x_351, 1, x_331);
return x_351;
}
}
}
}
else
{
lean_object* x_352; 
lean_dec(x_337);
lean_dec(x_335);
lean_dec(x_332);
lean_dec(x_323);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_313);
lean_dec(x_306);
lean_dec(x_1);
x_352 = lean_array_get(x_334, x_330, x_324);
lean_dec(x_330);
if (lean_obj_tag(x_352) == 0)
{
lean_object* x_353; lean_object* x_354; 
x_353 = lean_ctor_get(x_352, 2);
lean_inc(x_353);
lean_dec(x_352);
if (lean_is_scalar(x_328)) {
 x_354 = lean_alloc_ctor(0, 2, 0);
} else {
 x_354 = x_328;
}
lean_ctor_set(x_354, 0, x_353);
lean_ctor_set(x_354, 1, x_331);
return x_354;
}
else
{
lean_object* x_355; lean_object* x_356; 
x_355 = lean_ctor_get(x_352, 0);
lean_inc(x_355);
lean_dec(x_352);
if (lean_is_scalar(x_328)) {
 x_356 = lean_alloc_ctor(0, 2, 0);
} else {
 x_356 = x_328;
}
lean_ctor_set(x_356, 0, x_355);
lean_ctor_set(x_356, 1, x_331);
return x_356;
}
}
}
}
else
{
uint8_t x_361; 
lean_dec(x_328);
lean_dec(x_323);
lean_dec(x_319);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_313);
lean_dec(x_306);
lean_dec(x_1);
x_361 = !lean_is_exclusive(x_329);
if (x_361 == 0)
{
return x_329;
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_329, 0);
x_363 = lean_ctor_get(x_329, 1);
lean_inc(x_363);
lean_inc(x_362);
lean_dec(x_329);
x_364 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_364, 0, x_362);
lean_ctor_set(x_364, 1, x_363);
return x_364;
}
}
}
else
{
uint8_t x_365; 
lean_dec(x_323);
lean_dec(x_319);
lean_dec(x_317);
lean_dec(x_316);
lean_dec(x_313);
lean_dec(x_306);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_365 = !lean_is_exclusive(x_325);
if (x_365 == 0)
{
return x_325;
}
else
{
lean_object* x_366; lean_object* x_367; lean_object* x_368; 
x_366 = lean_ctor_get(x_325, 0);
x_367 = lean_ctor_get(x_325, 1);
lean_inc(x_367);
lean_inc(x_366);
lean_dec(x_325);
x_368 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_368, 0, x_366);
lean_ctor_set(x_368, 1, x_367);
return x_368;
}
}
}
else
{
lean_object* x_369; 
lean_dec(x_313);
lean_dec(x_306);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_369 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_56, x_8, x_312);
lean_dec(x_8);
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
return x_369;
}
}
else
{
uint8_t x_370; 
lean_dec(x_306);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_370 = !lean_is_exclusive(x_307);
if (x_370 == 0)
{
lean_object* x_371; lean_object* x_372; 
x_371 = lean_ctor_get(x_307, 0);
lean_dec(x_371);
x_372 = lean_ctor_get(x_308, 0);
lean_inc(x_372);
lean_dec(x_308);
lean_ctor_set(x_307, 0, x_372);
return x_307;
}
else
{
lean_object* x_373; lean_object* x_374; lean_object* x_375; 
x_373 = lean_ctor_get(x_307, 1);
lean_inc(x_373);
lean_dec(x_307);
x_374 = lean_ctor_get(x_308, 0);
lean_inc(x_374);
lean_dec(x_308);
x_375 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_373);
return x_375;
}
}
}
else
{
uint8_t x_376; 
lean_dec(x_306);
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_376 = !lean_is_exclusive(x_307);
if (x_376 == 0)
{
return x_307;
}
else
{
lean_object* x_377; lean_object* x_378; lean_object* x_379; 
x_377 = lean_ctor_get(x_307, 0);
x_378 = lean_ctor_get(x_307, 1);
lean_inc(x_378);
lean_inc(x_377);
lean_dec(x_307);
x_379 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_379, 0, x_377);
lean_ctor_set(x_379, 1, x_378);
return x_379;
}
}
}
case 5:
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; lean_object* x_385; 
lean_dec(x_7);
x_380 = lean_ctor_get(x_1, 0);
lean_inc(x_380);
x_381 = lean_st_ref_get(x_3, x_58);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
x_383 = lean_ctor_get(x_381, 1);
lean_inc(x_383);
lean_dec(x_381);
x_384 = lean_ctor_get(x_382, 0);
lean_inc(x_384);
lean_dec(x_382);
lean_inc(x_380);
x_385 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_384, x_380, x_40);
lean_dec(x_384);
if (lean_obj_tag(x_385) == 0)
{
lean_object* x_386; lean_object* x_387; uint8_t x_388; 
x_386 = lean_ctor_get(x_385, 0);
lean_inc(x_386);
lean_dec(x_385);
lean_inc(x_386);
x_387 = l_Lean_Compiler_LCNF_Simp_markUsedFVar(x_386, x_2, x_3, x_4, x_5, x_6, x_56, x_8, x_383);
lean_dec(x_8);
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_388 = !lean_is_exclusive(x_387);
if (x_388 == 0)
{
lean_object* x_389; uint8_t x_390; 
x_389 = lean_ctor_get(x_387, 0);
lean_dec(x_389);
x_390 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_380, x_386);
lean_dec(x_380);
if (x_390 == 0)
{
uint8_t x_391; 
x_391 = !lean_is_exclusive(x_1);
if (x_391 == 0)
{
lean_object* x_392; 
x_392 = lean_ctor_get(x_1, 0);
lean_dec(x_392);
lean_ctor_set(x_1, 0, x_386);
lean_ctor_set(x_387, 0, x_1);
return x_387;
}
else
{
lean_object* x_393; 
lean_dec(x_1);
x_393 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_393, 0, x_386);
lean_ctor_set(x_387, 0, x_393);
return x_387;
}
}
else
{
lean_dec(x_386);
lean_ctor_set(x_387, 0, x_1);
return x_387;
}
}
else
{
lean_object* x_394; uint8_t x_395; 
x_394 = lean_ctor_get(x_387, 1);
lean_inc(x_394);
lean_dec(x_387);
x_395 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_380, x_386);
lean_dec(x_380);
if (x_395 == 0)
{
lean_object* x_396; lean_object* x_397; lean_object* x_398; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_396 = x_1;
} else {
 lean_dec_ref(x_1);
 x_396 = lean_box(0);
}
if (lean_is_scalar(x_396)) {
 x_397 = lean_alloc_ctor(5, 1, 0);
} else {
 x_397 = x_396;
}
lean_ctor_set(x_397, 0, x_386);
x_398 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_398, 0, x_397);
lean_ctor_set(x_398, 1, x_394);
return x_398;
}
else
{
lean_object* x_399; 
lean_dec(x_386);
x_399 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_399, 0, x_1);
lean_ctor_set(x_399, 1, x_394);
return x_399;
}
}
}
else
{
lean_object* x_400; 
lean_dec(x_380);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_400 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_56, x_8, x_383);
lean_dec(x_8);
lean_dec(x_56);
lean_dec(x_6);
lean_dec(x_5);
return x_400;
}
}
case 6:
{
lean_object* x_401; lean_object* x_402; uint8_t x_403; 
lean_dec(x_56);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_401 = lean_ctor_get(x_1, 0);
lean_inc(x_401);
x_402 = lean_st_ref_get(x_3, x_58);
lean_dec(x_3);
x_403 = !lean_is_exclusive(x_402);
if (x_403 == 0)
{
lean_object* x_404; lean_object* x_405; lean_object* x_406; size_t x_407; size_t x_408; uint8_t x_409; 
x_404 = lean_ctor_get(x_402, 0);
x_405 = lean_ctor_get(x_404, 0);
lean_inc(x_405);
lean_dec(x_404);
lean_inc(x_401);
x_406 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_405, x_40, x_401);
lean_dec(x_405);
x_407 = lean_ptr_addr(x_401);
lean_dec(x_401);
x_408 = lean_ptr_addr(x_406);
x_409 = lean_usize_dec_eq(x_407, x_408);
if (x_409 == 0)
{
uint8_t x_410; 
x_410 = !lean_is_exclusive(x_1);
if (x_410 == 0)
{
lean_object* x_411; 
x_411 = lean_ctor_get(x_1, 0);
lean_dec(x_411);
lean_ctor_set(x_1, 0, x_406);
lean_ctor_set(x_402, 0, x_1);
return x_402;
}
else
{
lean_object* x_412; 
lean_dec(x_1);
x_412 = lean_alloc_ctor(6, 1, 0);
lean_ctor_set(x_412, 0, x_406);
lean_ctor_set(x_402, 0, x_412);
return x_402;
}
}
else
{
lean_dec(x_406);
lean_ctor_set(x_402, 0, x_1);
return x_402;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; size_t x_417; size_t x_418; uint8_t x_419; 
x_413 = lean_ctor_get(x_402, 0);
x_414 = lean_ctor_get(x_402, 1);
lean_inc(x_414);
lean_inc(x_413);
lean_dec(x_402);
x_415 = lean_ctor_get(x_413, 0);
lean_inc(x_415);
lean_dec(x_413);
lean_inc(x_401);
x_416 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_415, x_40, x_401);
lean_dec(x_415);
x_417 = lean_ptr_addr(x_401);
lean_dec(x_401);
x_418 = lean_ptr_addr(x_416);
x_419 = lean_usize_dec_eq(x_417, x_418);
if (x_419 == 0)
{
lean_object* x_420; lean_object* x_421; lean_object* x_422; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_420 = x_1;
} else {
 lean_dec_ref(x_1);
 x_420 = lean_box(0);
}
if (lean_is_scalar(x_420)) {
 x_421 = lean_alloc_ctor(6, 1, 0);
} else {
 x_421 = x_420;
}
lean_ctor_set(x_421, 0, x_416);
x_422 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_422, 0, x_421);
lean_ctor_set(x_422, 1, x_414);
return x_422;
}
else
{
lean_object* x_423; 
lean_dec(x_416);
x_423 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_423, 0, x_1);
lean_ctor_set(x_423, 1, x_414);
return x_423;
}
}
}
default: 
{
lean_object* x_424; lean_object* x_425; 
lean_dec(x_7);
x_424 = lean_ctor_get(x_1, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_1, 1);
lean_inc(x_425);
x_59 = x_424;
x_60 = x_425;
x_61 = x_2;
x_62 = x_3;
x_63 = x_4;
x_64 = x_5;
x_65 = x_6;
x_66 = x_56;
x_67 = x_8;
goto block_104;
}
}
block_104:
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_68 = lean_ctor_get(x_59, 0);
lean_inc(x_68);
x_69 = l_Lean_Compiler_LCNF_Simp_isOnceOrMustInline___redArg(x_68, x_62, x_58);
lean_dec(x_68);
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
lean_dec(x_69);
lean_inc(x_70);
lean_inc(x_1);
lean_inc(x_60);
x_72 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed), 13, 3);
lean_closure_set(x_72, 0, x_60);
lean_closure_set(x_72, 1, x_1);
lean_closure_set(x_72, 2, x_70);
x_73 = lean_unbox(x_70);
if (x_73 == 0)
{
uint8_t x_74; 
lean_dec(x_70);
lean_dec(x_60);
x_74 = l_Lean_Compiler_LCNF_Code_isFun(x_1);
lean_dec(x_1);
if (x_74 == 0)
{
x_10 = x_72;
x_11 = x_59;
x_12 = x_61;
x_13 = x_62;
x_14 = x_63;
x_15 = x_64;
x_16 = x_65;
x_17 = x_66;
x_18 = x_67;
x_19 = x_71;
goto block_29;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = lean_ctor_get(x_59, 3);
lean_inc(x_75);
x_76 = lean_ctor_get(x_59, 2);
lean_inc(x_76);
x_77 = l_Lean_Compiler_LCNF_isEtaExpandCandidateCore(x_75, x_76);
lean_dec(x_76);
if (x_77 == 0)
{
x_10 = x_72;
x_11 = x_59;
x_12 = x_61;
x_13 = x_62;
x_14 = x_63;
x_15 = x_64;
x_16 = x_65;
x_17 = x_66;
x_18 = x_67;
x_19 = x_71;
goto block_29;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_st_ref_get(x_62, x_71);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
x_80 = lean_ctor_get(x_78, 1);
lean_inc(x_80);
lean_dec(x_78);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
lean_dec(x_79);
x_82 = l_Lean_Compiler_LCNF_normFunDeclImp(x_40, x_59, x_81, x_64, x_65, x_66, x_67, x_80);
lean_dec(x_81);
x_83 = lean_ctor_get(x_82, 0);
lean_inc(x_83);
x_84 = lean_ctor_get(x_82, 1);
lean_inc(x_84);
lean_dec(x_82);
lean_inc(x_67);
lean_inc(x_66);
lean_inc(x_65);
lean_inc(x_64);
x_85 = l_Lean_Compiler_LCNF_FunDeclCore_etaExpand(x_83, x_64, x_65, x_66, x_67, x_84);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_62, x_87);
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_10 = x_72;
x_11 = x_86;
x_12 = x_61;
x_13 = x_62;
x_14 = x_63;
x_15 = x_64;
x_16 = x_65;
x_17 = x_66;
x_18 = x_67;
x_19 = x_89;
goto block_29;
}
else
{
uint8_t x_90; 
lean_dec(x_72);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_63);
lean_dec(x_62);
lean_dec(x_61);
x_90 = !lean_is_exclusive(x_85);
if (x_90 == 0)
{
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_85, 0);
x_92 = lean_ctor_get(x_85, 1);
lean_inc(x_92);
lean_inc(x_91);
lean_dec(x_85);
x_93 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_93, 0, x_91);
lean_ctor_set(x_93, 1, x_92);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; 
lean_dec(x_72);
x_94 = lean_st_ref_get(x_62, x_71);
x_95 = lean_ctor_get(x_94, 0);
lean_inc(x_95);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
lean_dec(x_94);
x_97 = lean_ctor_get(x_95, 0);
lean_inc(x_97);
lean_dec(x_95);
x_98 = l_Lean_Compiler_LCNF_normFunDeclImp(x_40, x_59, x_97, x_64, x_65, x_66, x_67, x_96);
lean_dec(x_97);
x_99 = lean_ctor_get(x_98, 0);
lean_inc(x_99);
x_100 = lean_ctor_get(x_98, 1);
lean_inc(x_100);
lean_dec(x_98);
x_101 = lean_box(0);
x_102 = lean_unbox(x_70);
lean_dec(x_70);
x_103 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_60, x_1, x_102, x_99, x_101, x_61, x_62, x_63, x_64, x_65, x_66, x_67, x_100);
return x_103;
}
}
}
else
{
lean_object* x_426; 
lean_dec(x_39);
lean_dec(x_38);
lean_dec(x_1);
x_426 = l_Lean_Compiler_LCNF_Simp_withIncRecDepth_throwMaxRecDepth(lean_box(0), x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_426;
}
block_29:
{
lean_object* x_20; 
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
x_20 = l_Lean_Compiler_LCNF_Simp_simpFunDecl(x_11, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_19);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_box(0);
x_24 = lean_apply_10(x_10, x_21, x_23, x_12, x_13, x_14, x_15, x_16, x_17, x_18, x_22);
return x_24;
}
else
{
uint8_t x_25; 
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_10);
x_25 = !lean_is_exclusive(x_20);
if (x_25 == 0)
{
return x_20;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_20, 0);
x_27 = lean_ctor_get(x_20, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_20);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
block_37:
{
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_31);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_30);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_32);
lean_dec(x_31);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_1);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = lean_usize_dec_lt(x_3, x_2);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_4);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 1);
lean_inc(x_9);
x_10 = lean_ctor_get(x_4, 2);
lean_inc(x_10);
x_11 = lean_nat_dec_lt(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec(x_10);
lean_dec(x_9);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_4);
lean_ctor_set(x_12, 1, x_6);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_13 = lean_st_ref_take(x_5, x_6);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_9, x_16);
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint64_t x_44; lean_object* x_45; uint64_t x_46; uint64_t x_47; uint64_t x_48; lean_object* x_49; uint64_t x_50; uint64_t x_51; uint64_t x_52; size_t x_53; size_t x_54; size_t x_55; size_t x_56; size_t x_57; lean_object* x_58; uint8_t x_59; 
x_20 = lean_ctor_get(x_18, 0);
x_21 = lean_ctor_get(x_18, 1);
x_22 = lean_ctor_get(x_4, 0);
lean_inc(x_22);
lean_dec(x_4);
lean_inc(x_22);
x_23 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_17);
lean_ctor_set(x_23, 2, x_10);
x_39 = lean_array_uget(x_1, x_3);
x_40 = lean_array_fget(x_22, x_9);
lean_dec(x_9);
lean_dec(x_22);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
lean_dec(x_39);
x_42 = l_Lean_Compiler_LCNF_Arg_toExpr(x_40);
x_43 = lean_array_get_size(x_21);
x_44 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_41);
x_45 = lean_unsigned_to_nat(32u);
x_46 = lean_uint64_of_nat(x_45);
x_47 = lean_uint64_shift_right(x_44, x_46);
x_48 = lean_uint64_xor(x_44, x_47);
x_49 = lean_unsigned_to_nat(16u);
x_50 = lean_uint64_of_nat(x_49);
x_51 = lean_uint64_shift_right(x_48, x_50);
x_52 = lean_uint64_xor(x_48, x_51);
x_53 = lean_uint64_to_usize(x_52);
x_54 = lean_usize_of_nat(x_43);
lean_dec(x_43);
x_55 = lean_usize_of_nat(x_16);
x_56 = lean_usize_sub(x_54, x_55);
x_57 = lean_usize_land(x_53, x_56);
x_58 = lean_array_uget(x_21, x_57);
x_59 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_41, x_58);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_60 = lean_nat_add(x_20, x_16);
lean_dec(x_20);
x_61 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_58);
x_62 = lean_array_uset(x_21, x_57, x_61);
x_63 = lean_unsigned_to_nat(2u);
x_64 = lean_nat_shiftl(x_60, x_63);
x_65 = lean_unsigned_to_nat(3u);
x_66 = lean_nat_div(x_64, x_65);
lean_dec(x_64);
x_67 = lean_array_get_size(x_62);
x_68 = lean_nat_dec_le(x_66, x_67);
lean_dec(x_67);
lean_dec(x_66);
if (x_68 == 0)
{
lean_object* x_69; 
x_69 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_62);
lean_ctor_set(x_18, 1, x_69);
lean_ctor_set(x_18, 0, x_60);
x_24 = x_18;
goto block_38;
}
else
{
lean_ctor_set(x_18, 1, x_62);
lean_ctor_set(x_18, 0, x_60);
x_24 = x_18;
goto block_38;
}
}
else
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; 
x_70 = lean_box(0);
x_71 = lean_array_uset(x_21, x_57, x_70);
x_72 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_41, x_42, x_58);
x_73 = lean_array_uset(x_71, x_57, x_72);
lean_ctor_set(x_18, 1, x_73);
x_24 = x_18;
goto block_38;
}
block_38:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; size_t x_35; size_t x_36; 
x_25 = lean_ctor_get(x_14, 1);
lean_inc(x_25);
x_26 = lean_ctor_get(x_14, 2);
lean_inc(x_26);
x_27 = lean_ctor_get(x_14, 3);
lean_inc(x_27);
x_28 = lean_ctor_get_uint8(x_14, sizeof(void*)*7);
x_29 = lean_ctor_get(x_14, 4);
lean_inc(x_29);
x_30 = lean_ctor_get(x_14, 5);
lean_inc(x_30);
x_31 = lean_ctor_get(x_14, 6);
lean_inc(x_31);
lean_dec(x_14);
x_32 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_32, 0, x_24);
lean_ctor_set(x_32, 1, x_25);
lean_ctor_set(x_32, 2, x_26);
lean_ctor_set(x_32, 3, x_27);
lean_ctor_set(x_32, 4, x_29);
lean_ctor_set(x_32, 5, x_30);
lean_ctor_set(x_32, 6, x_31);
lean_ctor_set_uint8(x_32, sizeof(void*)*7, x_28);
x_33 = lean_st_ref_set(x_5, x_32, x_15);
x_34 = lean_ctor_get(x_33, 1);
lean_inc(x_34);
lean_dec(x_33);
x_35 = lean_usize_of_nat(x_16);
x_36 = lean_usize_add(x_3, x_35);
x_3 = x_36;
x_4 = x_23;
x_6 = x_34;
goto _start;
}
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; uint64_t x_98; lean_object* x_99; uint64_t x_100; uint64_t x_101; uint64_t x_102; lean_object* x_103; uint64_t x_104; uint64_t x_105; uint64_t x_106; size_t x_107; size_t x_108; size_t x_109; size_t x_110; size_t x_111; lean_object* x_112; uint8_t x_113; 
x_74 = lean_ctor_get(x_18, 0);
x_75 = lean_ctor_get(x_18, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_18);
x_76 = lean_ctor_get(x_4, 0);
lean_inc(x_76);
lean_dec(x_4);
lean_inc(x_76);
x_77 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_17);
lean_ctor_set(x_77, 2, x_10);
x_93 = lean_array_uget(x_1, x_3);
x_94 = lean_array_fget(x_76, x_9);
lean_dec(x_9);
lean_dec(x_76);
x_95 = lean_ctor_get(x_93, 0);
lean_inc(x_95);
lean_dec(x_93);
x_96 = l_Lean_Compiler_LCNF_Arg_toExpr(x_94);
x_97 = lean_array_get_size(x_75);
x_98 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_95);
x_99 = lean_unsigned_to_nat(32u);
x_100 = lean_uint64_of_nat(x_99);
x_101 = lean_uint64_shift_right(x_98, x_100);
x_102 = lean_uint64_xor(x_98, x_101);
x_103 = lean_unsigned_to_nat(16u);
x_104 = lean_uint64_of_nat(x_103);
x_105 = lean_uint64_shift_right(x_102, x_104);
x_106 = lean_uint64_xor(x_102, x_105);
x_107 = lean_uint64_to_usize(x_106);
x_108 = lean_usize_of_nat(x_97);
lean_dec(x_97);
x_109 = lean_usize_of_nat(x_16);
x_110 = lean_usize_sub(x_108, x_109);
x_111 = lean_usize_land(x_107, x_110);
x_112 = lean_array_uget(x_75, x_111);
x_113 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_95, x_112);
if (x_113 == 0)
{
lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; uint8_t x_122; 
x_114 = lean_nat_add(x_74, x_16);
lean_dec(x_74);
x_115 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_115, 0, x_95);
lean_ctor_set(x_115, 1, x_96);
lean_ctor_set(x_115, 2, x_112);
x_116 = lean_array_uset(x_75, x_111, x_115);
x_117 = lean_unsigned_to_nat(2u);
x_118 = lean_nat_shiftl(x_114, x_117);
x_119 = lean_unsigned_to_nat(3u);
x_120 = lean_nat_div(x_118, x_119);
lean_dec(x_118);
x_121 = lean_array_get_size(x_116);
x_122 = lean_nat_dec_le(x_120, x_121);
lean_dec(x_121);
lean_dec(x_120);
if (x_122 == 0)
{
lean_object* x_123; lean_object* x_124; 
x_123 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_116);
x_124 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_124, 0, x_114);
lean_ctor_set(x_124, 1, x_123);
x_78 = x_124;
goto block_92;
}
else
{
lean_object* x_125; 
x_125 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_125, 0, x_114);
lean_ctor_set(x_125, 1, x_116);
x_78 = x_125;
goto block_92;
}
}
else
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
x_126 = lean_box(0);
x_127 = lean_array_uset(x_75, x_111, x_126);
x_128 = l_Std_DHashMap_Internal_AssocList_replace___at___Lean_Compiler_LCNF_LCtx_addParam_spec__4___redArg(x_95, x_96, x_112);
x_129 = lean_array_uset(x_127, x_111, x_128);
x_130 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_130, 0, x_74);
lean_ctor_set(x_130, 1, x_129);
x_78 = x_130;
goto block_92;
}
block_92:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; uint8_t x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; size_t x_89; size_t x_90; 
x_79 = lean_ctor_get(x_14, 1);
lean_inc(x_79);
x_80 = lean_ctor_get(x_14, 2);
lean_inc(x_80);
x_81 = lean_ctor_get(x_14, 3);
lean_inc(x_81);
x_82 = lean_ctor_get_uint8(x_14, sizeof(void*)*7);
x_83 = lean_ctor_get(x_14, 4);
lean_inc(x_83);
x_84 = lean_ctor_get(x_14, 5);
lean_inc(x_84);
x_85 = lean_ctor_get(x_14, 6);
lean_inc(x_85);
lean_dec(x_14);
x_86 = lean_alloc_ctor(0, 7, 1);
lean_ctor_set(x_86, 0, x_78);
lean_ctor_set(x_86, 1, x_79);
lean_ctor_set(x_86, 2, x_80);
lean_ctor_set(x_86, 3, x_81);
lean_ctor_set(x_86, 4, x_83);
lean_ctor_set(x_86, 5, x_84);
lean_ctor_set(x_86, 6, x_85);
lean_ctor_set_uint8(x_86, sizeof(void*)*7, x_82);
x_87 = lean_st_ref_set(x_5, x_86, x_15);
x_88 = lean_ctor_get(x_87, 1);
lean_inc(x_88);
lean_dec(x_87);
x_89 = lean_usize_of_nat(x_16);
x_90 = lean_usize_add(x_3, x_89);
x_3 = x_90;
x_4 = x_77;
x_6 = x_88;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_2, x_3, x_4, x_6, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = lean_unbox(x_13);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normFVarImp(x_15, x_14, x_16);
lean_dec(x_15);
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_19, x_4, x_6, x_8, x_12);
lean_dec(x_19);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
lean_free_object(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_22 = !lean_is_exclusive(x_20);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_20, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_20, 0, x_24);
return x_20;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_20, 1);
lean_inc(x_25);
lean_dec(x_20);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_20, 1);
lean_inc(x_28);
lean_dec(x_20);
x_29 = !lean_is_exclusive(x_21);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_30 = lean_ctor_get(x_21, 0);
x_31 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_30);
x_32 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_31);
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_32, 1);
lean_inc(x_34);
lean_dec(x_32);
lean_ctor_set_tag(x_17, 4);
lean_ctor_set(x_17, 0, x_34);
x_35 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_17, x_6, x_28);
lean_dec(x_17);
x_36 = lean_ctor_get(x_35, 1);
lean_inc(x_36);
lean_dec(x_35);
x_37 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_36);
if (lean_obj_tag(x_33) == 0)
{
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; lean_object* x_47; size_t x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_38 = lean_ctor_get(x_37, 1);
lean_inc(x_38);
lean_dec(x_37);
x_39 = lean_ctor_get(x_33, 1);
lean_inc(x_39);
x_40 = lean_ctor_get(x_33, 2);
lean_inc(x_40);
lean_dec(x_33);
x_41 = lean_ctor_get(x_30, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_30, 1);
lean_inc(x_42);
lean_dec(x_30);
x_43 = lean_ctor_get(x_41, 3);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_array_get_size(x_42);
x_45 = l_Array_toSubarray___redArg(x_42, x_43, x_44);
x_46 = lean_array_size(x_39);
x_47 = lean_unsigned_to_nat(0u);
x_48 = lean_usize_of_nat(x_47);
x_49 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_39, x_46, x_48, x_45, x_3, x_38);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
lean_inc(x_6);
x_51 = l_Lean_Compiler_LCNF_Simp_simp(x_40, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_50);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_39, x_6, x_53);
lean_dec(x_6);
lean_dec(x_39);
x_55 = !lean_is_exclusive(x_54);
if (x_55 == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_54, 0);
lean_dec(x_56);
lean_ctor_set(x_21, 0, x_52);
lean_ctor_set(x_54, 0, x_21);
return x_54;
}
else
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
lean_ctor_set(x_21, 0, x_52);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_21);
lean_ctor_set(x_58, 1, x_57);
return x_58;
}
}
else
{
uint8_t x_59; 
lean_dec(x_39);
lean_free_object(x_21);
lean_dec(x_6);
x_59 = !lean_is_exclusive(x_51);
if (x_59 == 0)
{
return x_51;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_51, 0);
x_61 = lean_ctor_get(x_51, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_51);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
uint8_t x_63; 
x_63 = !lean_is_exclusive(x_37);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_64 = lean_ctor_get(x_37, 1);
x_65 = lean_ctor_get(x_37, 0);
lean_dec(x_65);
x_66 = lean_ctor_get(x_33, 1);
lean_inc(x_66);
x_67 = lean_ctor_get(x_33, 2);
lean_inc(x_67);
lean_dec(x_33);
x_68 = !lean_is_exclusive(x_30);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_30, 0);
x_70 = lean_unsigned_to_nat(0u);
x_71 = lean_nat_dec_eq(x_69, x_70);
if (x_71 == 1)
{
lean_object* x_72; 
lean_free_object(x_30);
lean_dec(x_69);
lean_dec(x_66);
lean_free_object(x_37);
x_72 = l_Lean_Compiler_LCNF_Simp_simp(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_72) == 0)
{
uint8_t x_73; 
x_73 = !lean_is_exclusive(x_72);
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_72, 0);
lean_ctor_set(x_21, 0, x_74);
lean_ctor_set(x_72, 0, x_21);
return x_72;
}
else
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_ctor_get(x_72, 0);
x_76 = lean_ctor_get(x_72, 1);
lean_inc(x_76);
lean_inc(x_75);
lean_dec(x_72);
lean_ctor_set(x_21, 0, x_75);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_21);
lean_ctor_set(x_77, 1, x_76);
return x_77;
}
}
else
{
uint8_t x_78; 
lean_free_object(x_21);
x_78 = !lean_is_exclusive(x_72);
if (x_78 == 0)
{
return x_72;
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_72, 0);
x_80 = lean_ctor_get(x_72, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_72);
x_81 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
return x_81;
}
}
}
else
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; 
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_sub(x_69, x_82);
lean_dec(x_69);
lean_ctor_set_tag(x_30, 0);
lean_ctor_set(x_30, 0, x_83);
x_84 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_84, 0, x_30);
x_85 = lean_mk_string_unchecked("_x", 2, 2);
x_86 = l_Lean_Name_mkStr1(x_85);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_87 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_84, x_86, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_87) == 0)
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
x_89 = lean_ctor_get(x_87, 1);
lean_inc(x_89);
lean_dec(x_87);
x_90 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_91 = lean_array_get(x_90, x_66, x_70);
x_92 = lean_ctor_get(x_91, 0);
lean_inc(x_92);
lean_dec(x_91);
x_93 = lean_ctor_get(x_88, 0);
lean_inc(x_93);
x_94 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_92, x_93, x_3, x_6, x_7, x_8, x_89);
if (lean_obj_tag(x_94) == 0)
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_94, 1);
lean_inc(x_95);
lean_dec(x_94);
lean_inc(x_6);
x_96 = l_Lean_Compiler_LCNF_Simp_simp(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; uint8_t x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_66, x_6, x_98);
lean_dec(x_6);
lean_dec(x_66);
x_100 = !lean_is_exclusive(x_99);
if (x_100 == 0)
{
lean_object* x_101; 
x_101 = lean_ctor_get(x_99, 0);
lean_dec(x_101);
lean_ctor_set(x_37, 1, x_97);
lean_ctor_set(x_37, 0, x_88);
lean_ctor_set(x_21, 0, x_37);
lean_ctor_set(x_99, 0, x_21);
return x_99;
}
else
{
lean_object* x_102; lean_object* x_103; 
x_102 = lean_ctor_get(x_99, 1);
lean_inc(x_102);
lean_dec(x_99);
lean_ctor_set(x_37, 1, x_97);
lean_ctor_set(x_37, 0, x_88);
lean_ctor_set(x_21, 0, x_37);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_21);
lean_ctor_set(x_103, 1, x_102);
return x_103;
}
}
else
{
uint8_t x_104; 
lean_dec(x_88);
lean_dec(x_66);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_6);
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
else
{
uint8_t x_108; 
lean_dec(x_88);
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_108 = !lean_is_exclusive(x_94);
if (x_108 == 0)
{
return x_94;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; 
x_109 = lean_ctor_get(x_94, 0);
x_110 = lean_ctor_get(x_94, 1);
lean_inc(x_110);
lean_inc(x_109);
lean_dec(x_94);
x_111 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_111, 0, x_109);
lean_ctor_set(x_111, 1, x_110);
return x_111;
}
}
}
else
{
uint8_t x_112; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_112 = !lean_is_exclusive(x_87);
if (x_112 == 0)
{
return x_87;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_87, 0);
x_114 = lean_ctor_get(x_87, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_87);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
}
else
{
lean_object* x_116; lean_object* x_117; uint8_t x_118; 
x_116 = lean_ctor_get(x_30, 0);
lean_inc(x_116);
lean_dec(x_30);
x_117 = lean_unsigned_to_nat(0u);
x_118 = lean_nat_dec_eq(x_116, x_117);
if (x_118 == 1)
{
lean_object* x_119; 
lean_dec(x_116);
lean_dec(x_66);
lean_free_object(x_37);
x_119 = l_Lean_Compiler_LCNF_Simp_simp(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_119) == 0)
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; 
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
lean_ctor_set(x_21, 0, x_120);
if (lean_is_scalar(x_122)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_122;
}
lean_ctor_set(x_123, 0, x_21);
lean_ctor_set(x_123, 1, x_121);
return x_123;
}
else
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_free_object(x_21);
x_124 = lean_ctor_get(x_119, 0);
lean_inc(x_124);
x_125 = lean_ctor_get(x_119, 1);
lean_inc(x_125);
if (lean_is_exclusive(x_119)) {
 lean_ctor_release(x_119, 0);
 lean_ctor_release(x_119, 1);
 x_126 = x_119;
} else {
 lean_dec_ref(x_119);
 x_126 = lean_box(0);
}
if (lean_is_scalar(x_126)) {
 x_127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_127 = x_126;
}
lean_ctor_set(x_127, 0, x_124);
lean_ctor_set(x_127, 1, x_125);
return x_127;
}
}
else
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_128 = lean_unsigned_to_nat(1u);
x_129 = lean_nat_sub(x_116, x_128);
lean_dec(x_116);
x_130 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_130, 0, x_129);
x_131 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_131, 0, x_130);
x_132 = lean_mk_string_unchecked("_x", 2, 2);
x_133 = l_Lean_Name_mkStr1(x_132);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_134 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_131, x_133, x_5, x_6, x_7, x_8, x_64);
if (lean_obj_tag(x_134) == 0)
{
lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; 
x_135 = lean_ctor_get(x_134, 0);
lean_inc(x_135);
x_136 = lean_ctor_get(x_134, 1);
lean_inc(x_136);
lean_dec(x_134);
x_137 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_138 = lean_array_get(x_137, x_66, x_117);
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
lean_dec(x_138);
x_140 = lean_ctor_get(x_135, 0);
lean_inc(x_140);
x_141 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_139, x_140, x_3, x_6, x_7, x_8, x_136);
if (lean_obj_tag(x_141) == 0)
{
lean_object* x_142; lean_object* x_143; 
x_142 = lean_ctor_get(x_141, 1);
lean_inc(x_142);
lean_dec(x_141);
lean_inc(x_6);
x_143 = l_Lean_Compiler_LCNF_Simp_simp(x_67, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_142);
if (lean_obj_tag(x_143) == 0)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; 
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_143, 1);
lean_inc(x_145);
lean_dec(x_143);
x_146 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_66, x_6, x_145);
lean_dec(x_6);
lean_dec(x_66);
x_147 = lean_ctor_get(x_146, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_146)) {
 lean_ctor_release(x_146, 0);
 lean_ctor_release(x_146, 1);
 x_148 = x_146;
} else {
 lean_dec_ref(x_146);
 x_148 = lean_box(0);
}
lean_ctor_set(x_37, 1, x_144);
lean_ctor_set(x_37, 0, x_135);
lean_ctor_set(x_21, 0, x_37);
if (lean_is_scalar(x_148)) {
 x_149 = lean_alloc_ctor(0, 2, 0);
} else {
 x_149 = x_148;
}
lean_ctor_set(x_149, 0, x_21);
lean_ctor_set(x_149, 1, x_147);
return x_149;
}
else
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_135);
lean_dec(x_66);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_6);
x_150 = lean_ctor_get(x_143, 0);
lean_inc(x_150);
x_151 = lean_ctor_get(x_143, 1);
lean_inc(x_151);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_152 = x_143;
} else {
 lean_dec_ref(x_143);
 x_152 = lean_box(0);
}
if (lean_is_scalar(x_152)) {
 x_153 = lean_alloc_ctor(1, 2, 0);
} else {
 x_153 = x_152;
}
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_151);
return x_153;
}
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; 
lean_dec(x_135);
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_154 = lean_ctor_get(x_141, 0);
lean_inc(x_154);
x_155 = lean_ctor_get(x_141, 1);
lean_inc(x_155);
if (lean_is_exclusive(x_141)) {
 lean_ctor_release(x_141, 0);
 lean_ctor_release(x_141, 1);
 x_156 = x_141;
} else {
 lean_dec_ref(x_141);
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
}
else
{
lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_67);
lean_dec(x_66);
lean_free_object(x_37);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_158 = lean_ctor_get(x_134, 0);
lean_inc(x_158);
x_159 = lean_ctor_get(x_134, 1);
lean_inc(x_159);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_160 = x_134;
} else {
 lean_dec_ref(x_134);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(1, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_158);
lean_ctor_set(x_161, 1, x_159);
return x_161;
}
}
}
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; uint8_t x_168; 
x_162 = lean_ctor_get(x_37, 1);
lean_inc(x_162);
lean_dec(x_37);
x_163 = lean_ctor_get(x_33, 1);
lean_inc(x_163);
x_164 = lean_ctor_get(x_33, 2);
lean_inc(x_164);
lean_dec(x_33);
x_165 = lean_ctor_get(x_30, 0);
lean_inc(x_165);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_166 = x_30;
} else {
 lean_dec_ref(x_30);
 x_166 = lean_box(0);
}
x_167 = lean_unsigned_to_nat(0u);
x_168 = lean_nat_dec_eq(x_165, x_167);
if (x_168 == 1)
{
lean_object* x_169; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_163);
x_169 = l_Lean_Compiler_LCNF_Simp_simp(x_164, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_162);
if (lean_obj_tag(x_169) == 0)
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_170 = lean_ctor_get(x_169, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_169, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_172 = x_169;
} else {
 lean_dec_ref(x_169);
 x_172 = lean_box(0);
}
lean_ctor_set(x_21, 0, x_170);
if (lean_is_scalar(x_172)) {
 x_173 = lean_alloc_ctor(0, 2, 0);
} else {
 x_173 = x_172;
}
lean_ctor_set(x_173, 0, x_21);
lean_ctor_set(x_173, 1, x_171);
return x_173;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
lean_free_object(x_21);
x_174 = lean_ctor_get(x_169, 0);
lean_inc(x_174);
x_175 = lean_ctor_get(x_169, 1);
lean_inc(x_175);
if (lean_is_exclusive(x_169)) {
 lean_ctor_release(x_169, 0);
 lean_ctor_release(x_169, 1);
 x_176 = x_169;
} else {
 lean_dec_ref(x_169);
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
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; 
x_178 = lean_unsigned_to_nat(1u);
x_179 = lean_nat_sub(x_165, x_178);
lean_dec(x_165);
if (lean_is_scalar(x_166)) {
 x_180 = lean_alloc_ctor(0, 1, 0);
} else {
 x_180 = x_166;
 lean_ctor_set_tag(x_180, 0);
}
lean_ctor_set(x_180, 0, x_179);
x_181 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_181, 0, x_180);
x_182 = lean_mk_string_unchecked("_x", 2, 2);
x_183 = l_Lean_Name_mkStr1(x_182);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_184 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_181, x_183, x_5, x_6, x_7, x_8, x_162);
if (lean_obj_tag(x_184) == 0)
{
lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_185 = lean_ctor_get(x_184, 0);
lean_inc(x_185);
x_186 = lean_ctor_get(x_184, 1);
lean_inc(x_186);
lean_dec(x_184);
x_187 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_188 = lean_array_get(x_187, x_163, x_167);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
lean_dec(x_188);
x_190 = lean_ctor_get(x_185, 0);
lean_inc(x_190);
x_191 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_189, x_190, x_3, x_6, x_7, x_8, x_186);
if (lean_obj_tag(x_191) == 0)
{
lean_object* x_192; lean_object* x_193; 
x_192 = lean_ctor_get(x_191, 1);
lean_inc(x_192);
lean_dec(x_191);
lean_inc(x_6);
x_193 = l_Lean_Compiler_LCNF_Simp_simp(x_164, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_192);
if (lean_obj_tag(x_193) == 0)
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; 
x_194 = lean_ctor_get(x_193, 0);
lean_inc(x_194);
x_195 = lean_ctor_get(x_193, 1);
lean_inc(x_195);
lean_dec(x_193);
x_196 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_163, x_6, x_195);
lean_dec(x_6);
lean_dec(x_163);
x_197 = lean_ctor_get(x_196, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_196)) {
 lean_ctor_release(x_196, 0);
 lean_ctor_release(x_196, 1);
 x_198 = x_196;
} else {
 lean_dec_ref(x_196);
 x_198 = lean_box(0);
}
x_199 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_199, 0, x_185);
lean_ctor_set(x_199, 1, x_194);
lean_ctor_set(x_21, 0, x_199);
if (lean_is_scalar(x_198)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_198;
}
lean_ctor_set(x_200, 0, x_21);
lean_ctor_set(x_200, 1, x_197);
return x_200;
}
else
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; 
lean_dec(x_185);
lean_dec(x_163);
lean_free_object(x_21);
lean_dec(x_6);
x_201 = lean_ctor_get(x_193, 0);
lean_inc(x_201);
x_202 = lean_ctor_get(x_193, 1);
lean_inc(x_202);
if (lean_is_exclusive(x_193)) {
 lean_ctor_release(x_193, 0);
 lean_ctor_release(x_193, 1);
 x_203 = x_193;
} else {
 lean_dec_ref(x_193);
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
lean_dec(x_185);
lean_dec(x_164);
lean_dec(x_163);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_205 = lean_ctor_get(x_191, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_191, 1);
lean_inc(x_206);
if (lean_is_exclusive(x_191)) {
 lean_ctor_release(x_191, 0);
 lean_ctor_release(x_191, 1);
 x_207 = x_191;
} else {
 lean_dec_ref(x_191);
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
lean_dec(x_164);
lean_dec(x_163);
lean_free_object(x_21);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_209 = lean_ctor_get(x_184, 0);
lean_inc(x_209);
x_210 = lean_ctor_get(x_184, 1);
lean_inc(x_210);
if (lean_is_exclusive(x_184)) {
 lean_ctor_release(x_184, 0);
 lean_ctor_release(x_184, 1);
 x_211 = x_184;
} else {
 lean_dec_ref(x_184);
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
else
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
lean_dec(x_30);
x_213 = lean_ctor_get(x_37, 1);
lean_inc(x_213);
lean_dec(x_37);
x_214 = lean_ctor_get(x_33, 0);
lean_inc(x_214);
lean_dec(x_33);
x_215 = l_Lean_Compiler_LCNF_Simp_simp(x_214, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_213);
if (lean_obj_tag(x_215) == 0)
{
uint8_t x_216; 
x_216 = !lean_is_exclusive(x_215);
if (x_216 == 0)
{
lean_object* x_217; 
x_217 = lean_ctor_get(x_215, 0);
lean_ctor_set(x_21, 0, x_217);
lean_ctor_set(x_215, 0, x_21);
return x_215;
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; 
x_218 = lean_ctor_get(x_215, 0);
x_219 = lean_ctor_get(x_215, 1);
lean_inc(x_219);
lean_inc(x_218);
lean_dec(x_215);
lean_ctor_set(x_21, 0, x_218);
x_220 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_220, 0, x_21);
lean_ctor_set(x_220, 1, x_219);
return x_220;
}
}
else
{
uint8_t x_221; 
lean_free_object(x_21);
x_221 = !lean_is_exclusive(x_215);
if (x_221 == 0)
{
return x_215;
}
else
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; 
x_222 = lean_ctor_get(x_215, 0);
x_223 = lean_ctor_get(x_215, 1);
lean_inc(x_223);
lean_inc(x_222);
lean_dec(x_215);
x_224 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_224, 0, x_222);
lean_ctor_set(x_224, 1, x_223);
return x_224;
}
}
}
}
else
{
lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_225 = lean_ctor_get(x_21, 0);
lean_inc(x_225);
lean_dec(x_21);
x_226 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_225);
x_227 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_226);
x_228 = lean_ctor_get(x_227, 0);
lean_inc(x_228);
x_229 = lean_ctor_get(x_227, 1);
lean_inc(x_229);
lean_dec(x_227);
lean_ctor_set_tag(x_17, 4);
lean_ctor_set(x_17, 0, x_229);
x_230 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_17, x_6, x_28);
lean_dec(x_17);
x_231 = lean_ctor_get(x_230, 1);
lean_inc(x_231);
lean_dec(x_230);
x_232 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_231);
if (lean_obj_tag(x_228) == 0)
{
if (lean_obj_tag(x_225) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; size_t x_241; lean_object* x_242; size_t x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_233 = lean_ctor_get(x_232, 1);
lean_inc(x_233);
lean_dec(x_232);
x_234 = lean_ctor_get(x_228, 1);
lean_inc(x_234);
x_235 = lean_ctor_get(x_228, 2);
lean_inc(x_235);
lean_dec(x_228);
x_236 = lean_ctor_get(x_225, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_225, 1);
lean_inc(x_237);
lean_dec(x_225);
x_238 = lean_ctor_get(x_236, 3);
lean_inc(x_238);
lean_dec(x_236);
x_239 = lean_array_get_size(x_237);
x_240 = l_Array_toSubarray___redArg(x_237, x_238, x_239);
x_241 = lean_array_size(x_234);
x_242 = lean_unsigned_to_nat(0u);
x_243 = lean_usize_of_nat(x_242);
x_244 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_234, x_241, x_243, x_240, x_3, x_233);
x_245 = lean_ctor_get(x_244, 1);
lean_inc(x_245);
lean_dec(x_244);
lean_inc(x_6);
x_246 = l_Lean_Compiler_LCNF_Simp_simp(x_235, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_245);
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_247 = lean_ctor_get(x_246, 0);
lean_inc(x_247);
x_248 = lean_ctor_get(x_246, 1);
lean_inc(x_248);
lean_dec(x_246);
x_249 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_234, x_6, x_248);
lean_dec(x_6);
lean_dec(x_234);
x_250 = lean_ctor_get(x_249, 1);
lean_inc(x_250);
if (lean_is_exclusive(x_249)) {
 lean_ctor_release(x_249, 0);
 lean_ctor_release(x_249, 1);
 x_251 = x_249;
} else {
 lean_dec_ref(x_249);
 x_251 = lean_box(0);
}
x_252 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_252, 0, x_247);
if (lean_is_scalar(x_251)) {
 x_253 = lean_alloc_ctor(0, 2, 0);
} else {
 x_253 = x_251;
}
lean_ctor_set(x_253, 0, x_252);
lean_ctor_set(x_253, 1, x_250);
return x_253;
}
else
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; 
lean_dec(x_234);
lean_dec(x_6);
x_254 = lean_ctor_get(x_246, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_246, 1);
lean_inc(x_255);
if (lean_is_exclusive(x_246)) {
 lean_ctor_release(x_246, 0);
 lean_ctor_release(x_246, 1);
 x_256 = x_246;
} else {
 lean_dec_ref(x_246);
 x_256 = lean_box(0);
}
if (lean_is_scalar(x_256)) {
 x_257 = lean_alloc_ctor(1, 2, 0);
} else {
 x_257 = x_256;
}
lean_ctor_set(x_257, 0, x_254);
lean_ctor_set(x_257, 1, x_255);
return x_257;
}
}
else
{
lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint8_t x_265; 
x_258 = lean_ctor_get(x_232, 1);
lean_inc(x_258);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_259 = x_232;
} else {
 lean_dec_ref(x_232);
 x_259 = lean_box(0);
}
x_260 = lean_ctor_get(x_228, 1);
lean_inc(x_260);
x_261 = lean_ctor_get(x_228, 2);
lean_inc(x_261);
lean_dec(x_228);
x_262 = lean_ctor_get(x_225, 0);
lean_inc(x_262);
if (lean_is_exclusive(x_225)) {
 lean_ctor_release(x_225, 0);
 x_263 = x_225;
} else {
 lean_dec_ref(x_225);
 x_263 = lean_box(0);
}
x_264 = lean_unsigned_to_nat(0u);
x_265 = lean_nat_dec_eq(x_262, x_264);
if (x_265 == 1)
{
lean_object* x_266; 
lean_dec(x_263);
lean_dec(x_262);
lean_dec(x_260);
lean_dec(x_259);
x_266 = l_Lean_Compiler_LCNF_Simp_simp(x_261, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_258);
if (lean_obj_tag(x_266) == 0)
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; 
x_267 = lean_ctor_get(x_266, 0);
lean_inc(x_267);
x_268 = lean_ctor_get(x_266, 1);
lean_inc(x_268);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_269 = x_266;
} else {
 lean_dec_ref(x_266);
 x_269 = lean_box(0);
}
x_270 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_270, 0, x_267);
if (lean_is_scalar(x_269)) {
 x_271 = lean_alloc_ctor(0, 2, 0);
} else {
 x_271 = x_269;
}
lean_ctor_set(x_271, 0, x_270);
lean_ctor_set(x_271, 1, x_268);
return x_271;
}
else
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_272 = lean_ctor_get(x_266, 0);
lean_inc(x_272);
x_273 = lean_ctor_get(x_266, 1);
lean_inc(x_273);
if (lean_is_exclusive(x_266)) {
 lean_ctor_release(x_266, 0);
 lean_ctor_release(x_266, 1);
 x_274 = x_266;
} else {
 lean_dec_ref(x_266);
 x_274 = lean_box(0);
}
if (lean_is_scalar(x_274)) {
 x_275 = lean_alloc_ctor(1, 2, 0);
} else {
 x_275 = x_274;
}
lean_ctor_set(x_275, 0, x_272);
lean_ctor_set(x_275, 1, x_273);
return x_275;
}
}
else
{
lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_276 = lean_unsigned_to_nat(1u);
x_277 = lean_nat_sub(x_262, x_276);
lean_dec(x_262);
if (lean_is_scalar(x_263)) {
 x_278 = lean_alloc_ctor(0, 1, 0);
} else {
 x_278 = x_263;
 lean_ctor_set_tag(x_278, 0);
}
lean_ctor_set(x_278, 0, x_277);
x_279 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_279, 0, x_278);
x_280 = lean_mk_string_unchecked("_x", 2, 2);
x_281 = l_Lean_Name_mkStr1(x_280);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_282 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_279, x_281, x_5, x_6, x_7, x_8, x_258);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; lean_object* x_289; 
x_283 = lean_ctor_get(x_282, 0);
lean_inc(x_283);
x_284 = lean_ctor_get(x_282, 1);
lean_inc(x_284);
lean_dec(x_282);
x_285 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_286 = lean_array_get(x_285, x_260, x_264);
x_287 = lean_ctor_get(x_286, 0);
lean_inc(x_287);
lean_dec(x_286);
x_288 = lean_ctor_get(x_283, 0);
lean_inc(x_288);
x_289 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_287, x_288, x_3, x_6, x_7, x_8, x_284);
if (lean_obj_tag(x_289) == 0)
{
lean_object* x_290; lean_object* x_291; 
x_290 = lean_ctor_get(x_289, 1);
lean_inc(x_290);
lean_dec(x_289);
lean_inc(x_6);
x_291 = l_Lean_Compiler_LCNF_Simp_simp(x_261, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_290);
if (lean_obj_tag(x_291) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
x_293 = lean_ctor_get(x_291, 1);
lean_inc(x_293);
lean_dec(x_291);
x_294 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_260, x_6, x_293);
lean_dec(x_6);
lean_dec(x_260);
x_295 = lean_ctor_get(x_294, 1);
lean_inc(x_295);
if (lean_is_exclusive(x_294)) {
 lean_ctor_release(x_294, 0);
 lean_ctor_release(x_294, 1);
 x_296 = x_294;
} else {
 lean_dec_ref(x_294);
 x_296 = lean_box(0);
}
if (lean_is_scalar(x_259)) {
 x_297 = lean_alloc_ctor(0, 2, 0);
} else {
 x_297 = x_259;
}
lean_ctor_set(x_297, 0, x_283);
lean_ctor_set(x_297, 1, x_292);
x_298 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_298, 0, x_297);
if (lean_is_scalar(x_296)) {
 x_299 = lean_alloc_ctor(0, 2, 0);
} else {
 x_299 = x_296;
}
lean_ctor_set(x_299, 0, x_298);
lean_ctor_set(x_299, 1, x_295);
return x_299;
}
else
{
lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_283);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_6);
x_300 = lean_ctor_get(x_291, 0);
lean_inc(x_300);
x_301 = lean_ctor_get(x_291, 1);
lean_inc(x_301);
if (lean_is_exclusive(x_291)) {
 lean_ctor_release(x_291, 0);
 lean_ctor_release(x_291, 1);
 x_302 = x_291;
} else {
 lean_dec_ref(x_291);
 x_302 = lean_box(0);
}
if (lean_is_scalar(x_302)) {
 x_303 = lean_alloc_ctor(1, 2, 0);
} else {
 x_303 = x_302;
}
lean_ctor_set(x_303, 0, x_300);
lean_ctor_set(x_303, 1, x_301);
return x_303;
}
}
else
{
lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; 
lean_dec(x_283);
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_304 = lean_ctor_get(x_289, 0);
lean_inc(x_304);
x_305 = lean_ctor_get(x_289, 1);
lean_inc(x_305);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_306 = x_289;
} else {
 lean_dec_ref(x_289);
 x_306 = lean_box(0);
}
if (lean_is_scalar(x_306)) {
 x_307 = lean_alloc_ctor(1, 2, 0);
} else {
 x_307 = x_306;
}
lean_ctor_set(x_307, 0, x_304);
lean_ctor_set(x_307, 1, x_305);
return x_307;
}
}
else
{
lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; 
lean_dec(x_261);
lean_dec(x_260);
lean_dec(x_259);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_308 = lean_ctor_get(x_282, 0);
lean_inc(x_308);
x_309 = lean_ctor_get(x_282, 1);
lean_inc(x_309);
if (lean_is_exclusive(x_282)) {
 lean_ctor_release(x_282, 0);
 lean_ctor_release(x_282, 1);
 x_310 = x_282;
} else {
 lean_dec_ref(x_282);
 x_310 = lean_box(0);
}
if (lean_is_scalar(x_310)) {
 x_311 = lean_alloc_ctor(1, 2, 0);
} else {
 x_311 = x_310;
}
lean_ctor_set(x_311, 0, x_308);
lean_ctor_set(x_311, 1, x_309);
return x_311;
}
}
}
}
else
{
lean_object* x_312; lean_object* x_313; lean_object* x_314; 
lean_dec(x_225);
x_312 = lean_ctor_get(x_232, 1);
lean_inc(x_312);
lean_dec(x_232);
x_313 = lean_ctor_get(x_228, 0);
lean_inc(x_313);
lean_dec(x_228);
x_314 = l_Lean_Compiler_LCNF_Simp_simp(x_313, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_312);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_317 = x_314;
} else {
 lean_dec_ref(x_314);
 x_317 = lean_box(0);
}
x_318 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_318, 0, x_315);
if (lean_is_scalar(x_317)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_317;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_316);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
x_320 = lean_ctor_get(x_314, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_314, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_314)) {
 lean_ctor_release(x_314, 0);
 lean_ctor_release(x_314, 1);
 x_322 = x_314;
} else {
 lean_dec_ref(x_314);
 x_322 = lean_box(0);
}
if (lean_is_scalar(x_322)) {
 x_323 = lean_alloc_ctor(1, 2, 0);
} else {
 x_323 = x_322;
}
lean_ctor_set(x_323, 0, x_320);
lean_ctor_set(x_323, 1, x_321);
return x_323;
}
}
}
}
}
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; 
x_324 = lean_ctor_get(x_17, 0);
lean_inc(x_324);
lean_dec(x_17);
x_325 = l_Lean_Compiler_LCNF_Simp_findCtor_x3f___redArg(x_324, x_4, x_6, x_8, x_12);
lean_dec(x_324);
x_326 = lean_ctor_get(x_325, 0);
lean_inc(x_326);
if (lean_obj_tag(x_326) == 0)
{
lean_object* x_327; lean_object* x_328; lean_object* x_329; lean_object* x_330; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_327 = lean_ctor_get(x_325, 1);
lean_inc(x_327);
if (lean_is_exclusive(x_325)) {
 lean_ctor_release(x_325, 0);
 lean_ctor_release(x_325, 1);
 x_328 = x_325;
} else {
 lean_dec_ref(x_325);
 x_328 = lean_box(0);
}
x_329 = lean_box(0);
if (lean_is_scalar(x_328)) {
 x_330 = lean_alloc_ctor(0, 2, 0);
} else {
 x_330 = x_328;
}
lean_ctor_set(x_330, 0, x_329);
lean_ctor_set(x_330, 1, x_327);
return x_330;
}
else
{
lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; 
x_331 = lean_ctor_get(x_325, 1);
lean_inc(x_331);
lean_dec(x_325);
x_332 = lean_ctor_get(x_326, 0);
lean_inc(x_332);
if (lean_is_exclusive(x_326)) {
 lean_ctor_release(x_326, 0);
 x_333 = x_326;
} else {
 lean_dec_ref(x_326);
 x_333 = lean_box(0);
}
x_334 = l_Lean_Compiler_LCNF_Simp_CtorInfo_getName(x_332);
x_335 = l_Lean_Compiler_LCNF_CasesCore_extractAlt_x21(x_1, x_334);
x_336 = lean_ctor_get(x_335, 0);
lean_inc(x_336);
x_337 = lean_ctor_get(x_335, 1);
lean_inc(x_337);
lean_dec(x_335);
x_338 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_338, 0, x_337);
x_339 = l_Lean_Compiler_LCNF_eraseCode___redArg(x_338, x_6, x_331);
lean_dec(x_338);
x_340 = lean_ctor_get(x_339, 1);
lean_inc(x_340);
lean_dec(x_339);
x_341 = l_Lean_Compiler_LCNF_Simp_markSimplified___redArg(x_3, x_340);
if (lean_obj_tag(x_336) == 0)
{
if (lean_obj_tag(x_332) == 0)
{
lean_object* x_342; lean_object* x_343; lean_object* x_344; lean_object* x_345; lean_object* x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; size_t x_350; lean_object* x_351; size_t x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; 
x_342 = lean_ctor_get(x_341, 1);
lean_inc(x_342);
lean_dec(x_341);
x_343 = lean_ctor_get(x_336, 1);
lean_inc(x_343);
x_344 = lean_ctor_get(x_336, 2);
lean_inc(x_344);
lean_dec(x_336);
x_345 = lean_ctor_get(x_332, 0);
lean_inc(x_345);
x_346 = lean_ctor_get(x_332, 1);
lean_inc(x_346);
lean_dec(x_332);
x_347 = lean_ctor_get(x_345, 3);
lean_inc(x_347);
lean_dec(x_345);
x_348 = lean_array_get_size(x_346);
x_349 = l_Array_toSubarray___redArg(x_346, x_347, x_348);
x_350 = lean_array_size(x_343);
x_351 = lean_unsigned_to_nat(0u);
x_352 = lean_usize_of_nat(x_351);
x_353 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_343, x_350, x_352, x_349, x_3, x_342);
x_354 = lean_ctor_get(x_353, 1);
lean_inc(x_354);
lean_dec(x_353);
lean_inc(x_6);
x_355 = l_Lean_Compiler_LCNF_Simp_simp(x_344, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_354);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; 
x_356 = lean_ctor_get(x_355, 0);
lean_inc(x_356);
x_357 = lean_ctor_get(x_355, 1);
lean_inc(x_357);
lean_dec(x_355);
x_358 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_343, x_6, x_357);
lean_dec(x_6);
lean_dec(x_343);
x_359 = lean_ctor_get(x_358, 1);
lean_inc(x_359);
if (lean_is_exclusive(x_358)) {
 lean_ctor_release(x_358, 0);
 lean_ctor_release(x_358, 1);
 x_360 = x_358;
} else {
 lean_dec_ref(x_358);
 x_360 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_361 = lean_alloc_ctor(1, 1, 0);
} else {
 x_361 = x_333;
}
lean_ctor_set(x_361, 0, x_356);
if (lean_is_scalar(x_360)) {
 x_362 = lean_alloc_ctor(0, 2, 0);
} else {
 x_362 = x_360;
}
lean_ctor_set(x_362, 0, x_361);
lean_ctor_set(x_362, 1, x_359);
return x_362;
}
else
{
lean_object* x_363; lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_343);
lean_dec(x_333);
lean_dec(x_6);
x_363 = lean_ctor_get(x_355, 0);
lean_inc(x_363);
x_364 = lean_ctor_get(x_355, 1);
lean_inc(x_364);
if (lean_is_exclusive(x_355)) {
 lean_ctor_release(x_355, 0);
 lean_ctor_release(x_355, 1);
 x_365 = x_355;
} else {
 lean_dec_ref(x_355);
 x_365 = lean_box(0);
}
if (lean_is_scalar(x_365)) {
 x_366 = lean_alloc_ctor(1, 2, 0);
} else {
 x_366 = x_365;
}
lean_ctor_set(x_366, 0, x_363);
lean_ctor_set(x_366, 1, x_364);
return x_366;
}
}
else
{
lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_367 = lean_ctor_get(x_341, 1);
lean_inc(x_367);
if (lean_is_exclusive(x_341)) {
 lean_ctor_release(x_341, 0);
 lean_ctor_release(x_341, 1);
 x_368 = x_341;
} else {
 lean_dec_ref(x_341);
 x_368 = lean_box(0);
}
x_369 = lean_ctor_get(x_336, 1);
lean_inc(x_369);
x_370 = lean_ctor_get(x_336, 2);
lean_inc(x_370);
lean_dec(x_336);
x_371 = lean_ctor_get(x_332, 0);
lean_inc(x_371);
if (lean_is_exclusive(x_332)) {
 lean_ctor_release(x_332, 0);
 x_372 = x_332;
} else {
 lean_dec_ref(x_332);
 x_372 = lean_box(0);
}
x_373 = lean_unsigned_to_nat(0u);
x_374 = lean_nat_dec_eq(x_371, x_373);
if (x_374 == 1)
{
lean_object* x_375; 
lean_dec(x_372);
lean_dec(x_371);
lean_dec(x_369);
lean_dec(x_368);
x_375 = l_Lean_Compiler_LCNF_Simp_simp(x_370, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_367);
if (lean_obj_tag(x_375) == 0)
{
lean_object* x_376; lean_object* x_377; lean_object* x_378; lean_object* x_379; lean_object* x_380; 
x_376 = lean_ctor_get(x_375, 0);
lean_inc(x_376);
x_377 = lean_ctor_get(x_375, 1);
lean_inc(x_377);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_378 = x_375;
} else {
 lean_dec_ref(x_375);
 x_378 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_379 = lean_alloc_ctor(1, 1, 0);
} else {
 x_379 = x_333;
}
lean_ctor_set(x_379, 0, x_376);
if (lean_is_scalar(x_378)) {
 x_380 = lean_alloc_ctor(0, 2, 0);
} else {
 x_380 = x_378;
}
lean_ctor_set(x_380, 0, x_379);
lean_ctor_set(x_380, 1, x_377);
return x_380;
}
else
{
lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; 
lean_dec(x_333);
x_381 = lean_ctor_get(x_375, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_375, 1);
lean_inc(x_382);
if (lean_is_exclusive(x_375)) {
 lean_ctor_release(x_375, 0);
 lean_ctor_release(x_375, 1);
 x_383 = x_375;
} else {
 lean_dec_ref(x_375);
 x_383 = lean_box(0);
}
if (lean_is_scalar(x_383)) {
 x_384 = lean_alloc_ctor(1, 2, 0);
} else {
 x_384 = x_383;
}
lean_ctor_set(x_384, 0, x_381);
lean_ctor_set(x_384, 1, x_382);
return x_384;
}
}
else
{
lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; 
x_385 = lean_unsigned_to_nat(1u);
x_386 = lean_nat_sub(x_371, x_385);
lean_dec(x_371);
if (lean_is_scalar(x_372)) {
 x_387 = lean_alloc_ctor(0, 1, 0);
} else {
 x_387 = x_372;
 lean_ctor_set_tag(x_387, 0);
}
lean_ctor_set(x_387, 0, x_386);
x_388 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_388, 0, x_387);
x_389 = lean_mk_string_unchecked("_x", 2, 2);
x_390 = l_Lean_Name_mkStr1(x_389);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_391 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_388, x_390, x_5, x_6, x_7, x_8, x_367);
if (lean_obj_tag(x_391) == 0)
{
lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; 
x_392 = lean_ctor_get(x_391, 0);
lean_inc(x_392);
x_393 = lean_ctor_get(x_391, 1);
lean_inc(x_393);
lean_dec(x_391);
x_394 = l_Lean_Compiler_LCNF_instInhabitedParam;
x_395 = lean_array_get(x_394, x_369, x_373);
x_396 = lean_ctor_get(x_395, 0);
lean_inc(x_396);
lean_dec(x_395);
x_397 = lean_ctor_get(x_392, 0);
lean_inc(x_397);
x_398 = l_Lean_Compiler_LCNF_Simp_addFVarSubst___redArg(x_396, x_397, x_3, x_6, x_7, x_8, x_393);
if (lean_obj_tag(x_398) == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_398, 1);
lean_inc(x_399);
lean_dec(x_398);
lean_inc(x_6);
x_400 = l_Lean_Compiler_LCNF_Simp_simp(x_370, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_399);
if (lean_obj_tag(x_400) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; 
x_401 = lean_ctor_get(x_400, 0);
lean_inc(x_401);
x_402 = lean_ctor_get(x_400, 1);
lean_inc(x_402);
lean_dec(x_400);
x_403 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_369, x_6, x_402);
lean_dec(x_6);
lean_dec(x_369);
x_404 = lean_ctor_get(x_403, 1);
lean_inc(x_404);
if (lean_is_exclusive(x_403)) {
 lean_ctor_release(x_403, 0);
 lean_ctor_release(x_403, 1);
 x_405 = x_403;
} else {
 lean_dec_ref(x_403);
 x_405 = lean_box(0);
}
if (lean_is_scalar(x_368)) {
 x_406 = lean_alloc_ctor(0, 2, 0);
} else {
 x_406 = x_368;
}
lean_ctor_set(x_406, 0, x_392);
lean_ctor_set(x_406, 1, x_401);
if (lean_is_scalar(x_333)) {
 x_407 = lean_alloc_ctor(1, 1, 0);
} else {
 x_407 = x_333;
}
lean_ctor_set(x_407, 0, x_406);
if (lean_is_scalar(x_405)) {
 x_408 = lean_alloc_ctor(0, 2, 0);
} else {
 x_408 = x_405;
}
lean_ctor_set(x_408, 0, x_407);
lean_ctor_set(x_408, 1, x_404);
return x_408;
}
else
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_392);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_333);
lean_dec(x_6);
x_409 = lean_ctor_get(x_400, 0);
lean_inc(x_409);
x_410 = lean_ctor_get(x_400, 1);
lean_inc(x_410);
if (lean_is_exclusive(x_400)) {
 lean_ctor_release(x_400, 0);
 lean_ctor_release(x_400, 1);
 x_411 = x_400;
} else {
 lean_dec_ref(x_400);
 x_411 = lean_box(0);
}
if (lean_is_scalar(x_411)) {
 x_412 = lean_alloc_ctor(1, 2, 0);
} else {
 x_412 = x_411;
}
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_410);
return x_412;
}
}
else
{
lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; 
lean_dec(x_392);
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_413 = lean_ctor_get(x_398, 0);
lean_inc(x_413);
x_414 = lean_ctor_get(x_398, 1);
lean_inc(x_414);
if (lean_is_exclusive(x_398)) {
 lean_ctor_release(x_398, 0);
 lean_ctor_release(x_398, 1);
 x_415 = x_398;
} else {
 lean_dec_ref(x_398);
 x_415 = lean_box(0);
}
if (lean_is_scalar(x_415)) {
 x_416 = lean_alloc_ctor(1, 2, 0);
} else {
 x_416 = x_415;
}
lean_ctor_set(x_416, 0, x_413);
lean_ctor_set(x_416, 1, x_414);
return x_416;
}
}
else
{
lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; 
lean_dec(x_370);
lean_dec(x_369);
lean_dec(x_368);
lean_dec(x_333);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_417 = lean_ctor_get(x_391, 0);
lean_inc(x_417);
x_418 = lean_ctor_get(x_391, 1);
lean_inc(x_418);
if (lean_is_exclusive(x_391)) {
 lean_ctor_release(x_391, 0);
 lean_ctor_release(x_391, 1);
 x_419 = x_391;
} else {
 lean_dec_ref(x_391);
 x_419 = lean_box(0);
}
if (lean_is_scalar(x_419)) {
 x_420 = lean_alloc_ctor(1, 2, 0);
} else {
 x_420 = x_419;
}
lean_ctor_set(x_420, 0, x_417);
lean_ctor_set(x_420, 1, x_418);
return x_420;
}
}
}
}
else
{
lean_object* x_421; lean_object* x_422; lean_object* x_423; 
lean_dec(x_332);
x_421 = lean_ctor_get(x_341, 1);
lean_inc(x_421);
lean_dec(x_341);
x_422 = lean_ctor_get(x_336, 0);
lean_inc(x_422);
lean_dec(x_336);
x_423 = l_Lean_Compiler_LCNF_Simp_simp(x_422, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_421);
if (lean_obj_tag(x_423) == 0)
{
lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; 
x_424 = lean_ctor_get(x_423, 0);
lean_inc(x_424);
x_425 = lean_ctor_get(x_423, 1);
lean_inc(x_425);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_426 = x_423;
} else {
 lean_dec_ref(x_423);
 x_426 = lean_box(0);
}
if (lean_is_scalar(x_333)) {
 x_427 = lean_alloc_ctor(1, 1, 0);
} else {
 x_427 = x_333;
}
lean_ctor_set(x_427, 0, x_424);
if (lean_is_scalar(x_426)) {
 x_428 = lean_alloc_ctor(0, 2, 0);
} else {
 x_428 = x_426;
}
lean_ctor_set(x_428, 0, x_427);
lean_ctor_set(x_428, 1, x_425);
return x_428;
}
else
{
lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_333);
x_429 = lean_ctor_get(x_423, 0);
lean_inc(x_429);
x_430 = lean_ctor_get(x_423, 1);
lean_inc(x_430);
if (lean_is_exclusive(x_423)) {
 lean_ctor_release(x_423, 0);
 lean_ctor_release(x_423, 1);
 x_431 = x_423;
} else {
 lean_dec_ref(x_423);
 x_431 = lean_box(0);
}
if (lean_is_scalar(x_431)) {
 x_432 = lean_alloc_ctor(1, 2, 0);
} else {
 x_432 = x_431;
}
lean_ctor_set(x_432, 0, x_429);
lean_ctor_set(x_432, 1, x_430);
return x_432;
}
}
}
}
}
else
{
lean_object* x_433; uint8_t x_434; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_433 = l_Lean_Compiler_LCNF_mkReturnErased(x_5, x_6, x_7, x_8, x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
x_434 = !lean_is_exclusive(x_433);
if (x_434 == 0)
{
lean_object* x_435; lean_object* x_436; 
x_435 = lean_ctor_get(x_433, 0);
x_436 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_436, 0, x_435);
lean_ctor_set(x_433, 0, x_436);
return x_433;
}
else
{
lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; 
x_437 = lean_ctor_get(x_433, 0);
x_438 = lean_ctor_get(x_433, 1);
lean_inc(x_438);
lean_inc(x_437);
lean_dec(x_433);
x_439 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_439, 0, x_437);
x_440 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_440, 0, x_439);
lean_ctor_set(x_440, 1, x_438);
return x_440;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_8; 
x_7 = lean_array_get_size(x_3);
x_8 = lean_nat_dec_lt(x_2, x_7);
lean_dec(x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_2);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_6);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; uint8_t x_22; 
x_10 = lean_st_ref_get(x_4, x_6);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_array_fget(x_3, x_2);
x_14 = lean_ctor_get(x_13, 2);
lean_inc(x_14);
x_15 = lean_ctor_get(x_11, 0);
lean_inc(x_15);
lean_dec(x_11);
x_16 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_15, x_1, x_14);
lean_dec(x_15);
lean_inc(x_13);
x_17 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateParamImp___redArg(x_13, x_16, x_5, x_12);
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_17, 1);
lean_inc(x_19);
lean_dec(x_17);
x_20 = lean_ptr_addr(x_13);
lean_dec(x_13);
x_21 = lean_ptr_addr(x_18);
x_22 = lean_usize_dec_eq(x_20, x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_2, x_23);
x_25 = lean_array_fset(x_3, x_2, x_18);
lean_dec(x_2);
x_2 = x_24;
x_3 = x_25;
x_6 = x_19;
goto _start;
}
else
{
lean_object* x_27; lean_object* x_28; 
lean_dec(x_18);
x_27 = lean_unsigned_to_nat(1u);
x_28 = lean_nat_add(x_2, x_27);
lean_dec(x_2);
x_2 = x_28;
x_6 = x_19;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_2, x_3, x_5, x_8, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(0u);
x_12 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_1, x_11, x_2, x_4, x_7, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simpFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_10 = lean_st_ref_get(x_3, x_9);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_box(0);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
x_15 = lean_unbox(x_13);
x_16 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_15, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_12);
x_17 = lean_ctor_get(x_16, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_16, 1);
lean_inc(x_18);
lean_dec(x_16);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
lean_inc(x_6);
x_20 = l_Lean_Compiler_LCNF_Simp_simp(x_19, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_18);
if (lean_obj_tag(x_20) == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; lean_object* x_27; 
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_20, 1);
lean_inc(x_22);
lean_dec(x_20);
x_23 = lean_ctor_get(x_1, 3);
lean_inc(x_23);
x_24 = lean_ctor_get(x_11, 0);
lean_inc(x_24);
lean_dec(x_11);
x_25 = lean_unbox(x_13);
x_26 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_normExprImp_go(x_24, x_25, x_23);
lean_dec(x_24);
x_27 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_1, x_26, x_17, x_21, x_6, x_22);
lean_dec(x_6);
return x_27;
}
else
{
uint8_t x_28; 
lean_dec(x_17);
lean_dec(x_11);
lean_dec(x_6);
lean_dec(x_1);
x_28 = !lean_is_exclusive(x_20);
if (x_28 == 0)
{
return x_20;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_20, 0);
x_30 = lean_ctor_get(x_20, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_20);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Simp_inlineApp_x3f___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; lean_object* x_7; 
x_6 = lean_unbox(x_1);
lean_dec(x_1);
x_7 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___redArg(x_6, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normLetDecl___at___Lean_Compiler_LCNF_Simp_simp_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; 
x_5 = lean_unbox(x_1);
lean_dec(x_1);
x_6 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___redArg(x_5, x_2, x_3, x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normArgs___at___Lean_Compiler_LCNF_Simp_simp_spec__1(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_anyMUnsafe_any___at___Lean_Compiler_LCNF_Simp_simp_spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_Simp_simp_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Simp_simp___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
uint8_t x_14; lean_object* x_15; 
x_14 = lean_unbox(x_3);
lean_dec(x_3);
x_15 = l_Lean_Compiler_LCNF_Simp_simp___lam__0(x_1, x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_5);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
size_t x_7; size_t x_8; lean_object* x_9; 
x_7 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___redArg(x_1, x_7, x_8, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Simp_simpCasesOnCtor_x3f_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_15;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = lean_unbox(x_1);
lean_dec(x_1);
x_8 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___redArg(x_7, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_8;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
uint8_t x_12; lean_object* x_13; 
x_12 = lean_unbox(x_1);
lean_dec(x_1);
x_13 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0_spec__0(x_12, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_1);
lean_dec(x_1);
x_12 = l_Lean_Compiler_LCNF_normParams___at___Lean_Compiler_LCNF_Simp_simpFunDecl_spec__0(x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
lean_object* initialize_Lean_Compiler_ImplementedByAttr(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_ElimDead(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_AlphaEqv(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Bind(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_InlineProj(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_Used(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_SimpValue(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Simp_ConstantFold(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Simp_Main(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ImplementedByAttr(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_ElimDead(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_AlphaEqv(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Bind(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_FunDeclInfo(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineCandidate(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_InlineProj(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_Used(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_DefaultAlt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_SimpValue(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Simp_ConstantFold(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
