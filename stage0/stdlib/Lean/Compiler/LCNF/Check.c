// Lean compiler output
// Module: Lean.Compiler.LCNF.Check
// Imports: Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.PrettyPrinter Lean.Compiler.LCNF.CompatibleTypes
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
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_mkAppN(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withJp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_toExpr_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_check___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_FunDeclCore_getArity___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParam(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecl_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getLetDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqParam____x40_Lean_Compiler_LCNF_Basic___hyg_53_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkCases___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getBinderName___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t l_Lean_Compiler_LCNF_maybeTypeFormerType(lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkAppArgs___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams___boxed(lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__8(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__7(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Compiler_LCNF_instDecidableLePhase(uint8_t, uint8_t);
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getPhase___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_isCtorParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDeclCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetValue_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_Decl_check_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_isCtorParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1_spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_isErased(lean_object*);
lean_object* lean_usize_to_nat(size_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Compiler_LCNF_InferType_compatibleTypes(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParams___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDeclCore___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_isErasedCompatible_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes___redArg(lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getParam___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_foldlMUnsafe_fold(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withJp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withFVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getConfig___redArg(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_NameSet_contains(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Arg_toExpr(lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitFVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_check(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Compiler_LCNF_getFunDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__0(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkAppArgs(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_instantiateRevRangeArgs(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withFVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Data_Repr_0__Nat_reprFast(lean_object*);
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_instantiateRangeArgs_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkCases(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = l_Lean_Compiler_LCNF_getConfig___redArg(x_1, x_2);
x_4 = !lean_is_exclusive(x_3);
if (x_4 == 0)
{
lean_object* x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get_uint8(x_5, sizeof(void*)*3);
lean_dec(x_5);
x_7 = lean_box(x_6);
lean_ctor_set(x_3, 0, x_7);
return x_3;
}
else
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_ctor_get(x_3, 1);
lean_inc(x_9);
lean_inc(x_8);
lean_dec(x_3);
x_10 = lean_ctor_get_uint8(x_8, sizeof(void*)*3);
lean_dec(x_8);
x_11 = lean_box(x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_9);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Check_checkTypes___redArg(x_4, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_Check_checkTypes___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkTypes___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_Check_checkTypes(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_st_ref_get(x_2, x_9);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_12 = lean_ctor_get(x_10, 0);
x_13 = lean_ctor_get(x_3, 5);
x_14 = lean_ctor_get(x_8, 0);
lean_inc(x_14);
lean_dec(x_8);
x_15 = lean_ctor_get(x_12, 0);
lean_inc(x_15);
lean_dec(x_12);
x_16 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_15);
lean_dec(x_15);
x_17 = lean_ctor_get(x_3, 2);
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
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_14);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_16);
lean_ctor_set(x_27, 3, x_17);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_27);
lean_inc(x_13);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_13);
lean_ctor_set(x_28, 1, x_6);
lean_ctor_set_tag(x_10, 1);
lean_ctor_set(x_10, 0, x_28);
return x_10;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_29 = lean_ctor_get(x_10, 0);
x_30 = lean_ctor_get(x_10, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_10);
x_31 = lean_ctor_get(x_3, 5);
x_32 = lean_ctor_get(x_8, 0);
lean_inc(x_32);
lean_dec(x_8);
x_33 = lean_ctor_get(x_29, 0);
lean_inc(x_33);
lean_dec(x_29);
x_34 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_3, 2);
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_37);
x_38 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_38, 0, x_37);
lean_inc(x_37);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_37);
lean_inc(x_37);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_37);
lean_inc(x_37);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_37);
lean_inc(x_37);
x_42 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_42, 0, x_37);
x_43 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_43, 0, x_37);
x_44 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_44, 0, x_36);
lean_ctor_set(x_44, 1, x_36);
lean_ctor_set(x_44, 2, x_36);
lean_ctor_set(x_44, 3, x_38);
lean_ctor_set(x_44, 4, x_39);
lean_ctor_set(x_44, 5, x_40);
lean_ctor_set(x_44, 6, x_41);
lean_ctor_set(x_44, 7, x_42);
lean_ctor_set(x_44, 8, x_43);
lean_inc(x_35);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_32);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_34);
lean_ctor_set(x_45, 3, x_35);
lean_ctor_set_tag(x_6, 3);
lean_ctor_set(x_6, 1, x_1);
lean_ctor_set(x_6, 0, x_45);
lean_inc(x_31);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_31);
lean_ctor_set(x_46, 1, x_6);
x_47 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_30);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; 
x_48 = lean_ctor_get(x_6, 0);
x_49 = lean_ctor_get(x_6, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_6);
x_50 = lean_st_ref_get(x_2, x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_50, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_53 = x_50;
} else {
 lean_dec_ref(x_50);
 x_53 = lean_box(0);
}
x_54 = lean_ctor_get(x_3, 5);
x_55 = lean_ctor_get(x_48, 0);
lean_inc(x_55);
lean_dec(x_48);
x_56 = lean_ctor_get(x_51, 0);
lean_inc(x_56);
lean_dec(x_51);
x_57 = l_Lean_Compiler_LCNF_LCtx_toLocalContext(x_56);
lean_dec(x_56);
x_58 = lean_ctor_get(x_3, 2);
x_59 = lean_unsigned_to_nat(0u);
x_60 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_60);
x_61 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_61, 0, x_60);
lean_inc(x_60);
x_62 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_62, 0, x_60);
lean_inc(x_60);
x_63 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_63, 0, x_60);
lean_inc(x_60);
x_64 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_64, 0, x_60);
lean_inc(x_60);
x_65 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_65, 0, x_60);
x_66 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_66, 0, x_60);
x_67 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_67, 0, x_59);
lean_ctor_set(x_67, 1, x_59);
lean_ctor_set(x_67, 2, x_59);
lean_ctor_set(x_67, 3, x_61);
lean_ctor_set(x_67, 4, x_62);
lean_ctor_set(x_67, 5, x_63);
lean_ctor_set(x_67, 6, x_64);
lean_ctor_set(x_67, 7, x_65);
lean_ctor_set(x_67, 8, x_66);
lean_inc(x_58);
x_68 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_68, 0, x_55);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_68, 2, x_57);
lean_ctor_set(x_68, 3, x_58);
x_69 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_69, 0, x_68);
lean_ctor_set(x_69, 1, x_1);
lean_inc(x_54);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_54);
lean_ctor_set(x_70, 1, x_69);
if (lean_is_scalar(x_53)) {
 x_71 = lean_alloc_ctor(1, 2, 0);
} else {
 x_71 = x_53;
 lean_ctor_set_tag(x_71, 1);
}
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_52);
return x_71;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_2, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 1);
x_11 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_10, x_1);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; 
x_12 = l_Lean_Compiler_LCNF_getBinderName___redArg(x_1, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_mk_string_unchecked("invalid out of scope free variable ", 35, 35);
x_16 = l_Lean_stringToMessageData(x_15);
lean_dec(x_15);
x_17 = l_Lean_MessageData_ofName(x_13);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_16);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("", 0, 0);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_21, x_6, x_7, x_8, x_14);
return x_22;
}
else
{
uint8_t x_23; 
x_23 = !lean_is_exclusive(x_12);
if (x_23 == 0)
{
return x_12;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_12, 0);
x_25 = lean_ctor_get(x_12, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_12);
x_26 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
}
else
{
lean_object* x_27; uint8_t x_28; 
lean_dec(x_1);
x_27 = lean_ctor_get(x_11, 0);
lean_inc(x_27);
lean_dec(x_11);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_27, 1);
lean_dec(x_29);
x_30 = lean_ctor_get(x_27, 0);
lean_dec(x_30);
x_31 = lean_box(0);
lean_ctor_set(x_27, 1, x_9);
lean_ctor_set(x_27, 0, x_31);
return x_27;
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_dec(x_27);
x_32 = lean_box(0);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_9);
return x_33;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_isCtorParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 4)
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = l_Lean_getConstInfo___at_____private_Lean_Compiler_LCNF_Util_0__Lean_Compiler_LCNF_getCasesOnInductiveVal_x3f_spec__0(x_6, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
if (lean_obj_tag(x_8) == 6)
{
uint8_t x_9; 
x_9 = !lean_is_exclusive(x_7);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_7, 0);
lean_dec(x_10);
x_11 = lean_ctor_get(x_8, 0);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_11, 3);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_nat_dec_lt(x_2, x_12);
lean_dec(x_12);
x_14 = lean_box(x_13);
lean_ctor_set(x_7, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; 
x_15 = lean_ctor_get(x_7, 1);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_ctor_get(x_8, 0);
lean_inc(x_16);
lean_dec(x_8);
x_17 = lean_ctor_get(x_16, 3);
lean_inc(x_17);
lean_dec(x_16);
x_18 = lean_nat_dec_lt(x_2, x_17);
lean_dec(x_17);
x_19 = lean_box(x_18);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8_t x_21; 
lean_dec(x_8);
x_21 = !lean_is_exclusive(x_7);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
x_22 = lean_ctor_get(x_7, 0);
lean_dec(x_22);
x_23 = lean_box(0);
lean_ctor_set(x_7, 0, x_23);
return x_7;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_7, 1);
lean_inc(x_24);
lean_dec(x_7);
x_25 = lean_box(0);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_25);
lean_ctor_set(x_26, 1, x_24);
return x_26;
}
}
}
else
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_7);
if (x_27 == 0)
{
return x_7;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_7, 0);
x_29 = lean_ctor_get(x_7, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_7);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_isCtorParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Check_isCtorParam(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_117; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_19 = x_8;
} else {
 lean_dec_ref(x_8);
 x_19 = lean_box(0);
}
x_26 = l_Lean_Compiler_LCNF_Check_checkTypes___redArg(x_12, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
lean_inc(x_3);
x_30 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_17, x_7, x_2, x_3);
lean_dec(x_17);
x_117 = lean_unbox(x_27);
lean_dec(x_27);
if (x_117 == 0)
{
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = x_14;
x_103 = x_15;
x_104 = x_28;
goto block_116;
}
else
{
lean_object* x_118; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_118 = l_Lean_Compiler_LCNF_Arg_inferType(x_5, x_12, x_13, x_14, x_15, x_28);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_30);
lean_inc(x_119);
x_121 = l_Lean_Compiler_LCNF_InferType_compatibleTypes(x_119, x_30, x_11, x_12, x_13, x_14, x_15, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; size_t x_127; lean_object* x_128; size_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_mk_string_unchecked("type mismatch at LCNF application", 33, 33);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_array_size(x_3);
x_128 = lean_unsigned_to_nat(0u);
x_129 = lean_usize_of_nat(x_128);
x_130 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_toExpr_spec__0(x_127, x_129, x_3);
x_131 = l_Lean_mkAppN(x_4, x_130);
lean_dec(x_130);
x_132 = l_Lean_indentExpr(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_126);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("\nargument ", 10, 10);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Compiler_LCNF_Arg_toExpr(x_5);
x_138 = l_Lean_MessageData_ofExpr(x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked(" has type", 9, 9);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_indentExpr(x_119);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_indentExpr(x_30);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked("", 0, 0);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_152, x_13, x_14, x_15, x_124);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
return x_153;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_153);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
lean_object* x_158; 
lean_dec(x_119);
x_158 = lean_ctor_get(x_121, 1);
lean_inc(x_158);
lean_dec(x_121);
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = x_14;
x_103 = x_15;
x_104 = x_158;
goto block_116;
}
}
else
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_121);
if (x_159 == 0)
{
return x_121;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_121, 0);
x_161 = lean_ctor_get(x_121, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_121);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_118);
if (x_163 == 0)
{
return x_118;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_118, 0);
x_165 = lean_ctor_get(x_118, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_118);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
block_25:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
block_64:
{
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("invalid LCNF application", 24, 24);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_array_size(x_3);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_usize_of_nat(x_39);
x_41 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_instantiateRangeArgs_spec__0(x_38, x_40, x_3);
x_42 = l_Lean_mkAppN(x_4, x_41);
lean_dec(x_41);
x_43 = l_Lean_indentExpr(x_42);
if (lean_is_scalar(x_29)) {
 x_44 = lean_alloc_ctor(7, 2, 0);
} else {
 x_44 = x_29;
 lean_ctor_set_tag(x_44, 7);
}
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("\nargument", 9, 9);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Compiler_LCNF_Arg_toExpr(x_5);
x_49 = l_Lean_indentExpr(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_30);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_string_unchecked("\nmust be a free variable", 24, 24);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_58, x_33, x_32, x_34, x_31);
lean_dec(x_34);
lean_dec(x_32);
lean_dec(x_33);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = x_31;
goto block_25;
}
}
block_96:
{
if (x_72 == 0)
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
x_20 = x_73;
goto block_25;
}
case 1:
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_5, 0);
lean_inc(x_74);
lean_dec(x_5);
x_75 = l_Lean_Compiler_LCNF_Check_checkFVar(x_74, x_67, x_66, x_69, x_71, x_68, x_65, x_70, x_73);
lean_dec(x_70);
lean_dec(x_65);
lean_dec(x_68);
lean_dec(x_71);
lean_dec(x_69);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_20 = x_76;
goto block_25;
}
else
{
uint8_t x_77; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_69);
x_81 = l_Lean_Compiler_LCNF_getPhase___redArg(x_71, x_73);
lean_dec(x_71);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_4);
x_84 = l_Lean_Compiler_LCNF_Check_isCtorParam(x_4, x_2, x_65, x_70, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(1);
x_88 = lean_unbox(x_87);
x_89 = lean_unbox(x_82);
lean_dec(x_82);
x_90 = l_Lean_Compiler_LCNF_instDecidableLePhase(x_88, x_89);
if (x_90 == 0)
{
lean_dec(x_85);
x_31 = x_86;
x_32 = x_65;
x_33 = x_68;
x_34 = x_70;
x_35 = x_90;
goto block_64;
}
else
{
uint8_t x_91; 
x_91 = lean_unbox(x_85);
lean_dec(x_85);
x_31 = x_86;
x_32 = x_65;
x_33 = x_68;
x_34 = x_70;
x_35 = x_91;
goto block_64;
}
}
else
{
uint8_t x_92; 
lean_dec(x_82);
lean_dec(x_70);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
else
{
lean_dec(x_71);
lean_dec(x_70);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = x_73;
goto block_25;
}
}
block_116:
{
uint8_t x_105; 
lean_inc(x_30);
x_105 = l_Lean_Compiler_LCNF_maybeTypeFormerType(x_30);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_mk_empty_array_with_capacity(x_106);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_30);
x_108 = l_Lean_Compiler_LCNF_isErasedCompatible_go(x_30, x_107, x_100, x_101, x_102, x_103, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_unbox(x_109);
lean_dec(x_109);
x_65 = x_102;
x_66 = x_98;
x_67 = x_97;
x_68 = x_101;
x_69 = x_99;
x_70 = x_103;
x_71 = x_100;
x_72 = x_111;
x_73 = x_110;
goto block_96;
}
else
{
uint8_t x_112; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
x_65 = x_102;
x_66 = x_98;
x_67 = x_97;
x_68 = x_101;
x_69 = x_99;
x_70 = x_103;
x_71 = x_100;
x_72 = x_105;
x_73 = x_104;
goto block_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_nat_dec_lt(x_5, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_13);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_dec(x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_isErased(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_box(0);
x_40 = lean_array_fget(x_1, x_5);
x_41 = l_Lean_Expr_headBeta(x_36);
if (lean_obj_tag(x_41) == 7)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___lam__0(x_39, x_5, x_1, x_2, x_40, x_41, x_37, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_41);
x_14 = x_45;
goto block_31;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_inc(x_1);
x_46 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_41, x_37, x_5, x_1);
lean_dec(x_41);
x_47 = l_Lean_Expr_headBeta(x_46);
if (lean_obj_tag(x_47) == 7)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_51 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___lam__0(x_39, x_5, x_1, x_2, x_40, x_47, x_5, x_50, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_47);
x_14 = x_51;
goto block_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_37);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_13);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_36);
lean_ctor_set(x_59, 1, x_37);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_13);
return x_61;
}
}
block_31:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_4 = x_23;
x_5 = x_25;
x_13 = x_22;
goto _start;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; lean_object* x_73; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_117; 
x_17 = lean_ctor_get(x_8, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_8, 1);
lean_inc(x_18);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_19 = x_8;
} else {
 lean_dec_ref(x_8);
 x_19 = lean_box(0);
}
x_26 = l_Lean_Compiler_LCNF_Check_checkTypes___redArg(x_12, x_16);
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_26)) {
 lean_ctor_release(x_26, 0);
 lean_ctor_release(x_26, 1);
 x_29 = x_26;
} else {
 lean_dec_ref(x_26);
 x_29 = lean_box(0);
}
lean_inc(x_3);
x_30 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_17, x_7, x_2, x_3);
lean_dec(x_17);
x_117 = lean_unbox(x_27);
lean_dec(x_27);
if (x_117 == 0)
{
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = x_14;
x_103 = x_15;
x_104 = x_28;
goto block_116;
}
else
{
lean_object* x_118; 
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_5);
x_118 = l_Lean_Compiler_LCNF_Arg_inferType(x_5, x_12, x_13, x_14, x_15, x_28);
if (lean_obj_tag(x_118) == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_119 = lean_ctor_get(x_118, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_118, 1);
lean_inc(x_120);
lean_dec(x_118);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_30);
lean_inc(x_119);
x_121 = l_Lean_Compiler_LCNF_InferType_compatibleTypes(x_119, x_30, x_11, x_12, x_13, x_14, x_15, x_120);
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_122; uint8_t x_123; 
x_122 = lean_ctor_get(x_121, 0);
lean_inc(x_122);
x_123 = lean_unbox(x_122);
lean_dec(x_122);
if (x_123 == 0)
{
lean_object* x_124; lean_object* x_125; lean_object* x_126; size_t x_127; lean_object* x_128; size_t x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_1);
x_124 = lean_ctor_get(x_121, 1);
lean_inc(x_124);
lean_dec(x_121);
x_125 = lean_mk_string_unchecked("type mismatch at LCNF application", 33, 33);
x_126 = l_Lean_stringToMessageData(x_125);
lean_dec(x_125);
x_127 = lean_array_size(x_3);
x_128 = lean_unsigned_to_nat(0u);
x_129 = lean_usize_of_nat(x_128);
x_130 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_LetValue_toExpr_spec__0(x_127, x_129, x_3);
x_131 = l_Lean_mkAppN(x_4, x_130);
lean_dec(x_130);
x_132 = l_Lean_indentExpr(x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_126);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("\nargument ", 10, 10);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
x_136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_136, 0, x_133);
lean_ctor_set(x_136, 1, x_135);
x_137 = l_Lean_Compiler_LCNF_Arg_toExpr(x_5);
x_138 = l_Lean_MessageData_ofExpr(x_137);
x_139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_138);
x_140 = lean_mk_string_unchecked(" has type", 9, 9);
x_141 = l_Lean_stringToMessageData(x_140);
lean_dec(x_140);
x_142 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_142, 0, x_139);
lean_ctor_set(x_142, 1, x_141);
x_143 = l_Lean_indentExpr(x_119);
x_144 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
x_145 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_146 = l_Lean_stringToMessageData(x_145);
lean_dec(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_144);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_indentExpr(x_30);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_147);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked("", 0, 0);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_152, x_13, x_14, x_15, x_124);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_154 = !lean_is_exclusive(x_153);
if (x_154 == 0)
{
return x_153;
}
else
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; 
x_155 = lean_ctor_get(x_153, 0);
x_156 = lean_ctor_get(x_153, 1);
lean_inc(x_156);
lean_inc(x_155);
lean_dec(x_153);
x_157 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_157, 0, x_155);
lean_ctor_set(x_157, 1, x_156);
return x_157;
}
}
else
{
lean_object* x_158; 
lean_dec(x_119);
x_158 = lean_ctor_get(x_121, 1);
lean_inc(x_158);
lean_dec(x_121);
x_97 = x_9;
x_98 = x_10;
x_99 = x_11;
x_100 = x_12;
x_101 = x_13;
x_102 = x_14;
x_103 = x_15;
x_104 = x_158;
goto block_116;
}
}
else
{
uint8_t x_159; 
lean_dec(x_119);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_159 = !lean_is_exclusive(x_121);
if (x_159 == 0)
{
return x_121;
}
else
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
x_160 = lean_ctor_get(x_121, 0);
x_161 = lean_ctor_get(x_121, 1);
lean_inc(x_161);
lean_inc(x_160);
lean_dec(x_121);
x_162 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_162, 0, x_160);
lean_ctor_set(x_162, 1, x_161);
return x_162;
}
}
}
else
{
uint8_t x_163; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_13);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_163 = !lean_is_exclusive(x_118);
if (x_163 == 0)
{
return x_118;
}
else
{
lean_object* x_164; lean_object* x_165; lean_object* x_166; 
x_164 = lean_ctor_get(x_118, 0);
x_165 = lean_ctor_get(x_118, 1);
lean_inc(x_165);
lean_inc(x_164);
lean_dec(x_118);
x_166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_166, 0, x_164);
lean_ctor_set(x_166, 1, x_165);
return x_166;
}
}
}
block_25:
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
if (lean_is_scalar(x_19)) {
 x_21 = lean_alloc_ctor(0, 2, 0);
} else {
 x_21 = x_19;
}
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_21);
x_23 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_23, 0, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_20);
return x_24;
}
block_64:
{
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_60; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_1);
x_36 = lean_mk_string_unchecked("invalid LCNF application", 24, 24);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = lean_array_size(x_3);
x_39 = lean_unsigned_to_nat(0u);
x_40 = lean_usize_of_nat(x_39);
x_41 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_instantiateRangeArgs_spec__0(x_38, x_40, x_3);
x_42 = l_Lean_mkAppN(x_4, x_41);
lean_dec(x_41);
x_43 = l_Lean_indentExpr(x_42);
if (lean_is_scalar(x_29)) {
 x_44 = lean_alloc_ctor(7, 2, 0);
} else {
 x_44 = x_29;
 lean_ctor_set_tag(x_44, 7);
}
lean_ctor_set(x_44, 0, x_37);
lean_ctor_set(x_44, 1, x_43);
x_45 = lean_mk_string_unchecked("\nargument", 9, 9);
x_46 = l_Lean_stringToMessageData(x_45);
lean_dec(x_45);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_44);
lean_ctor_set(x_47, 1, x_46);
x_48 = l_Lean_Compiler_LCNF_Arg_toExpr(x_5);
x_49 = l_Lean_indentExpr(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = lean_mk_string_unchecked("\nhas type", 9, 9);
x_52 = l_Lean_stringToMessageData(x_51);
lean_dec(x_51);
x_53 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_53, 0, x_50);
lean_ctor_set(x_53, 1, x_52);
x_54 = l_Lean_indentExpr(x_30);
x_55 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_mk_string_unchecked("\nmust be a free variable", 24, 24);
x_57 = l_Lean_stringToMessageData(x_56);
lean_dec(x_56);
x_58 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_58, 0, x_55);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_58, x_33, x_31, x_32, x_34);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_33);
x_60 = !lean_is_exclusive(x_59);
if (x_60 == 0)
{
return x_59;
}
else
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_61 = lean_ctor_get(x_59, 0);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_inc(x_61);
lean_dec(x_59);
x_63 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_62);
return x_63;
}
}
else
{
lean_dec(x_33);
lean_dec(x_32);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = x_34;
goto block_25;
}
}
block_96:
{
if (x_72 == 0)
{
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
x_20 = x_73;
goto block_25;
}
case 1:
{
lean_object* x_74; lean_object* x_75; 
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_4);
lean_dec(x_3);
x_74 = lean_ctor_get(x_5, 0);
lean_inc(x_74);
lean_dec(x_5);
x_75 = l_Lean_Compiler_LCNF_Check_checkFVar(x_74, x_70, x_71, x_65, x_68, x_69, x_66, x_67, x_73);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_65);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_20 = x_76;
goto block_25;
}
else
{
uint8_t x_77; 
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_1);
x_77 = !lean_is_exclusive(x_75);
if (x_77 == 0)
{
return x_75;
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_78 = lean_ctor_get(x_75, 0);
x_79 = lean_ctor_get(x_75, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_75);
x_80 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_80, 0, x_78);
lean_ctor_set(x_80, 1, x_79);
return x_80;
}
}
}
default: 
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_65);
x_81 = l_Lean_Compiler_LCNF_getPhase___redArg(x_68, x_73);
lean_dec(x_68);
x_82 = lean_ctor_get(x_81, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_81, 1);
lean_inc(x_83);
lean_dec(x_81);
lean_inc(x_4);
x_84 = l_Lean_Compiler_LCNF_Check_isCtorParam(x_4, x_2, x_66, x_67, x_83);
if (lean_obj_tag(x_84) == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint8_t x_88; uint8_t x_89; uint8_t x_90; 
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_84, 1);
lean_inc(x_86);
lean_dec(x_84);
x_87 = lean_box(1);
x_88 = lean_unbox(x_87);
x_89 = lean_unbox(x_82);
lean_dec(x_82);
x_90 = l_Lean_Compiler_LCNF_instDecidableLePhase(x_88, x_89);
if (x_90 == 0)
{
lean_dec(x_85);
x_31 = x_66;
x_32 = x_67;
x_33 = x_69;
x_34 = x_86;
x_35 = x_90;
goto block_64;
}
else
{
uint8_t x_91; 
x_91 = lean_unbox(x_85);
lean_dec(x_85);
x_31 = x_66;
x_32 = x_67;
x_33 = x_69;
x_34 = x_86;
x_35 = x_91;
goto block_64;
}
}
else
{
uint8_t x_92; 
lean_dec(x_82);
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
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
}
else
{
lean_dec(x_69);
lean_dec(x_68);
lean_dec(x_67);
lean_dec(x_66);
lean_dec(x_65);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_20 = x_73;
goto block_25;
}
}
block_116:
{
uint8_t x_105; 
lean_inc(x_30);
x_105 = l_Lean_Compiler_LCNF_maybeTypeFormerType(x_30);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_unsigned_to_nat(0u);
x_107 = lean_mk_empty_array_with_capacity(x_106);
lean_inc(x_103);
lean_inc(x_102);
lean_inc(x_101);
lean_inc(x_100);
lean_inc(x_30);
x_108 = l_Lean_Compiler_LCNF_isErasedCompatible_go(x_30, x_107, x_100, x_101, x_102, x_103, x_104);
if (lean_obj_tag(x_108) == 0)
{
lean_object* x_109; lean_object* x_110; uint8_t x_111; 
x_109 = lean_ctor_get(x_108, 0);
lean_inc(x_109);
x_110 = lean_ctor_get(x_108, 1);
lean_inc(x_110);
lean_dec(x_108);
x_111 = lean_unbox(x_109);
lean_dec(x_109);
x_65 = x_99;
x_66 = x_102;
x_67 = x_103;
x_68 = x_100;
x_69 = x_101;
x_70 = x_97;
x_71 = x_98;
x_72 = x_111;
x_73 = x_110;
goto block_96;
}
else
{
uint8_t x_112; 
lean_dec(x_103);
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_100);
lean_dec(x_99);
lean_dec(x_30);
lean_dec(x_29);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_112 = !lean_is_exclusive(x_108);
if (x_112 == 0)
{
return x_108;
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
x_113 = lean_ctor_get(x_108, 0);
x_114 = lean_ctor_get(x_108, 1);
lean_inc(x_114);
lean_inc(x_113);
lean_dec(x_108);
x_115 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_115, 0, x_113);
lean_ctor_set(x_115, 1, x_114);
return x_115;
}
}
}
else
{
x_65 = x_99;
x_66 = x_102;
x_67 = x_103;
x_68 = x_100;
x_69 = x_101;
x_70 = x_97;
x_71 = x_98;
x_72 = x_105;
x_73 = x_104;
goto block_96;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; lean_object* x_32; uint8_t x_33; 
x_32 = lean_ctor_get(x_3, 1);
x_33 = lean_nat_dec_lt(x_5, x_32);
if (x_33 == 0)
{
lean_object* x_34; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_4);
lean_ctor_set(x_34, 1, x_13);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_4, 1);
lean_inc(x_35);
lean_dec(x_4);
x_36 = lean_ctor_get(x_35, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_35, 1);
lean_inc(x_37);
lean_dec(x_35);
x_38 = l_Lean_Expr_isErased(x_36);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_box(0);
x_40 = lean_array_fget(x_1, x_5);
x_41 = l_Lean_Expr_headBeta(x_36);
if (lean_obj_tag(x_41) == 7)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 2);
lean_inc(x_43);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_42);
lean_ctor_set(x_44, 1, x_43);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
x_45 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___lam__0(x_39, x_5, x_1, x_2, x_40, x_41, x_37, x_44, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_41);
x_14 = x_45;
goto block_31;
}
else
{
lean_object* x_46; lean_object* x_47; 
lean_inc(x_1);
x_46 = l_Lean_Compiler_LCNF_instantiateRevRangeArgs(x_41, x_37, x_5, x_1);
lean_dec(x_41);
x_47 = l_Lean_Expr_headBeta(x_46);
if (lean_obj_tag(x_47) == 7)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_37);
x_48 = lean_ctor_get(x_47, 1);
lean_inc(x_48);
x_49 = lean_ctor_get(x_47, 2);
lean_inc(x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_2);
lean_inc(x_1);
lean_inc(x_5);
x_51 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___lam__0(x_39, x_5, x_1, x_2, x_40, x_47, x_5, x_50, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_47);
x_14 = x_51;
goto block_31;
}
else
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; 
lean_dec(x_40);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_52 = lean_box(0);
x_53 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_53, 0, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_47);
lean_ctor_set(x_54, 1, x_37);
x_55 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_55, 0, x_53);
lean_ctor_set(x_55, 1, x_54);
x_56 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_13);
return x_56;
}
}
}
else
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_57 = lean_box(0);
x_58 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_58, 0, x_57);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_36);
lean_ctor_set(x_59, 1, x_37);
x_60 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_59);
x_61 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_61, 0, x_60);
lean_ctor_set(x_61, 1, x_13);
return x_61;
}
}
block_31:
{
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_16 = !lean_is_exclusive(x_14);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; 
x_17 = lean_ctor_get(x_14, 0);
lean_dec(x_17);
x_18 = lean_ctor_get(x_15, 0);
lean_inc(x_18);
lean_dec(x_15);
lean_ctor_set(x_14, 0, x_18);
return x_14;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_14, 1);
lean_inc(x_19);
lean_dec(x_14);
x_20 = lean_ctor_get(x_15, 0);
lean_inc(x_20);
lean_dec(x_15);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_14, 1);
lean_inc(x_22);
lean_dec(x_14);
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_3, 2);
x_25 = lean_nat_add(x_5, x_24);
lean_dec(x_5);
x_26 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg(x_1, x_2, x_3, x_23, x_25, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_22);
return x_26;
}
}
else
{
uint8_t x_27; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_27 = !lean_is_exclusive(x_14);
if (x_27 == 0)
{
return x_14;
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_14, 0);
x_29 = lean_ctor_get(x_14, 1);
lean_inc(x_29);
lean_inc(x_28);
lean_dec(x_14);
x_30 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_29);
return x_30;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkAppArgs(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_inferType(x_1, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(0u);
x_15 = lean_array_get_size(x_2);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_17, 2, x_16);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_12);
lean_ctor_set(x_19, 1, x_14);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg(x_2, x_1, x_17, x_20, x_14, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
lean_object* x_22; lean_object* x_23; 
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
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_21);
if (x_36 == 0)
{
return x_21;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_21, 0);
x_38 = lean_ctor_get(x_21, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_21);
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
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_2);
lean_dec(x_1);
x_40 = !lean_is_exclusive(x_11);
if (x_40 == 0)
{
return x_11;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_41 = lean_ctor_get(x_11, 0);
x_42 = lean_ctor_get(x_11, 1);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_11);
x_43 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
return x_43;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_2);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
lean_object* x_14; 
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_3);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15) {
_start:
{
lean_object* x_16; 
x_16 = l_Std_Range_forIn_x27_loop___at___Lean_Compiler_LCNF_Check_checkAppArgs_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_3);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkAppArgs___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Check_checkAppArgs(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
lean_dec(x_1);
x_11 = l_Lean_Compiler_LCNF_Check_checkFVar(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_11;
}
case 3:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_1, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_ctor_get(x_1, 2);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_Expr_const___override(x_12, x_13);
x_16 = l_Lean_Compiler_LCNF_Check_checkAppArgs(x_15, x_14, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_16;
}
case 4:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
lean_inc(x_17);
x_19 = l_Lean_Compiler_LCNF_Check_checkFVar(x_17, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_21 = l_Lean_Expr_fvar___override(x_17);
x_22 = l_Lean_Compiler_LCNF_Check_checkAppArgs(x_21, x_18, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_20);
return x_22;
}
else
{
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_19;
}
}
default: 
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_9);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkLetValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_7, x_1);
if (lean_obj_tag(x_8) == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_9 = lean_mk_string_unchecked("invalid jump to out of scope join point `", 41, 41);
x_10 = l_Lean_stringToMessageData(x_9);
lean_dec(x_9);
x_11 = l_Lean_Expr_fvar___override(x_1);
x_12 = l_Lean_MessageData_ofExpr(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_10);
lean_ctor_set(x_13, 1, x_12);
x_14 = lean_mk_string_unchecked("`", 1, 1);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_16, x_3, x_4, x_5, x_6);
return x_17;
}
else
{
lean_object* x_18; uint8_t x_19; 
lean_dec(x_1);
x_18 = lean_ctor_get(x_8, 0);
lean_inc(x_18);
lean_dec(x_8);
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_18, 1);
lean_dec(x_20);
x_21 = lean_ctor_get(x_18, 0);
lean_dec(x_21);
x_22 = lean_box(0);
lean_ctor_set(x_18, 1, x_6);
lean_ctor_set(x_18, 0, x_22);
return x_18;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_18);
x_23 = lean_box(0);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_6);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg(x_1, x_2, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkJpInScope___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkJpInScope(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_Compiler_LCNF_getParam___redArg(x_6, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_7) == 0)
{
uint8_t x_8; 
x_8 = !lean_is_exclusive(x_7);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_7, 0);
x_10 = lean_ctor_get(x_7, 1);
x_11 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqParam____x40_Lean_Compiler_LCNF_Basic___hyg_53_(x_1, x_9);
lean_dec(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
lean_free_object(x_7);
x_12 = lean_mk_string_unchecked("LCNF parameter mismatch at `", 28, 28);
x_13 = l_Lean_stringToMessageData(x_12);
lean_dec(x_12);
x_14 = lean_ctor_get(x_1, 1);
lean_inc(x_14);
lean_dec(x_1);
x_15 = l_Lean_MessageData_ofName(x_14);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_mk_string_unchecked("`, does not value in local context", 34, 34);
x_18 = l_Lean_stringToMessageData(x_17);
lean_dec(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_19, x_2, x_3, x_4, x_10);
return x_20;
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_box(0);
lean_ctor_set(x_7, 0, x_21);
return x_7;
}
}
else
{
lean_object* x_22; lean_object* x_23; uint8_t x_24; 
x_22 = lean_ctor_get(x_7, 0);
x_23 = lean_ctor_get(x_7, 1);
lean_inc(x_23);
lean_inc(x_22);
lean_dec(x_7);
x_24 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqParam____x40_Lean_Compiler_LCNF_Basic___hyg_53_(x_1, x_22);
lean_dec(x_22);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_mk_string_unchecked("LCNF parameter mismatch at `", 28, 28);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_ctor_get(x_1, 1);
lean_inc(x_27);
lean_dec(x_1);
x_28 = l_Lean_MessageData_ofName(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_mk_string_unchecked("`, does not value in local context", 34, 34);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_31);
x_33 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_32, x_2, x_3, x_4, x_23);
return x_33;
}
else
{
lean_object* x_34; lean_object* x_35; 
lean_dec(x_1);
x_34 = lean_box(0);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_23);
return x_35;
}
}
}
else
{
uint8_t x_36; 
lean_dec(x_1);
x_36 = !lean_is_exclusive(x_7);
if (x_36 == 0)
{
return x_7;
}
else
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_7, 0);
x_38 = lean_ctor_get(x_7, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_7);
x_39 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_39, 0, x_37);
lean_ctor_set(x_39, 1, x_38);
return x_39;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkParam___redArg(x_1, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Compiler_LCNF_Check_checkParam___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParam___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkParam(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_eq(x_2, x_3);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_4);
x_10 = lean_array_uget(x_1, x_2);
x_11 = l_Lean_Compiler_LCNF_Check_checkParam___redArg(x_10, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; size_t x_15; size_t x_16; 
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_11, 1);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_unsigned_to_nat(1u);
x_15 = lean_usize_of_nat(x_14);
x_16 = lean_usize_add(x_2, x_15);
x_2 = x_16;
x_4 = x_12;
x_8 = x_13;
goto _start;
}
else
{
return x_11;
}
}
else
{
lean_object* x_18; 
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_4);
lean_ctor_set(x_18, 1, x_8);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___redArg(x_1, x_2, x_3, x_4, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_get_size(x_1);
x_12 = lean_box(0);
x_13 = lean_nat_dec_lt(x_10, x_11);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_11);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_9);
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
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_12);
lean_ctor_set(x_16, 1, x_9);
return x_16;
}
else
{
size_t x_17; size_t x_18; lean_object* x_19; 
x_17 = lean_usize_of_nat(x_10);
x_18 = lean_usize_of_nat(x_11);
lean_dec(x_11);
x_19 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___redArg(x_1, x_17, x_18, x_12, x_6, x_7, x_8, x_9);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___redArg(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkParams_spec__0(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkParams___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkParams(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_49; lean_object* x_50; 
x_49 = lean_ctor_get(x_1, 3);
lean_inc(x_49);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_50 = l_Lean_Compiler_LCNF_Check_checkLetValue(x_49, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_50) == 0)
{
uint8_t x_51; 
x_51 = !lean_is_exclusive(x_50);
if (x_51 == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_52 = lean_ctor_get(x_50, 1);
x_53 = lean_ctor_get(x_50, 0);
lean_dec(x_53);
x_54 = l_Lean_Compiler_LCNF_Check_checkTypes___redArg(x_5, x_52);
x_55 = lean_ctor_get(x_54, 0);
lean_inc(x_55);
x_56 = lean_unbox(x_55);
lean_dec(x_55);
if (x_56 == 0)
{
lean_object* x_57; 
lean_free_object(x_50);
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
x_57 = lean_ctor_get(x_54, 1);
lean_inc(x_57);
lean_dec(x_54);
x_10 = x_6;
x_11 = x_7;
x_12 = x_8;
x_13 = x_57;
goto block_48;
}
else
{
uint8_t x_58; 
x_58 = !lean_is_exclusive(x_54);
if (x_58 == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_54, 1);
x_60 = lean_ctor_get(x_54, 0);
lean_dec(x_60);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_61 = l_Lean_Compiler_LCNF_LetValue_inferType(x_49, x_5, x_6, x_7, x_8, x_59);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_61, 1);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_ctor_get(x_1, 2);
lean_inc(x_64);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_62);
lean_inc(x_64);
x_65 = l_Lean_Compiler_LCNF_InferType_compatibleTypes(x_64, x_62, x_4, x_5, x_6, x_7, x_8, x_63);
if (lean_obj_tag(x_65) == 0)
{
lean_object* x_66; uint8_t x_67; 
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_unbox(x_66);
lean_dec(x_66);
if (x_67 == 0)
{
lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
lean_dec(x_65);
x_69 = lean_mk_string_unchecked("type mismatch at `", 18, 18);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_ctor_get(x_1, 1);
lean_inc(x_71);
lean_dec(x_1);
x_72 = l_Lean_MessageData_ofName(x_71);
lean_ctor_set_tag(x_54, 7);
lean_ctor_set(x_54, 1, x_72);
lean_ctor_set(x_54, 0, x_70);
x_73 = lean_mk_string_unchecked("`, value has type", 17, 17);
x_74 = l_Lean_stringToMessageData(x_73);
lean_dec(x_73);
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_74);
lean_ctor_set(x_50, 0, x_54);
x_75 = l_Lean_indentExpr(x_62);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_50);
lean_ctor_set(x_76, 1, x_75);
x_77 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_78 = l_Lean_stringToMessageData(x_77);
lean_dec(x_77);
x_79 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_79, 0, x_76);
lean_ctor_set(x_79, 1, x_78);
x_80 = l_Lean_indentExpr(x_64);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = lean_mk_string_unchecked("", 0, 0);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
x_84 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_84, 0, x_81);
lean_ctor_set(x_84, 1, x_83);
x_85 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_84, x_6, x_7, x_8, x_68);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_85;
}
else
{
lean_object* x_86; 
lean_dec(x_64);
lean_dec(x_62);
lean_free_object(x_54);
lean_free_object(x_50);
x_86 = lean_ctor_get(x_65, 1);
lean_inc(x_86);
lean_dec(x_65);
x_10 = x_6;
x_11 = x_7;
x_12 = x_8;
x_13 = x_86;
goto block_48;
}
}
else
{
uint8_t x_87; 
lean_dec(x_64);
lean_dec(x_62);
lean_free_object(x_54);
lean_free_object(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_65);
if (x_87 == 0)
{
return x_65;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_65, 0);
x_89 = lean_ctor_get(x_65, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_65);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
else
{
uint8_t x_91; 
lean_free_object(x_54);
lean_free_object(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_91 = !lean_is_exclusive(x_61);
if (x_91 == 0)
{
return x_61;
}
else
{
lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_92 = lean_ctor_get(x_61, 0);
x_93 = lean_ctor_get(x_61, 1);
lean_inc(x_93);
lean_inc(x_92);
lean_dec(x_61);
x_94 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
return x_94;
}
}
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_ctor_get(x_54, 1);
lean_inc(x_95);
lean_dec(x_54);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_96 = l_Lean_Compiler_LCNF_LetValue_inferType(x_49, x_5, x_6, x_7, x_8, x_95);
if (lean_obj_tag(x_96) == 0)
{
lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_97 = lean_ctor_get(x_96, 0);
lean_inc(x_97);
x_98 = lean_ctor_get(x_96, 1);
lean_inc(x_98);
lean_dec(x_96);
x_99 = lean_ctor_get(x_1, 2);
lean_inc(x_99);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_97);
lean_inc(x_99);
x_100 = l_Lean_Compiler_LCNF_InferType_compatibleTypes(x_99, x_97, x_4, x_5, x_6, x_7, x_8, x_98);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_unbox(x_101);
lean_dec(x_101);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_103 = lean_ctor_get(x_100, 1);
lean_inc(x_103);
lean_dec(x_100);
x_104 = lean_mk_string_unchecked("type mismatch at `", 18, 18);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = lean_ctor_get(x_1, 1);
lean_inc(x_106);
lean_dec(x_1);
x_107 = l_Lean_MessageData_ofName(x_106);
x_108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_107);
x_109 = lean_mk_string_unchecked("`, value has type", 17, 17);
x_110 = l_Lean_stringToMessageData(x_109);
lean_dec(x_109);
lean_ctor_set_tag(x_50, 7);
lean_ctor_set(x_50, 1, x_110);
lean_ctor_set(x_50, 0, x_108);
x_111 = l_Lean_indentExpr(x_97);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_50);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_114 = l_Lean_stringToMessageData(x_113);
lean_dec(x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_112);
lean_ctor_set(x_115, 1, x_114);
x_116 = l_Lean_indentExpr(x_99);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = lean_mk_string_unchecked("", 0, 0);
x_119 = l_Lean_stringToMessageData(x_118);
lean_dec(x_118);
x_120 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_120, 0, x_117);
lean_ctor_set(x_120, 1, x_119);
x_121 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_120, x_6, x_7, x_8, x_103);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_121;
}
else
{
lean_object* x_122; 
lean_dec(x_99);
lean_dec(x_97);
lean_free_object(x_50);
x_122 = lean_ctor_get(x_100, 1);
lean_inc(x_122);
lean_dec(x_100);
x_10 = x_6;
x_11 = x_7;
x_12 = x_8;
x_13 = x_122;
goto block_48;
}
}
else
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; 
lean_dec(x_99);
lean_dec(x_97);
lean_free_object(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_123 = lean_ctor_get(x_100, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_100, 1);
lean_inc(x_124);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_125 = x_100;
} else {
 lean_dec_ref(x_100);
 x_125 = lean_box(0);
}
if (lean_is_scalar(x_125)) {
 x_126 = lean_alloc_ctor(1, 2, 0);
} else {
 x_126 = x_125;
}
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_124);
return x_126;
}
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; 
lean_free_object(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_127 = lean_ctor_get(x_96, 0);
lean_inc(x_127);
x_128 = lean_ctor_get(x_96, 1);
lean_inc(x_128);
if (lean_is_exclusive(x_96)) {
 lean_ctor_release(x_96, 0);
 lean_ctor_release(x_96, 1);
 x_129 = x_96;
} else {
 lean_dec_ref(x_96);
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
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; uint8_t x_134; 
x_131 = lean_ctor_get(x_50, 1);
lean_inc(x_131);
lean_dec(x_50);
x_132 = l_Lean_Compiler_LCNF_Check_checkTypes___redArg(x_5, x_131);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_unbox(x_133);
lean_dec(x_133);
if (x_134 == 0)
{
lean_object* x_135; 
lean_dec(x_49);
lean_dec(x_5);
lean_dec(x_4);
x_135 = lean_ctor_get(x_132, 1);
lean_inc(x_135);
lean_dec(x_132);
x_10 = x_6;
x_11 = x_7;
x_12 = x_8;
x_13 = x_135;
goto block_48;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_132, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_137 = x_132;
} else {
 lean_dec_ref(x_132);
 x_137 = lean_box(0);
}
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
x_138 = l_Lean_Compiler_LCNF_LetValue_inferType(x_49, x_5, x_6, x_7, x_8, x_136);
if (lean_obj_tag(x_138) == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; 
x_139 = lean_ctor_get(x_138, 0);
lean_inc(x_139);
x_140 = lean_ctor_get(x_138, 1);
lean_inc(x_140);
lean_dec(x_138);
x_141 = lean_ctor_get(x_1, 2);
lean_inc(x_141);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_139);
lean_inc(x_141);
x_142 = l_Lean_Compiler_LCNF_InferType_compatibleTypes(x_141, x_139, x_4, x_5, x_6, x_7, x_8, x_140);
if (lean_obj_tag(x_142) == 0)
{
lean_object* x_143; uint8_t x_144; 
x_143 = lean_ctor_get(x_142, 0);
lean_inc(x_143);
x_144 = lean_unbox(x_143);
lean_dec(x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_145 = lean_ctor_get(x_142, 1);
lean_inc(x_145);
lean_dec(x_142);
x_146 = lean_mk_string_unchecked("type mismatch at `", 18, 18);
x_147 = l_Lean_stringToMessageData(x_146);
lean_dec(x_146);
x_148 = lean_ctor_get(x_1, 1);
lean_inc(x_148);
lean_dec(x_1);
x_149 = l_Lean_MessageData_ofName(x_148);
if (lean_is_scalar(x_137)) {
 x_150 = lean_alloc_ctor(7, 2, 0);
} else {
 x_150 = x_137;
 lean_ctor_set_tag(x_150, 7);
}
lean_ctor_set(x_150, 0, x_147);
lean_ctor_set(x_150, 1, x_149);
x_151 = lean_mk_string_unchecked("`, value has type", 17, 17);
x_152 = l_Lean_stringToMessageData(x_151);
lean_dec(x_151);
x_153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_153, 0, x_150);
lean_ctor_set(x_153, 1, x_152);
x_154 = l_Lean_indentExpr(x_139);
x_155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_155, 0, x_153);
lean_ctor_set(x_155, 1, x_154);
x_156 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_157 = l_Lean_stringToMessageData(x_156);
lean_dec(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_155);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_indentExpr(x_141);
x_160 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_160, 0, x_158);
lean_ctor_set(x_160, 1, x_159);
x_161 = lean_mk_string_unchecked("", 0, 0);
x_162 = l_Lean_stringToMessageData(x_161);
lean_dec(x_161);
x_163 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_163, 0, x_160);
lean_ctor_set(x_163, 1, x_162);
x_164 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_163, x_6, x_7, x_8, x_145);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_164;
}
else
{
lean_object* x_165; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
x_165 = lean_ctor_get(x_142, 1);
lean_inc(x_165);
lean_dec(x_142);
x_10 = x_6;
x_11 = x_7;
x_12 = x_8;
x_13 = x_165;
goto block_48;
}
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; 
lean_dec(x_141);
lean_dec(x_139);
lean_dec(x_137);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_166 = lean_ctor_get(x_142, 0);
lean_inc(x_166);
x_167 = lean_ctor_get(x_142, 1);
lean_inc(x_167);
if (lean_is_exclusive(x_142)) {
 lean_ctor_release(x_142, 0);
 lean_ctor_release(x_142, 1);
 x_168 = x_142;
} else {
 lean_dec_ref(x_142);
 x_168 = lean_box(0);
}
if (lean_is_scalar(x_168)) {
 x_169 = lean_alloc_ctor(1, 2, 0);
} else {
 x_169 = x_168;
}
lean_ctor_set(x_169, 0, x_166);
lean_ctor_set(x_169, 1, x_167);
return x_169;
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; 
lean_dec(x_137);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_170 = lean_ctor_get(x_138, 0);
lean_inc(x_170);
x_171 = lean_ctor_get(x_138, 1);
lean_inc(x_171);
if (lean_is_exclusive(x_138)) {
 lean_ctor_release(x_138, 0);
 lean_ctor_release(x_138, 1);
 x_172 = x_138;
} else {
 lean_dec_ref(x_138);
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
}
}
else
{
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_50;
}
block_48:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_1, 0);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_getLetDecl___redArg(x_14, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get(x_15, 1);
x_19 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(x_1, x_17);
lean_dec(x_17);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_free_object(x_15);
x_20 = lean_mk_string_unchecked("LCNF let declaration mismatch at `", 34, 34);
x_21 = l_Lean_stringToMessageData(x_20);
lean_dec(x_20);
x_22 = lean_ctor_get(x_1, 1);
lean_inc(x_22);
lean_dec(x_1);
x_23 = l_Lean_MessageData_ofName(x_22);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_21);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_mk_string_unchecked("`, does not match value in local context", 40, 40);
x_26 = l_Lean_stringToMessageData(x_25);
lean_dec(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_27, x_10, x_11, x_12, x_18);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_28;
}
else
{
lean_object* x_29; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_29 = lean_box(0);
lean_ctor_set(x_15, 0, x_29);
return x_15;
}
}
else
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_30 = lean_ctor_get(x_15, 0);
x_31 = lean_ctor_get(x_15, 1);
lean_inc(x_31);
lean_inc(x_30);
lean_dec(x_15);
x_32 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_beqLetDecl____x40_Lean_Compiler_LCNF_Basic___hyg_1722_(x_1, x_30);
lean_dec(x_30);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_33 = lean_mk_string_unchecked("LCNF let declaration mismatch at `", 34, 34);
x_34 = l_Lean_stringToMessageData(x_33);
lean_dec(x_33);
x_35 = lean_ctor_get(x_1, 1);
lean_inc(x_35);
lean_dec(x_1);
x_36 = l_Lean_MessageData_ofName(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("`, does not match value in local context", 40, 40);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_40, x_10, x_11, x_12, x_31);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
return x_41;
}
else
{
lean_object* x_42; lean_object* x_43; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
x_42 = lean_box(0);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_31);
return x_43;
}
}
}
else
{
uint8_t x_44; 
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_1);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkLetDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkLetDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_17; uint8_t x_18; 
x_17 = lean_st_ref_get(x_2, x_6);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint64_t x_25; lean_object* x_26; uint64_t x_27; uint64_t x_28; uint64_t x_29; lean_object* x_30; uint64_t x_31; uint64_t x_32; uint64_t x_33; size_t x_34; size_t x_35; lean_object* x_36; size_t x_37; size_t x_38; size_t x_39; lean_object* x_40; uint8_t x_41; 
x_21 = lean_ctor_get(x_17, 1);
x_22 = lean_ctor_get(x_19, 1);
x_23 = lean_ctor_get(x_19, 0);
lean_dec(x_23);
x_24 = lean_array_get_size(x_22);
x_25 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_26 = lean_unsigned_to_nat(32u);
x_27 = lean_uint64_of_nat(x_26);
x_28 = lean_uint64_shift_right(x_25, x_27);
x_29 = lean_uint64_xor(x_25, x_28);
x_30 = lean_unsigned_to_nat(16u);
x_31 = lean_uint64_of_nat(x_30);
x_32 = lean_uint64_shift_right(x_29, x_31);
x_33 = lean_uint64_xor(x_29, x_32);
x_34 = lean_uint64_to_usize(x_33);
x_35 = lean_usize_of_nat(x_24);
lean_dec(x_24);
x_36 = lean_unsigned_to_nat(1u);
x_37 = lean_usize_of_nat(x_36);
x_38 = lean_usize_sub(x_35, x_37);
x_39 = lean_usize_land(x_34, x_38);
x_40 = lean_array_uget(x_22, x_39);
lean_dec(x_22);
x_41 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_40);
lean_dec(x_40);
if (x_41 == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; size_t x_49; size_t x_50; size_t x_51; lean_object* x_52; uint8_t x_53; 
lean_free_object(x_19);
lean_free_object(x_17);
x_42 = lean_st_ref_take(x_2, x_21);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_box(0);
x_48 = lean_array_get_size(x_46);
x_49 = lean_usize_of_nat(x_48);
lean_dec(x_48);
x_50 = lean_usize_sub(x_49, x_37);
x_51 = lean_usize_land(x_34, x_50);
x_52 = lean_array_uget(x_46, x_51);
x_53 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_52);
if (x_53 == 0)
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_43);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; uint8_t x_65; 
x_55 = lean_ctor_get(x_43, 1);
lean_dec(x_55);
x_56 = lean_ctor_get(x_43, 0);
lean_dec(x_56);
x_57 = lean_nat_add(x_45, x_36);
lean_dec(x_45);
x_58 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_58, 0, x_1);
lean_ctor_set(x_58, 1, x_47);
lean_ctor_set(x_58, 2, x_52);
x_59 = lean_array_uset(x_46, x_51, x_58);
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
x_66 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_59);
lean_ctor_set(x_43, 1, x_66);
lean_ctor_set(x_43, 0, x_57);
x_7 = x_47;
x_8 = x_2;
x_9 = x_44;
x_10 = x_43;
goto block_16;
}
else
{
lean_ctor_set(x_43, 1, x_59);
lean_ctor_set(x_43, 0, x_57);
x_7 = x_47;
x_8 = x_2;
x_9 = x_44;
x_10 = x_43;
goto block_16;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; uint8_t x_75; 
lean_dec(x_43);
x_67 = lean_nat_add(x_45, x_36);
lean_dec(x_45);
x_68 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_68, 0, x_1);
lean_ctor_set(x_68, 1, x_47);
lean_ctor_set(x_68, 2, x_52);
x_69 = lean_array_uset(x_46, x_51, x_68);
x_70 = lean_unsigned_to_nat(2u);
x_71 = lean_nat_shiftl(x_67, x_70);
x_72 = lean_unsigned_to_nat(3u);
x_73 = lean_nat_div(x_71, x_72);
lean_dec(x_71);
x_74 = lean_array_get_size(x_69);
x_75 = lean_nat_dec_le(x_73, x_74);
lean_dec(x_74);
lean_dec(x_73);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; 
x_76 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_69);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_67);
lean_ctor_set(x_77, 1, x_76);
x_7 = x_47;
x_8 = x_2;
x_9 = x_44;
x_10 = x_77;
goto block_16;
}
else
{
lean_object* x_78; 
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_67);
lean_ctor_set(x_78, 1, x_69);
x_7 = x_47;
x_8 = x_2;
x_9 = x_44;
x_10 = x_78;
goto block_16;
}
}
}
else
{
lean_dec(x_52);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_1);
x_7 = x_47;
x_8 = x_2;
x_9 = x_44;
x_10 = x_43;
goto block_16;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
x_79 = lean_mk_string_unchecked("invalid LCNF, free variables are not unique `", 45, 45);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = l_Lean_MessageData_ofName(x_1);
lean_ctor_set_tag(x_19, 7);
lean_ctor_set(x_19, 1, x_81);
lean_ctor_set(x_19, 0, x_80);
x_82 = lean_mk_string_unchecked("`", 1, 1);
x_83 = l_Lean_stringToMessageData(x_82);
lean_dec(x_82);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_83);
x_84 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_17, x_3, x_4, x_5, x_21);
return x_84;
}
}
else
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; uint64_t x_88; lean_object* x_89; uint64_t x_90; uint64_t x_91; uint64_t x_92; lean_object* x_93; uint64_t x_94; uint64_t x_95; uint64_t x_96; size_t x_97; size_t x_98; lean_object* x_99; size_t x_100; size_t x_101; size_t x_102; lean_object* x_103; uint8_t x_104; 
x_85 = lean_ctor_get(x_17, 1);
x_86 = lean_ctor_get(x_19, 1);
lean_inc(x_86);
lean_dec(x_19);
x_87 = lean_array_get_size(x_86);
x_88 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_89 = lean_unsigned_to_nat(32u);
x_90 = lean_uint64_of_nat(x_89);
x_91 = lean_uint64_shift_right(x_88, x_90);
x_92 = lean_uint64_xor(x_88, x_91);
x_93 = lean_unsigned_to_nat(16u);
x_94 = lean_uint64_of_nat(x_93);
x_95 = lean_uint64_shift_right(x_92, x_94);
x_96 = lean_uint64_xor(x_92, x_95);
x_97 = lean_uint64_to_usize(x_96);
x_98 = lean_usize_of_nat(x_87);
lean_dec(x_87);
x_99 = lean_unsigned_to_nat(1u);
x_100 = lean_usize_of_nat(x_99);
x_101 = lean_usize_sub(x_98, x_100);
x_102 = lean_usize_land(x_97, x_101);
x_103 = lean_array_uget(x_86, x_102);
lean_dec(x_86);
x_104 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_103);
lean_dec(x_103);
if (x_104 == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; size_t x_112; size_t x_113; size_t x_114; lean_object* x_115; uint8_t x_116; 
lean_free_object(x_17);
x_105 = lean_st_ref_take(x_2, x_85);
x_106 = lean_ctor_get(x_105, 0);
lean_inc(x_106);
x_107 = lean_ctor_get(x_105, 1);
lean_inc(x_107);
lean_dec(x_105);
x_108 = lean_ctor_get(x_106, 0);
lean_inc(x_108);
x_109 = lean_ctor_get(x_106, 1);
lean_inc(x_109);
x_110 = lean_box(0);
x_111 = lean_array_get_size(x_109);
x_112 = lean_usize_of_nat(x_111);
lean_dec(x_111);
x_113 = lean_usize_sub(x_112, x_100);
x_114 = lean_usize_land(x_97, x_113);
x_115 = lean_array_uget(x_109, x_114);
x_116 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_115);
if (x_116 == 0)
{
lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
if (lean_is_exclusive(x_106)) {
 lean_ctor_release(x_106, 0);
 lean_ctor_release(x_106, 1);
 x_117 = x_106;
} else {
 lean_dec_ref(x_106);
 x_117 = lean_box(0);
}
x_118 = lean_nat_add(x_108, x_99);
lean_dec(x_108);
x_119 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_119, 0, x_1);
lean_ctor_set(x_119, 1, x_110);
lean_ctor_set(x_119, 2, x_115);
x_120 = lean_array_uset(x_109, x_114, x_119);
x_121 = lean_unsigned_to_nat(2u);
x_122 = lean_nat_shiftl(x_118, x_121);
x_123 = lean_unsigned_to_nat(3u);
x_124 = lean_nat_div(x_122, x_123);
lean_dec(x_122);
x_125 = lean_array_get_size(x_120);
x_126 = lean_nat_dec_le(x_124, x_125);
lean_dec(x_125);
lean_dec(x_124);
if (x_126 == 0)
{
lean_object* x_127; lean_object* x_128; 
x_127 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_120);
if (lean_is_scalar(x_117)) {
 x_128 = lean_alloc_ctor(0, 2, 0);
} else {
 x_128 = x_117;
}
lean_ctor_set(x_128, 0, x_118);
lean_ctor_set(x_128, 1, x_127);
x_7 = x_110;
x_8 = x_2;
x_9 = x_107;
x_10 = x_128;
goto block_16;
}
else
{
lean_object* x_129; 
if (lean_is_scalar(x_117)) {
 x_129 = lean_alloc_ctor(0, 2, 0);
} else {
 x_129 = x_117;
}
lean_ctor_set(x_129, 0, x_118);
lean_ctor_set(x_129, 1, x_120);
x_7 = x_110;
x_8 = x_2;
x_9 = x_107;
x_10 = x_129;
goto block_16;
}
}
else
{
lean_dec(x_115);
lean_dec(x_109);
lean_dec(x_108);
lean_dec(x_1);
x_7 = x_110;
x_8 = x_2;
x_9 = x_107;
x_10 = x_106;
goto block_16;
}
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_130 = lean_mk_string_unchecked("invalid LCNF, free variables are not unique `", 45, 45);
x_131 = l_Lean_stringToMessageData(x_130);
lean_dec(x_130);
x_132 = l_Lean_MessageData_ofName(x_1);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_131);
lean_ctor_set(x_133, 1, x_132);
x_134 = lean_mk_string_unchecked("`", 1, 1);
x_135 = l_Lean_stringToMessageData(x_134);
lean_dec(x_134);
lean_ctor_set_tag(x_17, 7);
lean_ctor_set(x_17, 1, x_135);
lean_ctor_set(x_17, 0, x_133);
x_136 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_17, x_3, x_4, x_5, x_85);
return x_136;
}
}
}
else
{
lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; lean_object* x_141; uint64_t x_142; lean_object* x_143; uint64_t x_144; uint64_t x_145; uint64_t x_146; lean_object* x_147; uint64_t x_148; uint64_t x_149; uint64_t x_150; size_t x_151; size_t x_152; lean_object* x_153; size_t x_154; size_t x_155; size_t x_156; lean_object* x_157; uint8_t x_158; 
x_137 = lean_ctor_get(x_17, 0);
x_138 = lean_ctor_get(x_17, 1);
lean_inc(x_138);
lean_inc(x_137);
lean_dec(x_17);
x_139 = lean_ctor_get(x_137, 1);
lean_inc(x_139);
if (lean_is_exclusive(x_137)) {
 lean_ctor_release(x_137, 0);
 lean_ctor_release(x_137, 1);
 x_140 = x_137;
} else {
 lean_dec_ref(x_137);
 x_140 = lean_box(0);
}
x_141 = lean_array_get_size(x_139);
x_142 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
x_143 = lean_unsigned_to_nat(32u);
x_144 = lean_uint64_of_nat(x_143);
x_145 = lean_uint64_shift_right(x_142, x_144);
x_146 = lean_uint64_xor(x_142, x_145);
x_147 = lean_unsigned_to_nat(16u);
x_148 = lean_uint64_of_nat(x_147);
x_149 = lean_uint64_shift_right(x_146, x_148);
x_150 = lean_uint64_xor(x_146, x_149);
x_151 = lean_uint64_to_usize(x_150);
x_152 = lean_usize_of_nat(x_141);
lean_dec(x_141);
x_153 = lean_unsigned_to_nat(1u);
x_154 = lean_usize_of_nat(x_153);
x_155 = lean_usize_sub(x_152, x_154);
x_156 = lean_usize_land(x_151, x_155);
x_157 = lean_array_uget(x_139, x_156);
lean_dec(x_139);
x_158 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_157);
lean_dec(x_157);
if (x_158 == 0)
{
lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; size_t x_166; size_t x_167; size_t x_168; lean_object* x_169; uint8_t x_170; 
lean_dec(x_140);
x_159 = lean_st_ref_take(x_2, x_138);
x_160 = lean_ctor_get(x_159, 0);
lean_inc(x_160);
x_161 = lean_ctor_get(x_159, 1);
lean_inc(x_161);
lean_dec(x_159);
x_162 = lean_ctor_get(x_160, 0);
lean_inc(x_162);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
x_164 = lean_box(0);
x_165 = lean_array_get_size(x_163);
x_166 = lean_usize_of_nat(x_165);
lean_dec(x_165);
x_167 = lean_usize_sub(x_166, x_154);
x_168 = lean_usize_land(x_151, x_167);
x_169 = lean_array_uget(x_163, x_168);
x_170 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_169);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; lean_object* x_178; lean_object* x_179; uint8_t x_180; 
if (lean_is_exclusive(x_160)) {
 lean_ctor_release(x_160, 0);
 lean_ctor_release(x_160, 1);
 x_171 = x_160;
} else {
 lean_dec_ref(x_160);
 x_171 = lean_box(0);
}
x_172 = lean_nat_add(x_162, x_153);
lean_dec(x_162);
x_173 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_173, 0, x_1);
lean_ctor_set(x_173, 1, x_164);
lean_ctor_set(x_173, 2, x_169);
x_174 = lean_array_uset(x_163, x_168, x_173);
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
if (lean_is_scalar(x_171)) {
 x_182 = lean_alloc_ctor(0, 2, 0);
} else {
 x_182 = x_171;
}
lean_ctor_set(x_182, 0, x_172);
lean_ctor_set(x_182, 1, x_181);
x_7 = x_164;
x_8 = x_2;
x_9 = x_161;
x_10 = x_182;
goto block_16;
}
else
{
lean_object* x_183; 
if (lean_is_scalar(x_171)) {
 x_183 = lean_alloc_ctor(0, 2, 0);
} else {
 x_183 = x_171;
}
lean_ctor_set(x_183, 0, x_172);
lean_ctor_set(x_183, 1, x_174);
x_7 = x_164;
x_8 = x_2;
x_9 = x_161;
x_10 = x_183;
goto block_16;
}
}
else
{
lean_dec(x_169);
lean_dec(x_163);
lean_dec(x_162);
lean_dec(x_1);
x_7 = x_164;
x_8 = x_2;
x_9 = x_161;
x_10 = x_160;
goto block_16;
}
}
else
{
lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_184 = lean_mk_string_unchecked("invalid LCNF, free variables are not unique `", 45, 45);
x_185 = l_Lean_stringToMessageData(x_184);
lean_dec(x_184);
x_186 = l_Lean_MessageData_ofName(x_1);
if (lean_is_scalar(x_140)) {
 x_187 = lean_alloc_ctor(7, 2, 0);
} else {
 x_187 = x_140;
 lean_ctor_set_tag(x_187, 7);
}
lean_ctor_set(x_187, 0, x_185);
lean_ctor_set(x_187, 1, x_186);
x_188 = lean_mk_string_unchecked("`", 1, 1);
x_189 = l_Lean_stringToMessageData(x_188);
lean_dec(x_188);
x_190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_190, 0, x_187);
lean_ctor_set(x_190, 1, x_189);
x_191 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_190, x_3, x_4, x_5, x_138);
return x_191;
}
}
block_16:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_st_ref_set(x_8, x_10, x_9);
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; 
x_13 = lean_ctor_get(x_11, 0);
lean_dec(x_13);
lean_ctor_set(x_11, 0, x_7);
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_7);
lean_ctor_set(x_15, 1, x_14);
return x_15;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_1, x_3, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_addFVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_addFVarId(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withFVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_1, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_3, 1);
lean_inc(x_14);
lean_dec(x_3);
x_15 = l_Lean_FVarIdSet_insert(x_14, x_1);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_13);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_8(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withFVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_2, x_5, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_4, 1);
lean_inc(x_15);
lean_dec(x_4);
x_16 = l_Lean_FVarIdSet_insert(x_15, x_2);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_8(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withJp___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
lean_inc(x_1);
x_11 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_1, x_4, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_12 = lean_ctor_get(x_11, 1);
lean_inc(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get(x_3, 0);
lean_inc(x_13);
x_14 = l_Lean_FVarIdSet_insert(x_13, x_1);
x_15 = lean_ctor_get(x_3, 1);
lean_inc(x_15);
lean_dec(x_3);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_8(x_2, x_16, x_4, x_5, x_6, x_7, x_8, x_9, x_12);
return x_17;
}
else
{
uint8_t x_18; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
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
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withJp(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
lean_inc(x_2);
x_12 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_2, x_5, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_4, 0);
lean_inc(x_14);
x_15 = l_Lean_FVarIdSet_insert(x_14, x_2);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_15);
lean_ctor_set(x_17, 1, x_16);
x_18 = lean_apply_8(x_3, x_17, x_5, x_6, x_7, x_8, x_9, x_10, x_13);
return x_18;
}
else
{
uint8_t x_19; 
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_19 = !lean_is_exclusive(x_12);
if (x_19 == 0)
{
return x_12;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_12, 0);
x_21 = lean_ctor_get(x_12, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_12);
x_22 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_21);
return x_22;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
lean_dec(x_2);
x_4 = l_Lean_FVarIdSet_insert(x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_11, x_4, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; uint8_t x_78; 
x_17 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__0), 2, 0);
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_22 = l_instMonadEIO(lean_box(0));
x_23 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_22);
x_24 = lean_ctor_get(x_23, 0);
lean_inc(x_24);
lean_dec(x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
lean_inc(x_25);
x_26 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_26, 0, x_25);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_27, 0, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
x_29 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_30 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_30, 0, x_29);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_33 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_33, 0, x_32);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_35, 0, lean_box(0));
lean_closure_set(x_35, 1, lean_box(0));
x_36 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_36, 0, x_35);
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_37, 0, x_36);
lean_inc(x_37);
lean_inc(x_34);
lean_inc(x_31);
x_38 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_38, 0, x_28);
lean_ctor_set(x_38, 1, x_20);
lean_ctor_set(x_38, 2, x_31);
lean_ctor_set(x_38, 3, x_34);
lean_ctor_set(x_38, 4, x_37);
x_39 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_39, 0, x_38);
lean_ctor_set(x_39, 1, x_21);
x_40 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
lean_inc(x_42);
x_43 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_43, 0, x_42);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_44, 0, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
x_46 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_46, 0, x_31);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_46);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_48, 0, x_34);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_49, 0, x_48);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_37);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_51, 0, x_50);
x_52 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_52, 0, x_45);
lean_ctor_set(x_52, 1, x_18);
lean_ctor_set(x_52, 2, x_47);
lean_ctor_set(x_52, 3, x_49);
lean_ctor_set(x_52, 4, x_51);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_52);
lean_ctor_set(x_53, 1, x_19);
x_54 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_53);
x_55 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_54);
x_56 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_55);
x_57 = lean_unsigned_to_nat(0u);
x_58 = lean_array_get_size(x_1);
x_78 = lean_nat_dec_lt(x_57, x_58);
if (x_78 == 0)
{
lean_dec(x_56);
x_59 = x_10;
goto block_77;
}
else
{
uint8_t x_79; 
x_79 = lean_nat_dec_le(x_58, x_58);
if (x_79 == 0)
{
lean_dec(x_56);
x_59 = x_10;
goto block_77;
}
else
{
lean_object* x_80; lean_object* x_81; size_t x_82; size_t x_83; lean_object* x_84; lean_object* x_85; 
x_80 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__1___boxed), 10, 0);
x_81 = lean_box(0);
x_82 = lean_usize_of_nat(x_57);
x_83 = lean_usize_of_nat(x_58);
lean_inc(x_1);
x_84 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_56, x_80, x_1, x_82, x_83, x_81);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
x_85 = lean_apply_8(x_84, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_85) == 0)
{
lean_object* x_86; 
x_86 = lean_ctor_get(x_85, 1);
lean_inc(x_86);
lean_dec(x_85);
x_59 = x_86;
goto block_77;
}
else
{
uint8_t x_87; 
lean_dec(x_58);
lean_dec(x_17);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_87 = !lean_is_exclusive(x_85);
if (x_87 == 0)
{
return x_85;
}
else
{
lean_object* x_88; lean_object* x_89; lean_object* x_90; 
x_88 = lean_ctor_get(x_85, 0);
x_89 = lean_ctor_get(x_85, 1);
lean_inc(x_89);
lean_inc(x_88);
lean_dec(x_85);
x_90 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_90, 0, x_88);
lean_ctor_set(x_90, 1, x_89);
return x_90;
}
}
}
}
block_16:
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_apply_8(x_2, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_11);
return x_15;
}
block_77:
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; uint8_t x_72; 
x_60 = lean_ctor_get(x_3, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_3, 1);
lean_inc(x_61);
lean_dec(x_3);
x_62 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_63 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_64 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_65 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_66 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_67 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_68 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_69 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_69, 0, x_62);
lean_ctor_set(x_69, 1, x_63);
x_70 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_70, 0, x_69);
lean_ctor_set(x_70, 1, x_64);
lean_ctor_set(x_70, 2, x_65);
lean_ctor_set(x_70, 3, x_66);
lean_ctor_set(x_70, 4, x_67);
x_71 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_68);
x_72 = lean_nat_dec_lt(x_57, x_58);
if (x_72 == 0)
{
lean_dec(x_71);
lean_dec(x_58);
lean_dec(x_17);
lean_dec(x_1);
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
goto block_16;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_58, x_58);
if (x_73 == 0)
{
lean_dec(x_71);
lean_dec(x_58);
lean_dec(x_17);
lean_dec(x_1);
x_11 = x_59;
x_12 = x_60;
x_13 = x_61;
goto block_16;
}
else
{
size_t x_74; size_t x_75; lean_object* x_76; 
x_74 = lean_usize_of_nat(x_57);
x_75 = lean_usize_of_nat(x_58);
lean_dec(x_58);
x_76 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_71, x_17, x_1, x_74, x_75, x_61);
x_11 = x_59;
x_12 = x_60;
x_13 = x_76;
goto block_16;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_79; 
x_18 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__0), 2, 0);
x_19 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__0___boxed), 7, 0);
x_20 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_instMonadCompilerM___lam__1), 9, 0);
x_21 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 0);
x_22 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 0);
x_23 = l_instMonadEIO(lean_box(0));
x_24 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_23);
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
lean_dec(x_24);
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec(x_25);
lean_inc(x_26);
x_27 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_27, 0, x_26);
x_28 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_28, 0, x_26);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_27);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_alloc_closure((void*)(l_instMonadEIO___lam__1), 5, 0);
x_31 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_31, 0, x_30);
x_32 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_32, 0, x_31);
x_33 = lean_alloc_closure((void*)(l_instMonadEIO___lam__2), 5, 0);
x_34 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_34, 0, x_33);
x_35 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_35, 0, x_34);
x_36 = lean_alloc_closure((void*)(l_EStateM_seqRight), 7, 2);
lean_closure_set(x_36, 0, lean_box(0));
lean_closure_set(x_36, 1, lean_box(0));
x_37 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_37, 0, x_36);
x_38 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_38, 0, x_37);
lean_inc(x_38);
lean_inc(x_35);
lean_inc(x_32);
x_39 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_39, 0, x_29);
lean_ctor_set(x_39, 1, x_21);
lean_ctor_set(x_39, 2, x_32);
lean_ctor_set(x_39, 3, x_35);
lean_ctor_set(x_39, 4, x_38);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_22);
x_41 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_40);
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
lean_dec(x_41);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
lean_dec(x_42);
lean_inc(x_43);
x_44 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__0), 6, 1);
lean_closure_set(x_44, 0, x_43);
x_45 = lean_alloc_closure((void*)(l_ReaderT_instFunctorOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_45);
x_47 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_47, 0, x_32);
x_48 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__1), 6, 1);
lean_closure_set(x_48, 0, x_47);
x_49 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_49, 0, x_35);
x_50 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_50, 0, x_49);
x_51 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_51, 0, x_38);
x_52 = lean_alloc_closure((void*)(l_ReaderT_instApplicativeOfMonad___redArg___lam__3), 6, 1);
lean_closure_set(x_52, 0, x_51);
x_53 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_53, 0, x_46);
lean_ctor_set(x_53, 1, x_19);
lean_ctor_set(x_53, 2, x_48);
lean_ctor_set(x_53, 3, x_50);
lean_ctor_set(x_53, 4, x_52);
x_54 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_54, 0, x_53);
lean_ctor_set(x_54, 1, x_20);
x_55 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_54);
x_56 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_55);
x_57 = l_ReaderT_instMonad(lean_box(0), lean_box(0), x_56);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_2);
x_79 = lean_nat_dec_lt(x_58, x_59);
if (x_79 == 0)
{
lean_dec(x_57);
x_60 = x_11;
goto block_78;
}
else
{
uint8_t x_80; 
x_80 = lean_nat_dec_le(x_59, x_59);
if (x_80 == 0)
{
lean_dec(x_57);
x_60 = x_11;
goto block_78;
}
else
{
lean_object* x_81; lean_object* x_82; size_t x_83; size_t x_84; lean_object* x_85; lean_object* x_86; 
x_81 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__1___boxed), 10, 0);
x_82 = lean_box(0);
x_83 = lean_usize_of_nat(x_58);
x_84 = lean_usize_of_nat(x_59);
lean_inc(x_2);
x_85 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_57, x_81, x_2, x_83, x_84, x_82);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
x_86 = lean_apply_8(x_85, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; 
x_87 = lean_ctor_get(x_86, 1);
lean_inc(x_87);
lean_dec(x_86);
x_60 = x_87;
goto block_78;
}
else
{
uint8_t x_88; 
lean_dec(x_59);
lean_dec(x_18);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_88 = !lean_is_exclusive(x_86);
if (x_88 == 0)
{
return x_86;
}
else
{
lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_89 = lean_ctor_get(x_86, 0);
x_90 = lean_ctor_get(x_86, 1);
lean_inc(x_90);
lean_inc(x_89);
lean_dec(x_86);
x_91 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
return x_91;
}
}
}
}
block_17:
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_13);
lean_ctor_set(x_15, 1, x_14);
x_16 = lean_apply_8(x_3, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_12);
return x_16;
}
block_78:
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_61 = lean_ctor_get(x_4, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_4, 1);
lean_inc(x_62);
lean_dec(x_4);
x_63 = lean_alloc_closure((void*)(l_Id_instMonad___lam__0), 4, 0);
x_64 = lean_alloc_closure((void*)(l_Id_instMonad___lam__1___boxed), 4, 0);
x_65 = lean_alloc_closure((void*)(l_Id_instMonad___lam__2___boxed), 2, 0);
x_66 = lean_alloc_closure((void*)(l_Id_instMonad___lam__3), 4, 0);
x_67 = lean_alloc_closure((void*)(l_Id_instMonad___lam__4___boxed), 4, 0);
x_68 = lean_alloc_closure((void*)(l_Id_instMonad___lam__5___boxed), 4, 0);
x_69 = lean_alloc_closure((void*)(l_Id_instMonad___lam__6), 4, 0);
x_70 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_70, 0, x_63);
lean_ctor_set(x_70, 1, x_64);
x_71 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_71, 0, x_70);
lean_ctor_set(x_71, 1, x_65);
lean_ctor_set(x_71, 2, x_66);
lean_ctor_set(x_71, 3, x_67);
lean_ctor_set(x_71, 4, x_68);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_71);
lean_ctor_set(x_72, 1, x_69);
x_73 = lean_nat_dec_lt(x_58, x_59);
if (x_73 == 0)
{
lean_dec(x_72);
lean_dec(x_59);
lean_dec(x_18);
lean_dec(x_2);
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
goto block_17;
}
else
{
uint8_t x_74; 
x_74 = lean_nat_dec_le(x_59, x_59);
if (x_74 == 0)
{
lean_dec(x_72);
lean_dec(x_59);
lean_dec(x_18);
lean_dec(x_2);
x_12 = x_60;
x_13 = x_61;
x_14 = x_62;
goto block_17;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = lean_usize_of_nat(x_58);
x_76 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_77 = l_Array_foldlMUnsafe_fold(lean_box(0), lean_box(0), lean_box(0), x_72, x_18, x_2, x_75, x_76, x_62);
x_12 = x_60;
x_13 = x_61;
x_14 = x_77;
goto block_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_Compiler_LCNF_Check_withParams___redArg___lam__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; 
x_10 = lean_usize_dec_eq(x_2, x_3);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
lean_dec(x_4);
x_11 = lean_array_uget(x_1, x_2);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_12, x_5, x_6, x_7, x_8, x_9);
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
x_18 = lean_usize_add(x_2, x_17);
x_2 = x_18;
x_4 = x_14;
x_9 = x_15;
goto _start;
}
else
{
return x_13;
}
}
else
{
lean_object* x_20; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_9);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg(x_1, x_2, x_3, x_4, x_6, x_9, x_10, x_11, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDeclCore(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_79; 
x_79 = l_Lean_Compiler_LCNF_Check_checkParams(x_2, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_79) == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; uint8_t x_92; 
x_80 = lean_ctor_get(x_79, 1);
lean_inc(x_80);
lean_dec(x_79);
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_array_get_size(x_2);
x_92 = lean_nat_dec_lt(x_81, x_82);
if (x_92 == 0)
{
x_83 = x_80;
goto block_91;
}
else
{
uint8_t x_93; 
x_93 = lean_nat_dec_le(x_82, x_82);
if (x_93 == 0)
{
x_83 = x_80;
goto block_91;
}
else
{
lean_object* x_94; size_t x_95; size_t x_96; lean_object* x_97; 
x_94 = lean_box(0);
x_95 = lean_usize_of_nat(x_81);
x_96 = lean_usize_of_nat(x_82);
x_97 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg(x_2, x_95, x_96, x_94, x_6, x_9, x_10, x_11, x_80);
if (lean_obj_tag(x_97) == 0)
{
lean_object* x_98; 
x_98 = lean_ctor_get(x_97, 1);
lean_inc(x_98);
lean_dec(x_97);
x_83 = x_98;
goto block_91;
}
else
{
lean_dec(x_82);
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
return x_97;
}
}
}
block_91:
{
lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_84 = lean_ctor_get(x_5, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_5, 1);
lean_inc(x_85);
lean_dec(x_5);
x_86 = lean_nat_dec_lt(x_81, x_82);
if (x_86 == 0)
{
lean_dec(x_82);
x_71 = x_84;
x_72 = x_83;
x_73 = x_85;
goto block_78;
}
else
{
uint8_t x_87; 
x_87 = lean_nat_dec_le(x_82, x_82);
if (x_87 == 0)
{
lean_dec(x_82);
x_71 = x_84;
x_72 = x_83;
x_73 = x_85;
goto block_78;
}
else
{
size_t x_88; size_t x_89; lean_object* x_90; 
x_88 = lean_usize_of_nat(x_81);
x_89 = lean_usize_of_nat(x_82);
lean_dec(x_82);
x_90 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0(x_2, x_88, x_89, x_85);
x_71 = x_84;
x_72 = x_83;
x_73 = x_90;
goto block_78;
}
}
}
}
else
{
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
return x_79;
}
block_70:
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_14 = l_Lean_Compiler_LCNF_Check_checkTypes___redArg(x_8, x_13);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_unbox(x_15);
lean_dec(x_15);
if (x_16 == 0)
{
uint8_t x_17; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_17 = !lean_is_exclusive(x_14);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_14, 0);
lean_dec(x_18);
x_19 = lean_box(0);
lean_ctor_set(x_14, 0, x_19);
return x_14;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = lean_ctor_get(x_14, 1);
lean_inc(x_20);
lean_dec(x_14);
x_21 = lean_box(0);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_20);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_14, 1);
lean_inc(x_23);
lean_dec(x_14);
x_24 = l_Lean_Compiler_LCNF_Code_inferType(x_4, x_8, x_9, x_10, x_11, x_23);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_24, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = l_Lean_Compiler_LCNF_mkForallParams(x_2, x_25, x_8, x_9, x_10, x_11, x_26);
lean_dec(x_25);
if (lean_obj_tag(x_27) == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
x_29 = lean_ctor_get(x_27, 1);
lean_inc(x_29);
lean_dec(x_27);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_28);
lean_inc(x_3);
x_30 = l_Lean_Compiler_LCNF_InferType_compatibleTypes(x_3, x_28, x_7, x_8, x_9, x_10, x_11, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; uint8_t x_32; 
x_31 = lean_ctor_get(x_30, 0);
lean_inc(x_31);
x_32 = lean_unbox(x_31);
lean_dec(x_31);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_33 = lean_ctor_get(x_30, 1);
lean_inc(x_33);
lean_dec(x_30);
x_34 = lean_mk_string_unchecked("type mismatch at `", 18, 18);
x_35 = l_Lean_stringToMessageData(x_34);
lean_dec(x_34);
x_36 = l_Lean_MessageData_ofName(x_1);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
x_38 = lean_mk_string_unchecked("`, value has type", 17, 17);
x_39 = l_Lean_stringToMessageData(x_38);
lean_dec(x_38);
x_40 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_40, 0, x_37);
lean_ctor_set(x_40, 1, x_39);
x_41 = l_Lean_indentExpr(x_28);
x_42 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_42, 0, x_40);
lean_ctor_set(x_42, 1, x_41);
x_43 = lean_mk_string_unchecked("\nbut is expected to have type", 29, 29);
x_44 = l_Lean_stringToMessageData(x_43);
lean_dec(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_42);
lean_ctor_set(x_45, 1, x_44);
x_46 = l_Lean_indentExpr(x_3);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("", 0, 0);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_50, x_9, x_10, x_11, x_33);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
return x_51;
}
else
{
uint8_t x_52; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_52 = !lean_is_exclusive(x_30);
if (x_52 == 0)
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_30, 0);
lean_dec(x_53);
x_54 = lean_box(0);
lean_ctor_set(x_30, 0, x_54);
return x_30;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_30, 1);
lean_inc(x_55);
lean_dec(x_30);
x_56 = lean_box(0);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
}
}
else
{
uint8_t x_58; 
lean_dec(x_28);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_3);
lean_dec(x_1);
x_58 = !lean_is_exclusive(x_30);
if (x_58 == 0)
{
return x_30;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_59 = lean_ctor_get(x_30, 0);
x_60 = lean_ctor_get(x_30, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_30);
x_61 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_61, 0, x_59);
lean_ctor_set(x_61, 1, x_60);
return x_61;
}
}
}
else
{
uint8_t x_62; 
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_27);
if (x_62 == 0)
{
return x_27;
}
else
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_63 = lean_ctor_get(x_27, 0);
x_64 = lean_ctor_get(x_27, 1);
lean_inc(x_64);
lean_inc(x_63);
lean_dec(x_27);
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
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_66 = !lean_is_exclusive(x_24);
if (x_66 == 0)
{
return x_24;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_24, 0);
x_68 = lean_ctor_get(x_24, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_24);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
block_78:
{
lean_object* x_74; lean_object* x_75; 
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_71);
lean_ctor_set(x_74, 1, x_73);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_4);
x_75 = l_Lean_Compiler_LCNF_Check_check(x_4, x_74, x_6, x_7, x_8, x_9, x_10, x_11, x_72);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; 
x_76 = lean_ctor_get(x_75, 1);
lean_inc(x_76);
lean_dec(x_75);
x_13 = x_76;
goto block_70;
}
else
{
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_77; 
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_13 = x_77;
goto block_70;
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_75;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_1, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 1);
lean_inc(x_11);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_10);
x_12 = l_Lean_Compiler_LCNF_Check_checkLetDecl(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_ctor_get(x_10, 0);
lean_inc(x_14);
lean_dec(x_10);
lean_inc(x_14);
x_15 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_14, x_3, x_6, x_7, x_8, x_13);
if (lean_obj_tag(x_15) == 0)
{
uint8_t x_16; 
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_15, 1);
x_18 = lean_ctor_get(x_15, 0);
lean_dec(x_18);
x_19 = lean_ctor_get(x_2, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_2, 1);
lean_inc(x_20);
lean_dec(x_2);
x_21 = l_Lean_FVarIdSet_insert(x_20, x_14);
lean_ctor_set(x_15, 1, x_21);
lean_ctor_set(x_15, 0, x_19);
x_1 = x_11;
x_2 = x_15;
x_9 = x_17;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_15, 1);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_ctor_get(x_2, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_dec(x_2);
x_26 = l_Lean_FVarIdSet_insert(x_25, x_14);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_1 = x_11;
x_2 = x_27;
x_9 = x_23;
goto _start;
}
}
else
{
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_15;
}
}
else
{
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_12;
}
}
case 1:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_1, 0);
x_31 = lean_ctor_get(x_1, 1);
x_32 = lean_box(0);
x_33 = lean_ctor_get(x_2, 1);
lean_inc(x_33);
lean_inc(x_33);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_33);
lean_ctor_set(x_1, 0, x_32);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_30);
x_34 = l_Lean_Compiler_LCNF_Check_checkFunDecl(x_30, x_1, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_34, 1);
lean_inc(x_35);
lean_dec(x_34);
x_36 = lean_ctor_get(x_30, 0);
lean_inc(x_36);
lean_dec(x_30);
lean_inc(x_36);
x_37 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_36, x_3, x_6, x_7, x_8, x_35);
if (lean_obj_tag(x_37) == 0)
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_39 = lean_ctor_get(x_37, 1);
x_40 = lean_ctor_get(x_37, 0);
lean_dec(x_40);
x_41 = lean_ctor_get(x_2, 0);
lean_inc(x_41);
lean_dec(x_2);
x_42 = l_Lean_FVarIdSet_insert(x_33, x_36);
lean_ctor_set(x_37, 1, x_42);
lean_ctor_set(x_37, 0, x_41);
x_1 = x_31;
x_2 = x_37;
x_9 = x_39;
goto _start;
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_44 = lean_ctor_get(x_37, 1);
lean_inc(x_44);
lean_dec(x_37);
x_45 = lean_ctor_get(x_2, 0);
lean_inc(x_45);
lean_dec(x_2);
x_46 = l_Lean_FVarIdSet_insert(x_33, x_36);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_1 = x_31;
x_2 = x_47;
x_9 = x_44;
goto _start;
}
}
else
{
lean_dec(x_36);
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_37;
}
}
else
{
lean_dec(x_33);
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_34;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
x_49 = lean_ctor_get(x_1, 0);
x_50 = lean_ctor_get(x_1, 1);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_1);
x_51 = lean_box(0);
x_52 = lean_ctor_get(x_2, 1);
lean_inc(x_52);
lean_inc(x_52);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_49);
x_54 = l_Lean_Compiler_LCNF_Check_checkFunDecl(x_49, x_53, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec(x_54);
x_56 = lean_ctor_get(x_49, 0);
lean_inc(x_56);
lean_dec(x_49);
lean_inc(x_56);
x_57 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_56, x_3, x_6, x_7, x_8, x_55);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
if (lean_is_exclusive(x_57)) {
 lean_ctor_release(x_57, 0);
 lean_ctor_release(x_57, 1);
 x_59 = x_57;
} else {
 lean_dec_ref(x_57);
 x_59 = lean_box(0);
}
x_60 = lean_ctor_get(x_2, 0);
lean_inc(x_60);
lean_dec(x_2);
x_61 = l_Lean_FVarIdSet_insert(x_52, x_56);
if (lean_is_scalar(x_59)) {
 x_62 = lean_alloc_ctor(0, 2, 0);
} else {
 x_62 = x_59;
}
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
x_1 = x_50;
x_2 = x_62;
x_9 = x_58;
goto _start;
}
else
{
lean_dec(x_56);
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_57;
}
}
else
{
lean_dec(x_52);
lean_dec(x_50);
lean_dec(x_49);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_54;
}
}
}
case 2:
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_1, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_1, 1);
lean_inc(x_65);
lean_dec(x_1);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_2);
lean_inc(x_64);
x_66 = l_Lean_Compiler_LCNF_Check_checkFunDecl(x_64, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_66, 1);
lean_inc(x_67);
lean_dec(x_66);
x_68 = lean_ctor_get(x_64, 0);
lean_inc(x_68);
lean_dec(x_64);
lean_inc(x_68);
x_69 = l_Lean_Compiler_LCNF_Check_addFVarId___redArg(x_68, x_3, x_6, x_7, x_8, x_67);
if (lean_obj_tag(x_69) == 0)
{
uint8_t x_70; 
x_70 = !lean_is_exclusive(x_69);
if (x_70 == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_71 = lean_ctor_get(x_69, 1);
x_72 = lean_ctor_get(x_69, 0);
lean_dec(x_72);
x_73 = lean_ctor_get(x_2, 0);
lean_inc(x_73);
x_74 = l_Lean_FVarIdSet_insert(x_73, x_68);
x_75 = lean_ctor_get(x_2, 1);
lean_inc(x_75);
lean_dec(x_2);
lean_ctor_set(x_69, 1, x_75);
lean_ctor_set(x_69, 0, x_74);
x_1 = x_65;
x_2 = x_69;
x_9 = x_71;
goto _start;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_77 = lean_ctor_get(x_69, 1);
lean_inc(x_77);
lean_dec(x_69);
x_78 = lean_ctor_get(x_2, 0);
lean_inc(x_78);
x_79 = l_Lean_FVarIdSet_insert(x_78, x_68);
x_80 = lean_ctor_get(x_2, 1);
lean_inc(x_80);
lean_dec(x_2);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_1 = x_65;
x_2 = x_81;
x_9 = x_77;
goto _start;
}
}
else
{
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_69;
}
}
else
{
lean_dec(x_65);
lean_dec(x_64);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_66;
}
}
case 3:
{
uint8_t x_83; 
x_83 = !lean_is_exclusive(x_1);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_97; 
x_84 = lean_ctor_get(x_1, 0);
x_85 = lean_ctor_get(x_1, 1);
lean_inc(x_84);
x_97 = l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg(x_84, x_2, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_97) == 0)
{
uint8_t x_98; 
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; lean_object* x_101; 
x_99 = lean_ctor_get(x_97, 1);
x_100 = lean_ctor_get(x_97, 0);
lean_dec(x_100);
lean_inc(x_84);
x_101 = l_Lean_Compiler_LCNF_getFunDecl(x_84, x_5, x_6, x_7, x_8, x_99);
if (lean_obj_tag(x_101) == 0)
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; uint8_t x_106; 
x_102 = lean_ctor_get(x_101, 0);
lean_inc(x_102);
x_103 = lean_ctor_get(x_101, 1);
lean_inc(x_103);
lean_dec(x_101);
x_104 = l_Lean_Compiler_LCNF_FunDeclCore_getArity___redArg(x_102);
x_105 = lean_array_get_size(x_85);
x_106 = lean_nat_dec_eq(x_104, x_105);
if (x_106 == 0)
{
lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_107 = lean_mk_string_unchecked("invalid LCNF `goto`, join point ", 32, 32);
x_108 = l_Lean_stringToMessageData(x_107);
lean_dec(x_107);
x_109 = lean_ctor_get(x_102, 1);
lean_inc(x_109);
lean_dec(x_102);
x_110 = l_Lean_MessageData_ofName(x_109);
lean_ctor_set_tag(x_97, 7);
lean_ctor_set(x_97, 1, x_110);
lean_ctor_set(x_97, 0, x_108);
x_111 = lean_mk_string_unchecked(" has #", 6, 6);
x_112 = l_Lean_stringToMessageData(x_111);
lean_dec(x_111);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_112);
lean_ctor_set(x_1, 0, x_97);
x_113 = l___private_Init_Data_Repr_0__Nat_reprFast(x_104);
x_114 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_114, 0, x_113);
x_115 = l_Lean_MessageData_ofFormat(x_114);
x_116 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_116, 0, x_1);
lean_ctor_set(x_116, 1, x_115);
x_117 = lean_mk_string_unchecked(" parameters, but #", 18, 18);
x_118 = l_Lean_stringToMessageData(x_117);
lean_dec(x_117);
x_119 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_119, 0, x_116);
lean_ctor_set(x_119, 1, x_118);
x_120 = l___private_Init_Data_Repr_0__Nat_reprFast(x_105);
x_121 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_121, 0, x_120);
x_122 = l_Lean_MessageData_ofFormat(x_121);
x_123 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_123, 0, x_119);
lean_ctor_set(x_123, 1, x_122);
x_124 = lean_mk_string_unchecked(" were provided", 14, 14);
x_125 = l_Lean_stringToMessageData(x_124);
lean_dec(x_124);
x_126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_126, 0, x_123);
lean_ctor_set(x_126, 1, x_125);
x_127 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_126, x_6, x_7, x_8, x_103);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_127;
}
else
{
lean_dec(x_105);
lean_dec(x_104);
lean_dec(x_102);
lean_free_object(x_97);
lean_free_object(x_1);
x_86 = x_2;
x_87 = x_3;
x_88 = x_4;
x_89 = x_5;
x_90 = x_6;
x_91 = x_7;
x_92 = x_8;
x_93 = x_103;
goto block_96;
}
}
else
{
uint8_t x_128; 
lean_free_object(x_97);
lean_free_object(x_1);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_128 = !lean_is_exclusive(x_101);
if (x_128 == 0)
{
return x_101;
}
else
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; 
x_129 = lean_ctor_get(x_101, 0);
x_130 = lean_ctor_get(x_101, 1);
lean_inc(x_130);
lean_inc(x_129);
lean_dec(x_101);
x_131 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_131, 0, x_129);
lean_ctor_set(x_131, 1, x_130);
return x_131;
}
}
}
else
{
lean_object* x_132; lean_object* x_133; 
x_132 = lean_ctor_get(x_97, 1);
lean_inc(x_132);
lean_dec(x_97);
lean_inc(x_84);
x_133 = l_Lean_Compiler_LCNF_getFunDecl(x_84, x_5, x_6, x_7, x_8, x_132);
if (lean_obj_tag(x_133) == 0)
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; 
x_134 = lean_ctor_get(x_133, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_133, 1);
lean_inc(x_135);
lean_dec(x_133);
x_136 = l_Lean_Compiler_LCNF_FunDeclCore_getArity___redArg(x_134);
x_137 = lean_array_get_size(x_85);
x_138 = lean_nat_dec_eq(x_136, x_137);
if (x_138 == 0)
{
lean_object* x_139; lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; 
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_139 = lean_mk_string_unchecked("invalid LCNF `goto`, join point ", 32, 32);
x_140 = l_Lean_stringToMessageData(x_139);
lean_dec(x_139);
x_141 = lean_ctor_get(x_134, 1);
lean_inc(x_141);
lean_dec(x_134);
x_142 = l_Lean_MessageData_ofName(x_141);
x_143 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_142);
x_144 = lean_mk_string_unchecked(" has #", 6, 6);
x_145 = l_Lean_stringToMessageData(x_144);
lean_dec(x_144);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_145);
lean_ctor_set(x_1, 0, x_143);
x_146 = l___private_Init_Data_Repr_0__Nat_reprFast(x_136);
x_147 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_147, 0, x_146);
x_148 = l_Lean_MessageData_ofFormat(x_147);
x_149 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_149, 0, x_1);
lean_ctor_set(x_149, 1, x_148);
x_150 = lean_mk_string_unchecked(" parameters, but #", 18, 18);
x_151 = l_Lean_stringToMessageData(x_150);
lean_dec(x_150);
x_152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_152, 0, x_149);
lean_ctor_set(x_152, 1, x_151);
x_153 = l___private_Init_Data_Repr_0__Nat_reprFast(x_137);
x_154 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_154, 0, x_153);
x_155 = l_Lean_MessageData_ofFormat(x_154);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_string_unchecked(" were provided", 14, 14);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_159, x_6, x_7, x_8, x_135);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_160;
}
else
{
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_134);
lean_free_object(x_1);
x_86 = x_2;
x_87 = x_3;
x_88 = x_4;
x_89 = x_5;
x_90 = x_6;
x_91 = x_7;
x_92 = x_8;
x_93 = x_135;
goto block_96;
}
}
else
{
lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_free_object(x_1);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_161 = lean_ctor_get(x_133, 0);
lean_inc(x_161);
x_162 = lean_ctor_get(x_133, 1);
lean_inc(x_162);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_163 = x_133;
} else {
 lean_dec_ref(x_133);
 x_163 = lean_box(0);
}
if (lean_is_scalar(x_163)) {
 x_164 = lean_alloc_ctor(1, 2, 0);
} else {
 x_164 = x_163;
}
lean_ctor_set(x_164, 0, x_161);
lean_ctor_set(x_164, 1, x_162);
return x_164;
}
}
}
else
{
lean_free_object(x_1);
lean_dec(x_85);
lean_dec(x_84);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_97;
}
block_96:
{
lean_object* x_94; lean_object* x_95; 
x_94 = l_Lean_Expr_fvar___override(x_84);
x_95 = l_Lean_Compiler_LCNF_Check_checkAppArgs(x_94, x_85, x_86, x_87, x_88, x_89, x_90, x_91, x_92, x_93);
lean_dec(x_86);
return x_95;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_178; 
x_165 = lean_ctor_get(x_1, 0);
x_166 = lean_ctor_get(x_1, 1);
lean_inc(x_166);
lean_inc(x_165);
lean_dec(x_1);
lean_inc(x_165);
x_178 = l_Lean_Compiler_LCNF_Check_checkJpInScope___redArg(x_165, x_2, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_178) == 0)
{
lean_object* x_179; lean_object* x_180; lean_object* x_181; 
x_179 = lean_ctor_get(x_178, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_178)) {
 lean_ctor_release(x_178, 0);
 lean_ctor_release(x_178, 1);
 x_180 = x_178;
} else {
 lean_dec_ref(x_178);
 x_180 = lean_box(0);
}
lean_inc(x_165);
x_181 = l_Lean_Compiler_LCNF_getFunDecl(x_165, x_5, x_6, x_7, x_8, x_179);
if (lean_obj_tag(x_181) == 0)
{
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; uint8_t x_186; 
x_182 = lean_ctor_get(x_181, 0);
lean_inc(x_182);
x_183 = lean_ctor_get(x_181, 1);
lean_inc(x_183);
lean_dec(x_181);
x_184 = l_Lean_Compiler_LCNF_FunDeclCore_getArity___redArg(x_182);
x_185 = lean_array_get_size(x_166);
x_186 = lean_nat_dec_eq(x_184, x_185);
if (x_186 == 0)
{
lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_187 = lean_mk_string_unchecked("invalid LCNF `goto`, join point ", 32, 32);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = lean_ctor_get(x_182, 1);
lean_inc(x_189);
lean_dec(x_182);
x_190 = l_Lean_MessageData_ofName(x_189);
if (lean_is_scalar(x_180)) {
 x_191 = lean_alloc_ctor(7, 2, 0);
} else {
 x_191 = x_180;
 lean_ctor_set_tag(x_191, 7);
}
lean_ctor_set(x_191, 0, x_188);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_mk_string_unchecked(" has #", 6, 6);
x_193 = l_Lean_stringToMessageData(x_192);
lean_dec(x_192);
x_194 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_194, 0, x_191);
lean_ctor_set(x_194, 1, x_193);
x_195 = l___private_Init_Data_Repr_0__Nat_reprFast(x_184);
x_196 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_196, 0, x_195);
x_197 = l_Lean_MessageData_ofFormat(x_196);
x_198 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_198, 0, x_194);
lean_ctor_set(x_198, 1, x_197);
x_199 = lean_mk_string_unchecked(" parameters, but #", 18, 18);
x_200 = l_Lean_stringToMessageData(x_199);
lean_dec(x_199);
x_201 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_201, 0, x_198);
lean_ctor_set(x_201, 1, x_200);
x_202 = l___private_Init_Data_Repr_0__Nat_reprFast(x_185);
x_203 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_203, 0, x_202);
x_204 = l_Lean_MessageData_ofFormat(x_203);
x_205 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_205, 0, x_201);
lean_ctor_set(x_205, 1, x_204);
x_206 = lean_mk_string_unchecked(" were provided", 14, 14);
x_207 = l_Lean_stringToMessageData(x_206);
lean_dec(x_206);
x_208 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_208, 0, x_205);
lean_ctor_set(x_208, 1, x_207);
x_209 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_208, x_6, x_7, x_8, x_183);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_209;
}
else
{
lean_dec(x_185);
lean_dec(x_184);
lean_dec(x_182);
lean_dec(x_180);
x_167 = x_2;
x_168 = x_3;
x_169 = x_4;
x_170 = x_5;
x_171 = x_6;
x_172 = x_7;
x_173 = x_8;
x_174 = x_183;
goto block_177;
}
}
else
{
lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
lean_dec(x_180);
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_210 = lean_ctor_get(x_181, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_181, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_181)) {
 lean_ctor_release(x_181, 0);
 lean_ctor_release(x_181, 1);
 x_212 = x_181;
} else {
 lean_dec_ref(x_181);
 x_212 = lean_box(0);
}
if (lean_is_scalar(x_212)) {
 x_213 = lean_alloc_ctor(1, 2, 0);
} else {
 x_213 = x_212;
}
lean_ctor_set(x_213, 0, x_210);
lean_ctor_set(x_213, 1, x_211);
return x_213;
}
}
else
{
lean_dec(x_166);
lean_dec(x_165);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_178;
}
block_177:
{
lean_object* x_175; lean_object* x_176; 
x_175 = l_Lean_Expr_fvar___override(x_165);
x_176 = l_Lean_Compiler_LCNF_Check_checkAppArgs(x_175, x_166, x_167, x_168, x_169, x_170, x_171, x_172, x_173, x_174);
lean_dec(x_167);
return x_176;
}
}
}
case 4:
{
lean_object* x_214; lean_object* x_215; 
x_214 = lean_ctor_get(x_1, 0);
lean_inc(x_214);
lean_dec(x_1);
x_215 = l_Lean_Compiler_LCNF_Check_checkCases(x_214, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_215;
}
case 5:
{
lean_object* x_216; lean_object* x_217; 
x_216 = lean_ctor_get(x_1, 0);
lean_inc(x_216);
lean_dec(x_1);
x_217 = l_Lean_Compiler_LCNF_Check_checkFVar(x_216, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
return x_217;
}
default: 
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_218 = lean_box(0);
x_219 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_9);
return x_219;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_6, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_box(0);
x_12 = lean_unbox(x_11);
lean_inc(x_1);
x_13 = l_Lean_Environment_find_x3f(x_10, x_1, x_12);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_free_object(x_6);
x_14 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_15 = l_Lean_stringToMessageData(x_14);
lean_dec(x_14);
x_16 = lean_unbox(x_11);
x_17 = l_Lean_MessageData_ofConstName(x_1, x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_15);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_mk_string_unchecked("'", 1, 1);
x_20 = l_Lean_stringToMessageData(x_19);
lean_dec(x_19);
x_21 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_21, 0, x_18);
lean_ctor_set(x_21, 1, x_20);
x_22 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_21, x_2, x_3, x_4, x_9);
return x_22;
}
else
{
lean_object* x_23; 
lean_dec(x_1);
x_23 = lean_ctor_get(x_13, 0);
lean_inc(x_23);
lean_dec(x_13);
lean_ctor_set(x_6, 0, x_23);
return x_6;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; 
x_24 = lean_ctor_get(x_6, 0);
x_25 = lean_ctor_get(x_6, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_6);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_box(0);
x_28 = lean_unbox(x_27);
lean_inc(x_1);
x_29 = l_Lean_Environment_find_x3f(x_26, x_1, x_28);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; uint8_t x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_30 = lean_mk_string_unchecked("unknown constant '", 18, 18);
x_31 = l_Lean_stringToMessageData(x_30);
lean_dec(x_30);
x_32 = lean_unbox(x_27);
x_33 = l_Lean_MessageData_ofConstName(x_1, x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = lean_mk_string_unchecked("'", 1, 1);
x_36 = l_Lean_stringToMessageData(x_35);
lean_dec(x_35);
x_37 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_36);
x_38 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_37, x_2, x_3, x_4, x_25);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_ctor_get(x_29, 0);
lean_inc(x_39);
lean_dec(x_29);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_25);
return x_40;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg(x_1, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Compiler_LCNF_Check_checkParams(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_182; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_182 = l_Lean_NameSet_contains(x_24, x_25);
if (x_182 == 0)
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_131 = x_24;
x_132 = x_6;
x_133 = x_7;
x_134 = x_8;
x_135 = x_9;
x_136 = x_10;
x_137 = x_11;
x_138 = x_12;
x_139 = x_29;
goto block_181;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_183 = lean_mk_string_unchecked("invalid LCNF `cases`, alternative `", 35, 35);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = l_Lean_MessageData_ofName(x_25);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_mk_string_unchecked("` occurs more than once", 23, 23);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_189, x_10, x_11, x_12, x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
return x_190;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_190);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
block_39:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_30);
x_14 = x_34;
x_15 = x_33;
goto block_20;
}
else
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_46);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Compiler_LCNF_Check_check(x_27, x_50, x_42, x_45, x_41, x_48, x_43, x_47, x_40);
x_31 = x_44;
x_32 = x_51;
goto block_39;
}
block_71:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_55, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_55, 1);
lean_inc(x_65);
lean_dec(x_55);
x_66 = lean_nat_dec_lt(x_61, x_56);
if (x_66 == 0)
{
lean_dec(x_56);
lean_dec(x_26);
x_40 = x_63;
x_41 = x_54;
x_42 = x_53;
x_43 = x_57;
x_44 = x_59;
x_45 = x_58;
x_46 = x_64;
x_47 = x_60;
x_48 = x_62;
x_49 = x_65;
goto block_52;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_56, x_56);
if (x_67 == 0)
{
lean_dec(x_56);
lean_dec(x_26);
x_40 = x_63;
x_41 = x_54;
x_42 = x_53;
x_43 = x_57;
x_44 = x_59;
x_45 = x_58;
x_46 = x_64;
x_47 = x_60;
x_48 = x_62;
x_49 = x_65;
goto block_52;
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = lean_usize_of_nat(x_61);
x_69 = lean_usize_of_nat(x_56);
lean_dec(x_56);
x_70 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0(x_26, x_68, x_69, x_65);
lean_dec(x_26);
x_40 = x_63;
x_41 = x_54;
x_42 = x_53;
x_43 = x_57;
x_44 = x_59;
x_45 = x_58;
x_46 = x_64;
x_47 = x_60;
x_48 = x_62;
x_49 = x_70;
goto block_52;
}
}
}
block_90:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_array_get_size(x_26);
x_83 = lean_nat_dec_lt(x_81, x_82);
if (x_83 == 0)
{
x_53 = x_74;
x_54 = x_76;
x_55 = x_73;
x_56 = x_82;
x_57 = x_78;
x_58 = x_75;
x_59 = x_72;
x_60 = x_79;
x_61 = x_81;
x_62 = x_77;
x_63 = x_80;
goto block_71;
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_le(x_82, x_82);
if (x_84 == 0)
{
x_53 = x_74;
x_54 = x_76;
x_55 = x_73;
x_56 = x_82;
x_57 = x_78;
x_58 = x_75;
x_59 = x_72;
x_60 = x_79;
x_61 = x_81;
x_62 = x_77;
x_63 = x_80;
goto block_71;
}
else
{
lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_usize_of_nat(x_81);
x_87 = lean_usize_of_nat(x_82);
x_88 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg(x_26, x_86, x_87, x_85, x_74, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_53 = x_74;
x_54 = x_76;
x_55 = x_73;
x_56 = x_82;
x_57 = x_78;
x_58 = x_75;
x_59 = x_72;
x_60 = x_79;
x_61 = x_81;
x_62 = x_77;
x_63 = x_89;
goto block_71;
}
else
{
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_27);
lean_dec(x_26);
x_31 = x_72;
x_32 = x_88;
goto block_39;
}
}
}
}
block_130:
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_array_get_size(x_26);
x_102 = lean_ctor_get(x_92, 4);
lean_inc(x_102);
lean_dec(x_92);
x_103 = lean_nat_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_104 = lean_mk_string_unchecked("invalid LCNF `cases`, `", 23, 23);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = l_Lean_MessageData_ofName(x_25);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked("` has # ", 8, 8);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Init_Data_Repr_0__Nat_reprFast(x_102);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked(" fields, but alternative has # ", 31, 31);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = l___private_Init_Data_Repr_0__Nat_reprFast(x_101);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_Lean_MessageData_ofFormat(x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked(" alternatives", 13, 13);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_124, x_97, x_98, x_99, x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_25);
x_72 = x_91;
x_73 = x_93;
x_74 = x_94;
x_75 = x_95;
x_76 = x_96;
x_77 = x_97;
x_78 = x_98;
x_79 = x_99;
x_80 = x_100;
goto block_90;
}
}
block_181:
{
lean_object* x_140; 
lean_inc(x_25);
x_140 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg(x_25, x_136, x_137, x_138, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_25);
x_143 = l_Lean_NameSet_insert(x_131, x_25);
if (lean_obj_tag(x_141) == 6)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
x_147 = lean_name_eq(x_145, x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_148 = lean_mk_string_unchecked("invalid LCNF `cases`, `", 23, 23);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
x_150 = l_Lean_MessageData_ofName(x_25);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_mk_string_unchecked("` is not a constructor of `", 27, 27);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_MessageData_ofName(x_146);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_string_unchecked("`", 1, 1);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_159, x_136, x_137, x_138, x_142);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
return x_160;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_160);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_dec(x_146);
x_91 = x_143;
x_92 = x_144;
x_93 = x_132;
x_94 = x_133;
x_95 = x_134;
x_96 = x_135;
x_97 = x_136;
x_98 = x_137;
x_99 = x_138;
x_100 = x_142;
goto block_130;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_165 = lean_mk_string_unchecked("invalid LCNF `cases`, `", 23, 23);
x_166 = l_Lean_stringToMessageData(x_165);
lean_dec(x_165);
x_167 = l_Lean_MessageData_ofName(x_25);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_mk_string_unchecked("` is not a constructor name", 27, 27);
x_170 = l_Lean_stringToMessageData(x_169);
lean_dec(x_169);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_171, x_136, x_137, x_138, x_142);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
return x_172;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_172);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_140);
if (x_177 == 0)
{
return x_140;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_140, 0);
x_179 = lean_ctor_get(x_140, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_140);
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
uint8_t x_195; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_28);
if (x_195 == 0)
{
return x_28;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_28, 0);
x_197 = lean_ctor_get(x_28, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_28);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_5, 0);
lean_inc(x_199);
lean_dec(x_5);
x_200 = lean_ctor_get(x_23, 0);
lean_inc(x_200);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_201 = l_Lean_Compiler_LCNF_Check_check(x_200, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_box(x_21);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_203);
x_14 = x_204;
x_15 = x_202;
goto block_20;
}
else
{
uint8_t x_205; 
lean_dec(x_199);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_201);
if (x_205 == 0)
{
return x_201;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_201, 0);
x_207 = lean_ctor_get(x_201, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_201);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
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
lean_dec(x_6);
lean_dec(x_1);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_5);
lean_ctor_set(x_22, 1, x_13);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_array_uget(x_2, x_4);
if (lean_obj_tag(x_23) == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_24 = lean_ctor_get(x_5, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_23, 1);
lean_inc(x_26);
x_27 = lean_ctor_get(x_23, 2);
lean_inc(x_27);
lean_dec(x_23);
x_28 = l_Lean_Compiler_LCNF_Check_checkParams(x_26, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; uint8_t x_182; 
x_29 = lean_ctor_get(x_28, 1);
lean_inc(x_29);
lean_dec(x_28);
x_30 = lean_ctor_get(x_5, 1);
lean_inc(x_30);
lean_dec(x_5);
x_182 = l_Lean_NameSet_contains(x_24, x_25);
if (x_182 == 0)
{
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_131 = x_24;
x_132 = x_6;
x_133 = x_7;
x_134 = x_8;
x_135 = x_9;
x_136 = x_10;
x_137 = x_11;
x_138 = x_12;
x_139 = x_29;
goto block_181;
}
else
{
lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; uint8_t x_191; 
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_24);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_183 = lean_mk_string_unchecked("invalid LCNF `cases`, alternative `", 35, 35);
x_184 = l_Lean_stringToMessageData(x_183);
lean_dec(x_183);
x_185 = l_Lean_MessageData_ofName(x_25);
x_186 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_186, 0, x_184);
lean_ctor_set(x_186, 1, x_185);
x_187 = lean_mk_string_unchecked("` occurs more than once", 23, 23);
x_188 = l_Lean_stringToMessageData(x_187);
lean_dec(x_187);
x_189 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_188);
x_190 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_189, x_10, x_11, x_12, x_29);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
x_191 = !lean_is_exclusive(x_190);
if (x_191 == 0)
{
return x_190;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; 
x_192 = lean_ctor_get(x_190, 0);
x_193 = lean_ctor_get(x_190, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_190);
x_194 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_194, 0, x_192);
lean_ctor_set(x_194, 1, x_193);
return x_194;
}
}
block_39:
{
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_30);
x_14 = x_34;
x_15 = x_33;
goto block_20;
}
else
{
uint8_t x_35; 
lean_dec(x_31);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_35 = !lean_is_exclusive(x_32);
if (x_35 == 0)
{
return x_32;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_32, 0);
x_37 = lean_ctor_get(x_32, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_32);
x_38 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
return x_38;
}
}
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_45);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_Compiler_LCNF_Check_check(x_27, x_50, x_47, x_46, x_43, x_41, x_40, x_44, x_48);
x_31 = x_42;
x_32 = x_51;
goto block_39;
}
block_71:
{
lean_object* x_64; lean_object* x_65; uint8_t x_66; 
x_64 = lean_ctor_get(x_62, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 1);
lean_inc(x_65);
lean_dec(x_62);
x_66 = lean_nat_dec_lt(x_59, x_53);
if (x_66 == 0)
{
lean_dec(x_53);
lean_dec(x_26);
x_40 = x_55;
x_41 = x_54;
x_42 = x_56;
x_43 = x_57;
x_44 = x_58;
x_45 = x_64;
x_46 = x_60;
x_47 = x_61;
x_48 = x_63;
x_49 = x_65;
goto block_52;
}
else
{
uint8_t x_67; 
x_67 = lean_nat_dec_le(x_53, x_53);
if (x_67 == 0)
{
lean_dec(x_53);
lean_dec(x_26);
x_40 = x_55;
x_41 = x_54;
x_42 = x_56;
x_43 = x_57;
x_44 = x_58;
x_45 = x_64;
x_46 = x_60;
x_47 = x_61;
x_48 = x_63;
x_49 = x_65;
goto block_52;
}
else
{
size_t x_68; size_t x_69; lean_object* x_70; 
x_68 = lean_usize_of_nat(x_59);
x_69 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_70 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0(x_26, x_68, x_69, x_65);
lean_dec(x_26);
x_40 = x_55;
x_41 = x_54;
x_42 = x_56;
x_43 = x_57;
x_44 = x_58;
x_45 = x_64;
x_46 = x_60;
x_47 = x_61;
x_48 = x_63;
x_49 = x_70;
goto block_52;
}
}
}
block_90:
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = lean_unsigned_to_nat(0u);
x_82 = lean_array_get_size(x_26);
x_83 = lean_nat_dec_lt(x_81, x_82);
if (x_83 == 0)
{
x_53 = x_82;
x_54 = x_77;
x_55 = x_78;
x_56 = x_72;
x_57 = x_76;
x_58 = x_79;
x_59 = x_81;
x_60 = x_75;
x_61 = x_74;
x_62 = x_73;
x_63 = x_80;
goto block_71;
}
else
{
uint8_t x_84; 
x_84 = lean_nat_dec_le(x_82, x_82);
if (x_84 == 0)
{
x_53 = x_82;
x_54 = x_77;
x_55 = x_78;
x_56 = x_72;
x_57 = x_76;
x_58 = x_79;
x_59 = x_81;
x_60 = x_75;
x_61 = x_74;
x_62 = x_73;
x_63 = x_80;
goto block_71;
}
else
{
lean_object* x_85; size_t x_86; size_t x_87; lean_object* x_88; 
x_85 = lean_box(0);
x_86 = lean_usize_of_nat(x_81);
x_87 = lean_usize_of_nat(x_82);
x_88 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg(x_26, x_86, x_87, x_85, x_74, x_77, x_78, x_79, x_80);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_89; 
x_89 = lean_ctor_get(x_88, 1);
lean_inc(x_89);
lean_dec(x_88);
x_53 = x_82;
x_54 = x_77;
x_55 = x_78;
x_56 = x_72;
x_57 = x_76;
x_58 = x_79;
x_59 = x_81;
x_60 = x_75;
x_61 = x_74;
x_62 = x_73;
x_63 = x_89;
goto block_71;
}
else
{
lean_dec(x_82);
lean_dec(x_79);
lean_dec(x_78);
lean_dec(x_77);
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_73);
lean_dec(x_27);
lean_dec(x_26);
x_31 = x_72;
x_32 = x_88;
goto block_39;
}
}
}
}
block_130:
{
lean_object* x_101; lean_object* x_102; uint8_t x_103; 
x_101 = lean_array_get_size(x_26);
x_102 = lean_ctor_get(x_91, 4);
lean_inc(x_102);
lean_dec(x_91);
x_103 = lean_nat_dec_eq(x_101, x_102);
if (x_103 == 0)
{
lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; uint8_t x_126; 
lean_dec(x_96);
lean_dec(x_95);
lean_dec(x_93);
lean_dec(x_92);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_104 = lean_mk_string_unchecked("invalid LCNF `cases`, `", 23, 23);
x_105 = l_Lean_stringToMessageData(x_104);
lean_dec(x_104);
x_106 = l_Lean_MessageData_ofName(x_25);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_mk_string_unchecked("` has # ", 8, 8);
x_109 = l_Lean_stringToMessageData(x_108);
lean_dec(x_108);
x_110 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_110, 0, x_107);
lean_ctor_set(x_110, 1, x_109);
x_111 = l___private_Init_Data_Repr_0__Nat_reprFast(x_102);
x_112 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_112, 0, x_111);
x_113 = l_Lean_MessageData_ofFormat(x_112);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_110);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_mk_string_unchecked(" fields, but alternative has # ", 31, 31);
x_116 = l_Lean_stringToMessageData(x_115);
lean_dec(x_115);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_114);
lean_ctor_set(x_117, 1, x_116);
x_118 = l___private_Init_Data_Repr_0__Nat_reprFast(x_101);
x_119 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_119, 0, x_118);
x_120 = l_Lean_MessageData_ofFormat(x_119);
x_121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_121, 0, x_117);
lean_ctor_set(x_121, 1, x_120);
x_122 = lean_mk_string_unchecked(" alternatives", 13, 13);
x_123 = l_Lean_stringToMessageData(x_122);
lean_dec(x_122);
x_124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_124, 0, x_121);
lean_ctor_set(x_124, 1, x_123);
x_125 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_124, x_97, x_98, x_99, x_100);
lean_dec(x_99);
lean_dec(x_98);
lean_dec(x_97);
x_126 = !lean_is_exclusive(x_125);
if (x_126 == 0)
{
return x_125;
}
else
{
lean_object* x_127; lean_object* x_128; lean_object* x_129; 
x_127 = lean_ctor_get(x_125, 0);
x_128 = lean_ctor_get(x_125, 1);
lean_inc(x_128);
lean_inc(x_127);
lean_dec(x_125);
x_129 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_129, 0, x_127);
lean_ctor_set(x_129, 1, x_128);
return x_129;
}
}
else
{
lean_dec(x_102);
lean_dec(x_101);
lean_dec(x_25);
x_72 = x_92;
x_73 = x_93;
x_74 = x_94;
x_75 = x_95;
x_76 = x_96;
x_77 = x_97;
x_78 = x_98;
x_79 = x_99;
x_80 = x_100;
goto block_90;
}
}
block_181:
{
lean_object* x_140; 
lean_inc(x_25);
x_140 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg(x_25, x_136, x_137, x_138, x_139);
if (lean_obj_tag(x_140) == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_140, 0);
lean_inc(x_141);
x_142 = lean_ctor_get(x_140, 1);
lean_inc(x_142);
lean_dec(x_140);
lean_inc(x_25);
x_143 = l_Lean_NameSet_insert(x_131, x_25);
if (lean_obj_tag(x_141) == 6)
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; uint8_t x_147; 
x_144 = lean_ctor_get(x_141, 0);
lean_inc(x_144);
lean_dec(x_141);
x_145 = lean_ctor_get(x_144, 1);
lean_inc(x_145);
x_146 = lean_ctor_get(x_1, 0);
lean_inc(x_146);
x_147 = lean_name_eq(x_145, x_146);
lean_dec(x_145);
if (x_147 == 0)
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; uint8_t x_161; 
lean_dec(x_144);
lean_dec(x_143);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_148 = lean_mk_string_unchecked("invalid LCNF `cases`, `", 23, 23);
x_149 = l_Lean_stringToMessageData(x_148);
lean_dec(x_148);
x_150 = l_Lean_MessageData_ofName(x_25);
x_151 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_151, 0, x_149);
lean_ctor_set(x_151, 1, x_150);
x_152 = lean_mk_string_unchecked("` is not a constructor of `", 27, 27);
x_153 = l_Lean_stringToMessageData(x_152);
lean_dec(x_152);
x_154 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_154, 0, x_151);
lean_ctor_set(x_154, 1, x_153);
x_155 = l_Lean_MessageData_ofName(x_146);
x_156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_156, 0, x_154);
lean_ctor_set(x_156, 1, x_155);
x_157 = lean_mk_string_unchecked("`", 1, 1);
x_158 = l_Lean_stringToMessageData(x_157);
lean_dec(x_157);
x_159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_159, x_136, x_137, x_138, x_142);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
x_161 = !lean_is_exclusive(x_160);
if (x_161 == 0)
{
return x_160;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; 
x_162 = lean_ctor_get(x_160, 0);
x_163 = lean_ctor_get(x_160, 1);
lean_inc(x_163);
lean_inc(x_162);
lean_dec(x_160);
x_164 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_164, 0, x_162);
lean_ctor_set(x_164, 1, x_163);
return x_164;
}
}
else
{
lean_dec(x_146);
x_91 = x_144;
x_92 = x_143;
x_93 = x_132;
x_94 = x_133;
x_95 = x_134;
x_96 = x_135;
x_97 = x_136;
x_98 = x_137;
x_99 = x_138;
x_100 = x_142;
goto block_130;
}
}
else
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; uint8_t x_173; 
lean_dec(x_143);
lean_dec(x_141);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_165 = lean_mk_string_unchecked("invalid LCNF `cases`, `", 23, 23);
x_166 = l_Lean_stringToMessageData(x_165);
lean_dec(x_165);
x_167 = l_Lean_MessageData_ofName(x_25);
x_168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
x_169 = lean_mk_string_unchecked("` is not a constructor name", 27, 27);
x_170 = l_Lean_stringToMessageData(x_169);
lean_dec(x_169);
x_171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_171, 0, x_168);
lean_ctor_set(x_171, 1, x_170);
x_172 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_171, x_136, x_137, x_138, x_142);
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
x_173 = !lean_is_exclusive(x_172);
if (x_173 == 0)
{
return x_172;
}
else
{
lean_object* x_174; lean_object* x_175; lean_object* x_176; 
x_174 = lean_ctor_get(x_172, 0);
x_175 = lean_ctor_get(x_172, 1);
lean_inc(x_175);
lean_inc(x_174);
lean_dec(x_172);
x_176 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_176, 0, x_174);
lean_ctor_set(x_176, 1, x_175);
return x_176;
}
}
}
else
{
uint8_t x_177; 
lean_dec(x_138);
lean_dec(x_137);
lean_dec(x_136);
lean_dec(x_135);
lean_dec(x_134);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_30);
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_177 = !lean_is_exclusive(x_140);
if (x_177 == 0)
{
return x_140;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; 
x_178 = lean_ctor_get(x_140, 0);
x_179 = lean_ctor_get(x_140, 1);
lean_inc(x_179);
lean_inc(x_178);
lean_dec(x_140);
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
uint8_t x_195; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_25);
lean_dec(x_24);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_28);
if (x_195 == 0)
{
return x_28;
}
else
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; 
x_196 = lean_ctor_get(x_28, 0);
x_197 = lean_ctor_get(x_28, 1);
lean_inc(x_197);
lean_inc(x_196);
lean_dec(x_28);
x_198 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_198, 0, x_196);
lean_ctor_set(x_198, 1, x_197);
return x_198;
}
}
}
else
{
lean_object* x_199; lean_object* x_200; lean_object* x_201; 
x_199 = lean_ctor_get(x_5, 0);
lean_inc(x_199);
lean_dec(x_5);
x_200 = lean_ctor_get(x_23, 0);
lean_inc(x_200);
lean_dec(x_23);
lean_inc(x_12);
lean_inc(x_11);
lean_inc(x_10);
lean_inc(x_9);
lean_inc(x_8);
lean_inc(x_6);
x_201 = l_Lean_Compiler_LCNF_Check_check(x_200, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
if (lean_obj_tag(x_201) == 0)
{
lean_object* x_202; lean_object* x_203; lean_object* x_204; 
x_202 = lean_ctor_get(x_201, 1);
lean_inc(x_202);
lean_dec(x_201);
x_203 = lean_box(x_21);
x_204 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_204, 0, x_199);
lean_ctor_set(x_204, 1, x_203);
x_14 = x_204;
x_15 = x_202;
goto block_20;
}
else
{
uint8_t x_205; 
lean_dec(x_199);
lean_dec(x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_1);
x_205 = !lean_is_exclusive(x_201);
if (x_205 == 0)
{
return x_201;
}
else
{
lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_206 = lean_ctor_get(x_201, 0);
x_207 = lean_ctor_get(x_201, 1);
lean_inc(x_207);
lean_inc(x_206);
lean_dec(x_201);
x_208 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_208, 0, x_206);
lean_ctor_set(x_208, 1, x_207);
return x_208;
}
}
}
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_4, x_17);
x_19 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1_spec__1(x_1, x_2, x_3, x_18, x_14, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_15);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkCases(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_1, 2);
lean_inc(x_10);
x_11 = l_Lean_Compiler_LCNF_Check_checkFVar(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_11) == 0)
{
uint8_t x_12; 
x_12 = !lean_is_exclusive(x_11);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; size_t x_20; lean_object* x_21; 
x_13 = lean_ctor_get(x_11, 1);
x_14 = lean_ctor_get(x_11, 0);
lean_dec(x_14);
x_15 = lean_box(0);
x_16 = lean_box(0);
x_17 = lean_ctor_get(x_1, 3);
lean_inc(x_17);
lean_ctor_set(x_11, 1, x_16);
lean_ctor_set(x_11, 0, x_15);
x_18 = lean_array_size(x_17);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_usize_of_nat(x_19);
x_21 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1(x_1, x_17, x_18, x_20, x_11, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_13);
lean_dec(x_17);
if (lean_obj_tag(x_21) == 0)
{
uint8_t x_22; 
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
lean_dec(x_23);
x_24 = lean_box(0);
lean_ctor_set(x_21, 0, x_24);
return x_21;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_dec(x_21);
x_26 = lean_box(0);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8_t x_28; 
x_28 = !lean_is_exclusive(x_21);
if (x_28 == 0)
{
return x_21;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_21, 0);
x_30 = lean_ctor_get(x_21, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_21);
x_31 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
return x_31;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; lean_object* x_38; size_t x_39; lean_object* x_40; 
x_32 = lean_ctor_get(x_11, 1);
lean_inc(x_32);
lean_dec(x_11);
x_33 = lean_box(0);
x_34 = lean_box(0);
x_35 = lean_ctor_get(x_1, 3);
lean_inc(x_35);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_34);
x_37 = lean_array_size(x_35);
x_38 = lean_unsigned_to_nat(0u);
x_39 = lean_usize_of_nat(x_38);
x_40 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1(x_1, x_35, x_37, x_39, x_36, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_32);
lean_dec(x_35);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
x_41 = lean_ctor_get(x_40, 1);
lean_inc(x_41);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_42 = x_40;
} else {
 lean_dec_ref(x_40);
 x_42 = lean_box(0);
}
x_43 = lean_box(0);
if (lean_is_scalar(x_42)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_42;
}
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_41);
return x_44;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_45 = lean_ctor_get(x_40, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 lean_ctor_release(x_40, 1);
 x_47 = x_40;
} else {
 lean_dec_ref(x_40);
 x_47 = lean_box(0);
}
if (lean_is_scalar(x_47)) {
 x_48 = lean_alloc_ctor(1, 2, 0);
} else {
 x_48 = x_47;
}
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_46);
return x_48;
}
}
}
else
{
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_10 = lean_ctor_get(x_1, 1);
lean_inc(x_10);
x_11 = lean_ctor_get(x_1, 2);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 3);
lean_inc(x_12);
x_13 = lean_ctor_get(x_1, 4);
lean_inc(x_13);
lean_inc(x_8);
lean_inc(x_7);
lean_inc(x_6);
lean_inc(x_5);
lean_inc(x_12);
lean_inc(x_10);
x_14 = l_Lean_Compiler_LCNF_Check_checkFunDeclCore(x_10, x_11, x_12, x_13, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_55; 
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
if (lean_is_exclusive(x_14)) {
 lean_ctor_release(x_14, 0);
 lean_ctor_release(x_14, 1);
 x_16 = x_14;
} else {
 lean_dec_ref(x_14);
 x_16 = lean_box(0);
}
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
lean_inc(x_17);
x_55 = l_Lean_Compiler_LCNF_getFunDecl(x_17, x_5, x_6, x_7, x_8, x_15);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_84; uint8_t x_85; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_55, 1);
lean_inc(x_57);
lean_dec(x_55);
x_84 = lean_ctor_get(x_56, 1);
lean_inc(x_84);
x_85 = lean_name_eq(x_84, x_10);
if (x_85 == 0)
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; 
lean_dec(x_56);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_5);
lean_dec(x_1);
x_86 = lean_mk_string_unchecked("LCNF local function declaration mismatch at `", 45, 45);
x_87 = l_Lean_stringToMessageData(x_86);
lean_dec(x_86);
x_88 = l_Lean_MessageData_ofName(x_10);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = lean_mk_string_unchecked("`, binder name in local context `", 33, 33);
x_91 = l_Lean_stringToMessageData(x_90);
lean_dec(x_90);
x_92 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_92, 0, x_89);
lean_ctor_set(x_92, 1, x_91);
x_93 = l_Lean_MessageData_ofName(x_84);
x_94 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_94, 0, x_92);
lean_ctor_set(x_94, 1, x_93);
x_95 = lean_mk_string_unchecked("`", 1, 1);
x_96 = l_Lean_stringToMessageData(x_95);
lean_dec(x_95);
x_97 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_97, 0, x_94);
lean_ctor_set(x_97, 1, x_96);
x_98 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_97, x_6, x_7, x_8, x_57);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
return x_98;
}
else
{
lean_dec(x_84);
x_58 = x_5;
x_59 = x_6;
x_60 = x_7;
x_61 = x_8;
x_62 = x_57;
goto block_83;
}
block_83:
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_56, 3);
lean_inc(x_63);
lean_dec(x_56);
x_64 = lean_expr_eqv(x_63, x_12);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
lean_dec(x_58);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_1);
x_65 = lean_mk_string_unchecked("LCNF local function declaration mismatch at `", 45, 45);
x_66 = l_Lean_stringToMessageData(x_65);
lean_dec(x_65);
x_67 = l_Lean_MessageData_ofName(x_10);
x_68 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
x_69 = lean_mk_string_unchecked("`, type in local context", 24, 24);
x_70 = l_Lean_stringToMessageData(x_69);
lean_dec(x_69);
x_71 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_71, 0, x_68);
lean_ctor_set(x_71, 1, x_70);
x_72 = l_Lean_indentExpr(x_63);
x_73 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_73, 0, x_71);
lean_ctor_set(x_73, 1, x_72);
x_74 = lean_mk_string_unchecked("\nexpected", 9, 9);
x_75 = l_Lean_stringToMessageData(x_74);
lean_dec(x_74);
x_76 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_76, 0, x_73);
lean_ctor_set(x_76, 1, x_75);
x_77 = l_Lean_indentExpr(x_12);
x_78 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_78, 0, x_76);
lean_ctor_set(x_78, 1, x_77);
x_79 = lean_mk_string_unchecked("", 0, 0);
x_80 = l_Lean_stringToMessageData(x_79);
lean_dec(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_78);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_81, x_59, x_60, x_61, x_62);
lean_dec(x_61);
lean_dec(x_60);
lean_dec(x_59);
return x_82;
}
else
{
lean_dec(x_63);
lean_dec(x_12);
x_18 = x_58;
x_19 = x_59;
x_20 = x_60;
x_21 = x_61;
x_22 = x_62;
goto block_54;
}
}
}
else
{
uint8_t x_99; 
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_99 = !lean_is_exclusive(x_55);
if (x_99 == 0)
{
return x_55;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; 
x_100 = lean_ctor_get(x_55, 0);
x_101 = lean_ctor_get(x_55, 1);
lean_inc(x_101);
lean_inc(x_100);
lean_dec(x_55);
x_102 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_102, 0, x_100);
lean_ctor_set(x_102, 1, x_101);
return x_102;
}
}
block_54:
{
lean_object* x_23; 
x_23 = l_Lean_Compiler_LCNF_getFunDecl(x_17, x_18, x_19, x_20, x_21, x_22);
lean_dec(x_18);
if (lean_obj_tag(x_23) == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_23);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; 
x_25 = lean_ctor_get(x_23, 0);
x_26 = lean_ctor_get(x_23, 1);
x_27 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(x_25, x_1);
lean_dec(x_1);
lean_dec(x_25);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_23);
x_28 = lean_mk_string_unchecked("LCNF local function declaration mismatch at `", 45, 45);
x_29 = l_Lean_stringToMessageData(x_28);
lean_dec(x_28);
x_30 = l_Lean_MessageData_ofName(x_10);
if (lean_is_scalar(x_16)) {
 x_31 = lean_alloc_ctor(7, 2, 0);
} else {
 x_31 = x_16;
 lean_ctor_set_tag(x_31, 7);
}
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = lean_mk_string_unchecked("`, declaration in local context does match", 42, 42);
x_33 = l_Lean_stringToMessageData(x_32);
lean_dec(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_34, x_19, x_20, x_21, x_26);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_35;
}
else
{
lean_object* x_36; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_10);
x_36 = lean_box(0);
lean_ctor_set(x_23, 0, x_36);
return x_23;
}
}
else
{
lean_object* x_37; lean_object* x_38; uint8_t x_39; 
x_37 = lean_ctor_get(x_23, 0);
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
lean_inc(x_37);
lean_dec(x_23);
x_39 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_eqFunDecl(x_37, x_1);
lean_dec(x_1);
lean_dec(x_37);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
x_40 = lean_mk_string_unchecked("LCNF local function declaration mismatch at `", 45, 45);
x_41 = l_Lean_stringToMessageData(x_40);
lean_dec(x_40);
x_42 = l_Lean_MessageData_ofName(x_10);
if (lean_is_scalar(x_16)) {
 x_43 = lean_alloc_ctor(7, 2, 0);
} else {
 x_43 = x_16;
 lean_ctor_set_tag(x_43, 7);
}
lean_ctor_set(x_43, 0, x_41);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_mk_string_unchecked("`, declaration in local context does match", 42, 42);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_46, 0, x_43);
lean_ctor_set(x_46, 1, x_45);
x_47 = l_Lean_throwError___at___Lean_Compiler_LCNF_Check_checkFVar_spec__0___redArg(x_46, x_19, x_20, x_21, x_38);
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_10);
x_48 = lean_box(0);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_38);
return x_49;
}
}
}
else
{
uint8_t x_50; 
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_10);
lean_dec(x_1);
x_50 = !lean_is_exclusive(x_23);
if (x_50 == 0)
{
return x_23;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; 
x_51 = lean_ctor_get(x_23, 0);
x_52 = lean_ctor_get(x_23, 1);
lean_inc(x_52);
lean_inc(x_51);
lean_dec(x_23);
x_53 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_53, 0, x_51);
lean_ctor_set(x_53, 1, x_52);
return x_53;
}
}
}
}
else
{
lean_dec(x_12);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__0(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___redArg(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
size_t x_13; size_t x_14; lean_object* x_15; 
x_13 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Check_checkFunDeclCore_spec__1(x_1, x_13, x_14, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDeclCore___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Lean_Compiler_LCNF_Check_checkFunDeclCore(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_check___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_check(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___redArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_getConstInfo___at___Lean_Compiler_LCNF_Check_checkCases_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1_spec__1(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Check_checkCases_spec__1(x_1, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13);
lean_dec(x_7);
lean_dec(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkCases___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkCases(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_checkFunDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Compiler_LCNF_Check_checkFunDecl(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; lean_object* x_19; lean_object* x_20; size_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_7, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_unsigned_to_nat(5u);
x_18 = lean_usize_of_nat(x_17);
x_19 = lean_usize_to_nat(x_18);
x_20 = lean_nat_pow(x_9, x_19);
lean_dec(x_19);
x_21 = lean_usize_of_nat(x_20);
lean_dec(x_20);
x_22 = lean_usize_to_nat(x_21);
x_23 = lean_mk_empty_array_with_capacity(x_22);
lean_dec(x_22);
x_24 = lean_st_mk_ref(x_16, x_6);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_26 = lean_ctor_get(x_24, 0);
x_27 = lean_ctor_get(x_24, 1);
x_28 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_23);
x_29 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_29, 0, x_23);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_28);
x_32 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_32, 0, x_29);
lean_ctor_set(x_32, 1, x_23);
lean_ctor_set(x_32, 2, x_8);
lean_ctor_set(x_32, 3, x_8);
lean_ctor_set_usize(x_32, 4, x_18);
lean_ctor_set(x_24, 1, x_30);
lean_ctor_set(x_24, 0, x_30);
x_33 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_30);
lean_inc(x_26);
x_34 = lean_apply_8(x_1, x_24, x_26, x_33, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
x_35 = lean_ctor_get(x_34, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_34, 1);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_st_ref_get(x_26, x_36);
lean_dec(x_26);
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
lean_dec(x_39);
lean_ctor_set(x_37, 0, x_35);
return x_37;
}
else
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_37, 1);
lean_inc(x_40);
lean_dec(x_37);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_35);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
else
{
lean_dec(x_26);
return x_34;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_42 = lean_ctor_get(x_24, 0);
x_43 = lean_ctor_get(x_24, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_24);
x_44 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
lean_inc(x_23);
x_45 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_45, 0, x_23);
x_46 = lean_box(0);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_44);
x_48 = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_23);
lean_ctor_set(x_48, 2, x_8);
lean_ctor_set(x_48, 3, x_8);
lean_ctor_set_usize(x_48, 4, x_18);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_46);
lean_ctor_set(x_49, 1, x_46);
x_50 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_48);
lean_ctor_set(x_50, 2, x_46);
lean_inc(x_42);
x_51 = lean_apply_8(x_1, x_49, x_42, x_50, x_2, x_3, x_4, x_5, x_43);
if (lean_obj_tag(x_51) == 0)
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_52 = lean_ctor_get(x_51, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_51, 1);
lean_inc(x_53);
lean_dec(x_51);
x_54 = lean_st_ref_get(x_42, x_53);
lean_dec(x_42);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_56 = x_54;
} else {
 lean_dec_ref(x_54);
 x_56 = lean_box(0);
}
if (lean_is_scalar(x_56)) {
 x_57 = lean_alloc_ctor(0, 2, 0);
} else {
 x_57 = x_56;
}
lean_ctor_set(x_57, 0, x_52);
lean_ctor_set(x_57, 1, x_55);
return x_57;
}
else
{
lean_dec(x_42);
return x_51;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Check_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_Check_run___redArg(x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_Decl_check_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_2, 0);
lean_inc(x_11);
lean_dec(x_2);
x_12 = lean_apply_9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_10);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_check(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_7 = lean_ctor_get(x_1, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_1, 3);
lean_inc(x_8);
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
x_10 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_Check_checkFunDeclCore___boxed), 12, 3);
lean_closure_set(x_10, 0, x_7);
lean_closure_set(x_10, 1, x_8);
lean_closure_set(x_10, 2, x_9);
x_11 = lean_ctor_get(x_1, 4);
lean_inc(x_11);
lean_dec(x_1);
x_12 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_Decl_check_spec__0), 10, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = l_Lean_Compiler_LCNF_Check_run___redArg(x_12, x_2, x_3, x_4, x_5, x_6);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitFVar(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint64_t x_7; lean_object* x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; lean_object* x_12; uint64_t x_13; uint64_t x_14; uint64_t x_15; size_t x_16; size_t x_17; lean_object* x_18; size_t x_19; size_t x_20; size_t x_21; lean_object* x_22; uint8_t x_23; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = lean_array_get_size(x_4);
x_7 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_22 = lean_array_uget(x_4, x_21);
x_23 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_22);
if (x_23 == 0)
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_2);
if (x_24 == 0)
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_25 = lean_ctor_get(x_2, 1);
lean_dec(x_25);
x_26 = lean_ctor_get(x_2, 0);
lean_dec(x_26);
x_27 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_28 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_28, 0, x_1);
lean_ctor_set(x_28, 1, x_5);
lean_ctor_set(x_28, 2, x_22);
x_29 = lean_array_uset(x_4, x_21, x_28);
x_30 = lean_unsigned_to_nat(2u);
x_31 = lean_nat_shiftl(x_27, x_30);
x_32 = lean_unsigned_to_nat(3u);
x_33 = lean_nat_div(x_31, x_32);
lean_dec(x_31);
x_34 = lean_array_get_size(x_29);
x_35 = lean_nat_dec_le(x_33, x_34);
lean_dec(x_34);
lean_dec(x_33);
if (x_35 == 0)
{
lean_object* x_36; lean_object* x_37; 
x_36 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_29);
lean_ctor_set(x_2, 1, x_36);
lean_ctor_set(x_2, 0, x_27);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_5);
lean_ctor_set(x_37, 1, x_2);
return x_37;
}
else
{
lean_object* x_38; 
lean_ctor_set(x_2, 1, x_29);
lean_ctor_set(x_2, 0, x_27);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_5);
lean_ctor_set(x_38, 1, x_2);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
lean_dec(x_2);
x_39 = lean_nat_add(x_3, x_18);
lean_dec(x_3);
x_40 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_40, 0, x_1);
lean_ctor_set(x_40, 1, x_5);
lean_ctor_set(x_40, 2, x_22);
x_41 = lean_array_uset(x_4, x_21, x_40);
x_42 = lean_unsigned_to_nat(2u);
x_43 = lean_nat_shiftl(x_39, x_42);
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_div(x_43, x_44);
lean_dec(x_43);
x_46 = lean_array_get_size(x_41);
x_47 = lean_nat_dec_le(x_45, x_46);
lean_dec(x_46);
lean_dec(x_45);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_41);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_39);
lean_ctor_set(x_49, 1, x_48);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_5);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_51, 0, x_39);
lean_ctor_set(x_51, 1, x_41);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_5);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
else
{
lean_object* x_53; 
lean_dec(x_22);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_53 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_53, 0, x_5);
lean_ctor_set(x_53, 1, x_2);
return x_53;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParam(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitFVar(x_3, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParam(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_box(0);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams_spec__0(x_1, x_10, x_11, x_5, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_14; 
x_14 = lean_usize_dec_eq(x_2, x_3);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_4);
x_15 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 2);
lean_inc(x_17);
lean_dec(x_15);
x_18 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams(x_16, x_5);
lean_dec(x_16);
x_19 = lean_ctor_get(x_18, 1);
lean_inc(x_19);
lean_dec(x_18);
x_20 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode(x_17, x_19);
x_6 = x_20;
goto block_13;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_15, 0);
lean_inc(x_21);
lean_dec(x_15);
x_22 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode(x_21, x_5);
x_6 = x_22;
goto block_13;
}
}
else
{
lean_object* x_23; 
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_4);
lean_ctor_set(x_23, 1, x_5);
return x_23;
}
block_13:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; size_t x_10; size_t x_11; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
lean_dec(x_6);
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_usize_of_nat(x_9);
x_11 = lean_usize_add(x_2, x_10);
x_2 = x_11;
x_4 = x_7;
x_5 = x_8;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc(x_17);
x_18 = lean_ctor_get(x_1, 1);
lean_inc(x_18);
lean_dec(x_1);
x_19 = lean_ctor_get(x_17, 0);
lean_inc(x_19);
lean_dec(x_17);
x_20 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitFVar(x_19, x_2);
x_21 = lean_ctor_get(x_20, 1);
lean_inc(x_21);
lean_dec(x_20);
x_1 = x_18;
x_2 = x_21;
goto _start;
}
case 1:
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_3 = x_23;
x_4 = x_24;
x_5 = x_2;
goto block_16;
}
case 2:
{
lean_object* x_25; lean_object* x_26; 
x_25 = lean_ctor_get(x_1, 0);
lean_inc(x_25);
x_26 = lean_ctor_get(x_1, 1);
lean_inc(x_26);
lean_dec(x_1);
x_3 = x_25;
x_4 = x_26;
x_5 = x_2;
goto block_16;
}
case 4:
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; uint8_t x_32; 
x_27 = lean_ctor_get(x_1, 0);
lean_inc(x_27);
lean_dec(x_1);
x_28 = lean_ctor_get(x_27, 3);
lean_inc(x_28);
lean_dec(x_27);
x_29 = lean_unsigned_to_nat(0u);
x_30 = lean_array_get_size(x_28);
x_31 = lean_box(0);
x_32 = lean_nat_dec_lt(x_29, x_30);
if (x_32 == 0)
{
lean_object* x_33; 
lean_dec(x_30);
lean_dec(x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_2);
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
lean_dec(x_28);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_31);
lean_ctor_set(x_35, 1, x_2);
return x_35;
}
else
{
size_t x_36; size_t x_37; lean_object* x_38; 
x_36 = lean_usize_of_nat(x_29);
x_37 = lean_usize_of_nat(x_30);
lean_dec(x_30);
x_38 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode_spec__0(x_28, x_36, x_37, x_31, x_2);
lean_dec(x_28);
return x_38;
}
}
}
default: 
{
lean_object* x_39; lean_object* x_40; 
lean_dec(x_1);
x_39 = lean_box(0);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_2);
return x_40;
}
}
block_16:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_6 = lean_ctor_get(x_3, 0);
lean_inc(x_6);
x_7 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitFVar(x_6, x_5);
x_8 = lean_ctor_get(x_7, 1);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ctor_get(x_3, 2);
lean_inc(x_9);
x_10 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams(x_9, x_8);
lean_dec(x_9);
x_11 = lean_ctor_get(x_10, 1);
lean_inc(x_11);
lean_dec(x_10);
x_12 = lean_ctor_get(x_3, 4);
lean_inc(x_12);
lean_dec(x_3);
x_13 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode(x_12, x_11);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_1 = x_4;
x_2 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecl_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
lean_dec(x_1);
x_6 = lean_box(0);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_3);
return x_7;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecl(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_1, 3);
lean_inc(x_3);
x_4 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitParams(x_3, x_2);
lean_dec(x_3);
x_5 = lean_ctor_get(x_4, 1);
lean_inc(x_5);
lean_dec(x_4);
x_6 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitCode), 2, 0);
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
lean_dec(x_1);
x_8 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecl_spec__0(x_6, x_7, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_eq(x_2, x_3);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; size_t x_12; size_t x_13; 
lean_dec(x_4);
x_7 = lean_array_uget(x_1, x_2);
x_8 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecl(x_7, x_5);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
x_10 = lean_ctor_get(x_8, 1);
lean_inc(x_10);
lean_dec(x_8);
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_2, x_12);
x_2 = x_13;
x_4 = x_9;
x_5 = x_10;
goto _start;
}
else
{
lean_object* x_15; 
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_4);
lean_ctor_set(x_15, 1, x_5);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_array_get_size(x_1);
x_5 = lean_box(0);
x_6 = lean_nat_dec_lt(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; 
lean_dec(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_5);
lean_ctor_set(x_7, 1, x_2);
return x_7;
}
else
{
uint8_t x_8; 
x_8 = lean_nat_dec_le(x_4, x_4);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_5);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
else
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_usize_of_nat(x_3);
x_11 = lean_usize_of_nat(x_4);
lean_dec(x_4);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls_spec__0(x_1, x_10, x_11, x_5, x_2);
return x_12;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls_spec__0(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_10);
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
x_39 = lean_mk_string_unchecked("`", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_41, x_4, x_5, x_6, x_7, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_43);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("`", 1, 1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_50, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_11);
x_52 = lean_box(0);
x_2 = x_52;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_10);
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
x_39 = lean_mk_string_unchecked("`", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_41, x_4, x_5, x_6, x_7, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_43);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("`", 1, 1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_50, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
x_52 = lean_box(0);
x_53 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0_spec__0(x_1, x_52, x_12, x_4, x_5, x_6, x_7, x_8);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_10);
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
x_39 = lean_mk_string_unchecked("`", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_41, x_4, x_5, x_6, x_7, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_43);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("`", 1, 1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_50, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_11);
x_52 = lean_box(0);
x_2 = x_52;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_10);
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
x_39 = lean_mk_string_unchecked("`", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_41, x_4, x_5, x_6, x_7, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_43);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("`", 1, 1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_50, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
x_52 = lean_box(0);
x_53 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2_spec__2(x_1, x_52, x_12, x_4, x_5, x_6, x_7, x_8);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_10);
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
x_39 = lean_mk_string_unchecked("`", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_41, x_4, x_5, x_6, x_7, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_43);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("`", 1, 1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_50, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
else
{
lean_object* x_52; 
lean_dec(x_11);
x_52 = lean_box(0);
x_2 = x_52;
x_3 = x_12;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_9; 
lean_dec(x_1);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_2);
lean_ctor_set(x_9, 1, x_8);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
lean_dec(x_2);
x_10 = lean_ctor_get(x_3, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_3, 1);
lean_inc(x_11);
x_12 = lean_ctor_get(x_3, 2);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_ctor_get(x_1, 1);
lean_inc(x_13);
x_14 = lean_array_get_size(x_13);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_10);
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
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_10, x_30);
lean_dec(x_30);
lean_dec(x_10);
if (x_31 == 0)
{
uint8_t x_32; 
lean_dec(x_12);
x_32 = !lean_is_exclusive(x_1);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_33 = lean_ctor_get(x_1, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_1, 0);
lean_dec(x_34);
x_35 = lean_ctor_get(x_11, 1);
lean_inc(x_35);
lean_dec(x_11);
x_36 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_37 = l_Lean_stringToMessageData(x_36);
lean_dec(x_36);
x_38 = l_Lean_MessageData_ofName(x_35);
lean_ctor_set_tag(x_1, 7);
lean_ctor_set(x_1, 1, x_38);
lean_ctor_set(x_1, 0, x_37);
x_39 = lean_mk_string_unchecked("`", 1, 1);
x_40 = l_Lean_stringToMessageData(x_39);
lean_dec(x_39);
x_41 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_41, 0, x_1);
lean_ctor_set(x_41, 1, x_40);
x_42 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_41, x_4, x_5, x_6, x_7, x_8);
return x_42;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_1);
x_43 = lean_ctor_get(x_11, 1);
lean_inc(x_43);
lean_dec(x_11);
x_44 = lean_mk_string_unchecked("LCNF local context contains unused local variable declaration `", 63, 63);
x_45 = l_Lean_stringToMessageData(x_44);
lean_dec(x_44);
x_46 = l_Lean_MessageData_ofName(x_43);
x_47 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_47, 0, x_45);
lean_ctor_set(x_47, 1, x_46);
x_48 = lean_mk_string_unchecked("`", 1, 1);
x_49 = l_Lean_stringToMessageData(x_48);
lean_dec(x_48);
x_50 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_50, 0, x_47);
lean_ctor_set(x_50, 1, x_49);
x_51 = l_Lean_throwError___at___Lean_Compiler_LCNF_getType_spec__1(lean_box(0), x_50, x_4, x_5, x_6, x_7, x_8);
return x_51;
}
}
else
{
lean_object* x_52; lean_object* x_53; 
lean_dec(x_11);
x_52 = lean_box(0);
x_53 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4_spec__4(x_1, x_52, x_12, x_4, x_5, x_6, x_7, x_8);
return x_53;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__6(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_box(0);
lean_inc(x_1);
x_14 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4(x_1, x_13, x_12, x_6, x_7, x_8, x_9, x_10);
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
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_15;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__7(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_box(0);
lean_inc(x_1);
x_14 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2(x_1, x_13, x_12, x_6, x_7, x_8, x_9, x_10);
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
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_15;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__8(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; 
x_11 = lean_usize_dec_eq(x_3, x_4);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
lean_dec(x_5);
x_12 = lean_array_uget(x_2, x_3);
x_13 = lean_box(0);
lean_inc(x_1);
x_14 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0(x_1, x_13, x_12, x_6, x_7, x_8, x_9, x_10);
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
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_5 = x_15;
x_10 = x_16;
goto _start;
}
else
{
lean_dec(x_1);
return x_14;
}
}
else
{
lean_object* x_21; 
lean_dec(x_1);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_10);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_37; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; 
x_7 = lean_unsigned_to_nat(8u);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_unsigned_to_nat(2u);
x_10 = lean_nat_shiftl(x_7, x_9);
x_11 = lean_unsigned_to_nat(3u);
x_12 = lean_nat_div(x_10, x_11);
lean_dec(x_10);
x_13 = l_Nat_nextPowerOfTwo(x_12);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_mk_array(x_13, x_14);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_8);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_Compiler_LCNF_checkDeadLocalDecls_visitDecls(x_1, x_16);
x_18 = lean_ctor_get(x_17, 1);
lean_inc(x_18);
lean_dec(x_17);
x_19 = lean_st_ref_get(x_3, x_6);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 1);
lean_inc(x_21);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 lean_ctor_release(x_19, 1);
 x_22 = x_19;
} else {
 lean_dec_ref(x_19);
 x_22 = lean_box(0);
}
x_23 = lean_ctor_get(x_20, 0);
lean_inc(x_23);
lean_dec(x_20);
x_49 = lean_ctor_get(x_23, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_49, 1);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_array_get_size(x_50);
x_52 = lean_nat_dec_lt(x_8, x_51);
if (x_52 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
x_37 = x_21;
goto block_48;
}
else
{
uint8_t x_53; 
x_53 = lean_nat_dec_le(x_51, x_51);
if (x_53 == 0)
{
lean_dec(x_51);
lean_dec(x_50);
x_37 = x_21;
goto block_48;
}
else
{
lean_object* x_54; size_t x_55; size_t x_56; lean_object* x_57; 
x_54 = lean_box(0);
x_55 = lean_usize_of_nat(x_8);
x_56 = lean_usize_of_nat(x_51);
lean_dec(x_51);
lean_inc(x_18);
x_57 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__8(x_18, x_50, x_55, x_56, x_54, x_2, x_3, x_4, x_5, x_21);
lean_dec(x_50);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; 
x_58 = lean_ctor_get(x_57, 1);
lean_inc(x_58);
lean_dec(x_57);
x_37 = x_58;
goto block_48;
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
return x_57;
}
}
}
block_36:
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_25 = lean_ctor_get(x_23, 2);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_25, 1);
lean_inc(x_26);
lean_dec(x_25);
x_27 = lean_array_get_size(x_26);
x_28 = lean_box(0);
x_29 = lean_nat_dec_lt(x_8, x_27);
if (x_29 == 0)
{
lean_object* x_30; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_18);
if (lean_is_scalar(x_22)) {
 x_30 = lean_alloc_ctor(0, 2, 0);
} else {
 x_30 = x_22;
}
lean_ctor_set(x_30, 0, x_28);
lean_ctor_set(x_30, 1, x_24);
return x_30;
}
else
{
uint8_t x_31; 
x_31 = lean_nat_dec_le(x_27, x_27);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_27);
lean_dec(x_26);
lean_dec(x_18);
if (lean_is_scalar(x_22)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_22;
}
lean_ctor_set(x_32, 0, x_28);
lean_ctor_set(x_32, 1, x_24);
return x_32;
}
else
{
size_t x_33; size_t x_34; lean_object* x_35; 
lean_dec(x_22);
x_33 = lean_usize_of_nat(x_8);
x_34 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_35 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__6(x_18, x_26, x_33, x_34, x_28, x_2, x_3, x_4, x_5, x_24);
lean_dec(x_26);
return x_35;
}
}
}
block_48:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_38 = lean_ctor_get(x_23, 1);
lean_inc(x_38);
x_39 = lean_ctor_get(x_38, 1);
lean_inc(x_39);
lean_dec(x_38);
x_40 = lean_array_get_size(x_39);
x_41 = lean_nat_dec_lt(x_8, x_40);
if (x_41 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
x_24 = x_37;
goto block_36;
}
else
{
uint8_t x_42; 
x_42 = lean_nat_dec_le(x_40, x_40);
if (x_42 == 0)
{
lean_dec(x_40);
lean_dec(x_39);
x_24 = x_37;
goto block_36;
}
else
{
lean_object* x_43; size_t x_44; size_t x_45; lean_object* x_46; 
x_43 = lean_box(0);
x_44 = lean_usize_of_nat(x_8);
x_45 = lean_usize_of_nat(x_40);
lean_dec(x_40);
lean_inc(x_18);
x_46 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__7(x_18, x_39, x_44, x_45, x_43, x_2, x_3, x_4, x_5, x_37);
lean_dec(x_39);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 1);
lean_inc(x_47);
lean_dec(x_46);
x_24 = x_47;
goto block_36;
}
else
{
lean_dec(x_23);
lean_dec(x_22);
lean_dec(x_18);
return x_46;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Std_DHashMap_Internal_AssocList_foldlM___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__6(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__7(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_13 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_checkDeadLocalDecls_spec__8(x_1, x_2, x_11, x_12, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_checkDeadLocalDecls___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Compiler_LCNF_checkDeadLocalDecls(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_7;
}
}
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PrettyPrinter(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompatibleTypes(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_Check(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PrettyPrinter(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompatibleTypes(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
