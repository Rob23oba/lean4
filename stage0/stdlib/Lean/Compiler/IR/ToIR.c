// Lean compiler output
// Module: Lean.Compiler.IR.ToIR
// Imports: Lean.Compiler.LCNF.Basic Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.IR.Basic Lean.Compiler.IR.CompilerM Lean.Compiler.IR.CtorLayout Lean.CoreM Lean.Environment
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
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_const___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__8(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_find_env_decl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* l_Lean_Name_toString(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lit___override(lean_object*);
lean_object* l_Lean_Expr_sort___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_mdata___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_instMonadEIO___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_proj___override(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_bvar___override(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__6(uint8_t, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
lean_object* l_Lean_Environment_addExtraName(lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedFnBody;
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_getCtorInfo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instMonad(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object*, lean_object*);
uint64_t l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(lean_object*);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
lean_object* lean_nat_div(lean_object*, lean_object*);
lean_object* l_Array_empty(lean_object*);
lean_object* l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedCtorInfo;
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerType_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instMonadEIO(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_panic___at___Lean_Expr_appFn_x21_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_declMapExt;
lean_object* l_Lean_Expr_forallE___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_ReaderT_instApplicativeOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_instInhabitedOfMonad___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* l_Array_extract(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedIRType;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_letE___override(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_IR_instInhabitedArg;
uint8_t l_Lean_isExtern(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_bind(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
lean_object* l_instMonadEIO___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_get_ctor_layout(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_app___override(lean_object*, lean_object*);
lean_object* lean_nat_pow(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_ReaderT_instFunctorOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
lean_object* lean_panic_fn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_GetElem_0__List_get_x21Internal___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
lean_object* lean_array_mk(lean_object*);
lean_object* l_EStateM_seqRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Core_instMonadCoreM___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__2(lean_object*);
lean_object* l_Lean_Expr_headBeta(lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_ir_mk_dummy_extern_decl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_StateT_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_lam___override(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_lengthTR(lean_object*, lean_object*);
uint8_t l_Lean_Expr_isForall(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_land(size_t, size_t);
lean_object* l_StateT_pure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_instInhabitedTranslatedProj;
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_5 = lean_unsigned_to_nat(8u);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_unsigned_to_nat(2u);
x_8 = lean_nat_shiftl(x_5, x_7);
x_9 = lean_unsigned_to_nat(3u);
x_10 = lean_nat_div(x_8, x_9);
lean_dec(x_8);
x_11 = l_Nat_nextPowerOfTwo(x_10);
lean_dec(x_10);
x_12 = lean_box(0);
x_13 = lean_mk_array(x_11, x_12);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_6);
lean_ctor_set(x_14, 1, x_13);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
x_17 = lean_apply_4(x_1, x_16, x_2, x_3, x_4);
if (lean_obj_tag(x_17) == 0)
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
else
{
uint8_t x_25; 
x_25 = !lean_is_exclusive(x_17);
if (x_25 == 0)
{
return x_17;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_17, 0);
x_27 = lean_ctor_get(x_17, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_17);
x_28 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_28, 0, x_26);
lean_ctor_set(x_28, 1, x_27);
return x_28;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_M_run(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_M_run___redArg(x_2, x_3, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_15 = lean_array_get_size(x_6);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_31 = lean_array_uget(x_6, x_30);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_4, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_4, 0);
lean_dec(x_35);
lean_inc(x_7);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_7);
x_37 = lean_nat_add(x_5, x_27);
lean_dec(x_5);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_31);
x_39 = lean_array_uset(x_6, x_30, x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_shiftl(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_39);
lean_ctor_set(x_4, 1, x_46);
lean_ctor_set(x_4, 0, x_37);
x_8 = x_4;
goto block_14;
}
else
{
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_37);
x_8 = x_4;
goto block_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_4);
lean_inc(x_7);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_7);
x_48 = lean_nat_add(x_5, x_27);
lean_dec(x_5);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_31);
x_50 = lean_array_uset(x_6, x_30, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_8 = x_58;
goto block_14;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_50);
x_8 = x_59;
goto block_14;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = x_4;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindVar(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_5 = lean_ctor_get(x_3, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
x_8 = lean_box(0);
x_15 = lean_array_get_size(x_7);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_31 = lean_array_uget(x_7, x_30);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_5);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_5, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_5, 0);
lean_dec(x_35);
x_36 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_36, 0, x_2);
x_37 = lean_nat_add(x_6, x_27);
lean_dec(x_6);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_31);
x_39 = lean_array_uset(x_7, x_30, x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_shiftl(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_39);
lean_ctor_set(x_5, 1, x_46);
lean_ctor_set(x_5, 0, x_37);
x_9 = x_5;
goto block_14;
}
else
{
lean_ctor_set(x_5, 1, x_39);
lean_ctor_set(x_5, 0, x_37);
x_9 = x_5;
goto block_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_5);
x_47 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_47, 0, x_2);
x_48 = lean_nat_add(x_6, x_27);
lean_dec(x_6);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_31);
x_50 = lean_array_uset(x_7, x_30, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_9 = x_58;
goto block_14;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_50);
x_9 = x_59;
goto block_14;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_9 = x_5;
goto block_14;
}
block_14:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_10 = lean_ctor_get(x_3, 1);
lean_inc(x_10);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_9);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_1, x_2, x_3, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindVarToVarId___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_bindVarToVarId(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_ctor_get(x_1, 0);
x_5 = lean_unsigned_to_nat(1u);
x_6 = lean_nat_add(x_3, x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
lean_inc(x_3);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_7);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar___redArg(x_1, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_IR_ToIR_newVar___redArg(x_1, x_2);
lean_dec(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_newVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_newVar(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; lean_object* x_21; uint64_t x_22; uint64_t x_23; uint64_t x_24; size_t x_25; size_t x_26; lean_object* x_27; size_t x_28; size_t x_29; size_t x_30; lean_object* x_31; uint8_t x_32; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec(x_2);
x_15 = lean_array_get_size(x_6);
x_16 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_31 = lean_array_uget(x_6, x_30);
x_32 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_31);
if (x_32 == 0)
{
uint8_t x_33; 
x_33 = !lean_is_exclusive(x_4);
if (x_33 == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; 
x_34 = lean_ctor_get(x_4, 1);
lean_dec(x_34);
x_35 = lean_ctor_get(x_4, 0);
lean_dec(x_35);
lean_inc(x_7);
x_36 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_36, 0, x_7);
x_37 = lean_nat_add(x_5, x_27);
lean_dec(x_5);
x_38 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_38, 0, x_1);
lean_ctor_set(x_38, 1, x_36);
lean_ctor_set(x_38, 2, x_31);
x_39 = lean_array_uset(x_6, x_30, x_38);
x_40 = lean_unsigned_to_nat(2u);
x_41 = lean_nat_shiftl(x_37, x_40);
x_42 = lean_unsigned_to_nat(3u);
x_43 = lean_nat_div(x_41, x_42);
lean_dec(x_41);
x_44 = lean_array_get_size(x_39);
x_45 = lean_nat_dec_le(x_43, x_44);
lean_dec(x_44);
lean_dec(x_43);
if (x_45 == 0)
{
lean_object* x_46; 
x_46 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_39);
lean_ctor_set(x_4, 1, x_46);
lean_ctor_set(x_4, 0, x_37);
x_8 = x_4;
goto block_14;
}
else
{
lean_ctor_set(x_4, 1, x_39);
lean_ctor_set(x_4, 0, x_37);
x_8 = x_4;
goto block_14;
}
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
lean_dec(x_4);
lean_inc(x_7);
x_47 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_47, 0, x_7);
x_48 = lean_nat_add(x_5, x_27);
lean_dec(x_5);
x_49 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_49, 0, x_1);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_49, 2, x_31);
x_50 = lean_array_uset(x_6, x_30, x_49);
x_51 = lean_unsigned_to_nat(2u);
x_52 = lean_nat_shiftl(x_48, x_51);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_div(x_52, x_53);
lean_dec(x_52);
x_55 = lean_array_get_size(x_50);
x_56 = lean_nat_dec_le(x_54, x_55);
lean_dec(x_55);
lean_dec(x_54);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; 
x_57 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_50);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_48);
lean_ctor_set(x_58, 1, x_57);
x_8 = x_58;
goto block_14;
}
else
{
lean_object* x_59; 
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_48);
lean_ctor_set(x_59, 1, x_50);
x_8 = x_59;
goto block_14;
}
}
}
else
{
lean_dec(x_31);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = x_4;
goto block_14;
}
block_14:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_9 = lean_unsigned_to_nat(1u);
x_10 = lean_nat_add(x_7, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_7);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindJoinPoint___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindJoinPoint(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_14; uint64_t x_15; lean_object* x_16; uint64_t x_17; uint64_t x_18; uint64_t x_19; lean_object* x_20; uint64_t x_21; uint64_t x_22; uint64_t x_23; size_t x_24; size_t x_25; lean_object* x_26; size_t x_27; size_t x_28; size_t x_29; lean_object* x_30; uint8_t x_31; 
x_4 = lean_ctor_get(x_2, 0);
lean_inc(x_4);
x_5 = lean_ctor_get(x_4, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_4, 1);
lean_inc(x_6);
x_7 = lean_box(0);
x_14 = lean_array_get_size(x_6);
x_15 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_1);
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
x_30 = lean_array_uget(x_6, x_29);
x_31 = l_Std_DHashMap_Internal_AssocList_contains___at___Lean_Compiler_LCNF_LCtx_addParam_spec__0(lean_box(0), x_1, x_30);
if (x_31 == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_4);
if (x_32 == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_33 = lean_ctor_get(x_4, 1);
lean_dec(x_33);
x_34 = lean_ctor_get(x_4, 0);
lean_dec(x_34);
x_35 = lean_box(2);
x_36 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_37 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_37, 0, x_1);
lean_ctor_set(x_37, 1, x_35);
lean_ctor_set(x_37, 2, x_30);
x_38 = lean_array_uset(x_6, x_29, x_37);
x_39 = lean_unsigned_to_nat(2u);
x_40 = lean_nat_shiftl(x_36, x_39);
x_41 = lean_unsigned_to_nat(3u);
x_42 = lean_nat_div(x_40, x_41);
lean_dec(x_40);
x_43 = lean_array_get_size(x_38);
x_44 = lean_nat_dec_le(x_42, x_43);
lean_dec(x_43);
lean_dec(x_42);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_38);
lean_ctor_set(x_4, 1, x_45);
lean_ctor_set(x_4, 0, x_36);
x_8 = x_4;
goto block_13;
}
else
{
lean_ctor_set(x_4, 1, x_38);
lean_ctor_set(x_4, 0, x_36);
x_8 = x_4;
goto block_13;
}
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; uint8_t x_55; 
lean_dec(x_4);
x_46 = lean_box(2);
x_47 = lean_nat_add(x_5, x_26);
lean_dec(x_5);
x_48 = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(x_48, 0, x_1);
lean_ctor_set(x_48, 1, x_46);
lean_ctor_set(x_48, 2, x_30);
x_49 = lean_array_uset(x_6, x_29, x_48);
x_50 = lean_unsigned_to_nat(2u);
x_51 = lean_nat_shiftl(x_47, x_50);
x_52 = lean_unsigned_to_nat(3u);
x_53 = lean_nat_div(x_51, x_52);
lean_dec(x_51);
x_54 = lean_array_get_size(x_49);
x_55 = lean_nat_dec_le(x_53, x_54);
lean_dec(x_54);
lean_dec(x_53);
if (x_55 == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = l_Std_DHashMap_Internal_Raw_u2080_expand___at___Lean_Compiler_LCNF_LCtx_addParam_spec__1(lean_box(0), x_49);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_47);
lean_ctor_set(x_57, 1, x_56);
x_8 = x_57;
goto block_13;
}
else
{
lean_object* x_58; 
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_47);
lean_ctor_set(x_58, 1, x_49);
x_8 = x_58;
goto block_13;
}
}
}
else
{
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = x_4;
goto block_13;
}
block_13:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_9 = lean_ctor_get(x_2, 1);
lean_inc(x_9);
lean_dec(x_2);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_8);
lean_ctor_set(x_10, 1, x_9);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_7);
lean_ctor_set(x_11, 1, x_10);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_3);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased___redArg(x_1, x_2, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_bindErased___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_bindErased(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = lean_st_ref_get(x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_dec(x_7);
x_9 = lean_ir_find_env_decl(x_8, x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_2);
lean_ctor_set(x_5, 0, x_10);
return x_5;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_11 = lean_ctor_get(x_5, 0);
x_12 = lean_ctor_get(x_5, 1);
lean_inc(x_12);
lean_inc(x_11);
lean_dec(x_5);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
lean_dec(x_11);
x_14 = lean_ir_find_env_decl(x_13, x_1);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_2);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_15);
lean_ctor_set(x_16, 1, x_12);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_findDecl___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_findDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_findDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_34; 
x_5 = lean_st_ref_take(x_3, x_4);
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_5, 1);
lean_inc(x_7);
if (lean_is_exclusive(x_5)) {
 lean_ctor_release(x_5, 0);
 lean_ctor_release(x_5, 1);
 x_8 = x_5;
} else {
 lean_dec_ref(x_5);
 x_8 = lean_box(0);
}
x_9 = lean_ctor_get(x_6, 0);
lean_inc(x_9);
x_10 = l_Lean_IR_declMapExt;
x_34 = lean_ctor_get(x_1, 0);
lean_inc(x_34);
x_11 = x_34;
goto block_33;
block_33:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_12 = l_Lean_Environment_addExtraName(x_9, x_11);
x_13 = l_Lean_PersistentEnvExtension_addEntry(lean_box(0), lean_box(0), lean_box(0), x_10, x_12, x_1);
x_14 = lean_ctor_get(x_6, 1);
lean_inc(x_14);
x_15 = lean_ctor_get(x_6, 2);
lean_inc(x_15);
x_16 = lean_ctor_get(x_6, 3);
lean_inc(x_16);
x_17 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
x_18 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_18, 0, x_17);
lean_inc(x_18);
if (lean_is_scalar(x_8)) {
 x_19 = lean_alloc_ctor(0, 2, 0);
} else {
 x_19 = x_8;
}
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_ctor_get(x_6, 5);
lean_inc(x_20);
x_21 = lean_ctor_get(x_6, 6);
lean_inc(x_21);
x_22 = lean_ctor_get(x_6, 7);
lean_inc(x_22);
lean_dec(x_6);
x_23 = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(x_23, 0, x_13);
lean_ctor_set(x_23, 1, x_14);
lean_ctor_set(x_23, 2, x_15);
lean_ctor_set(x_23, 3, x_16);
lean_ctor_set(x_23, 4, x_19);
lean_ctor_set(x_23, 5, x_20);
lean_ctor_set(x_23, 6, x_21);
lean_ctor_set(x_23, 7, x_22);
x_24 = lean_st_ref_set(x_3, x_23, x_7);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_24, 0);
lean_dec(x_26);
x_27 = lean_box(0);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_24, 0, x_28);
return x_24;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_24, 1);
lean_inc(x_29);
lean_dec(x_24);
x_30 = lean_box(0);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_29);
return x_32;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_2, x_4, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_ToIR_addDecl___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_addDecl___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_addDecl(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLitValue(lean_object* x_1) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
uint8_t x_2; 
x_2 = !lean_is_exclusive(x_1);
if (x_2 == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
lean_dec(x_1);
x_4 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_4, 0, x_3);
return x_4;
}
}
else
{
uint8_t x_5; 
x_5 = !lean_is_exclusive(x_1);
if (x_5 == 0)
{
return x_1;
}
else
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__0), 2, 1);
lean_closure_set(x_6, 0, x_3);
x_7 = lean_apply_1(x_4, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__2(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_apply_1(x_1, x_4);
lean_ctor_set(x_2, 0, x_5);
x_6 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_6, 0, lean_box(0));
lean_closure_set(x_6, 1, x_2);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = lean_ctor_get(x_2, 0);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
lean_inc(x_7);
lean_dec(x_2);
x_9 = lean_apply_1(x_1, x_7);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_8);
x_11 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_11, 0, lean_box(0));
lean_closure_set(x_11, 1, x_10);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__3(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__2), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, x_6, x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__3), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__5(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; lean_object* x_5; 
x_4 = lean_ctor_get(x_2, 0);
lean_dec(x_4);
lean_ctor_set(x_2, 0, x_1);
x_5 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_5, 0, lean_box(0));
lean_closure_set(x_5, 1, x_2);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_ctor_get(x_2, 1);
lean_inc(x_6);
lean_dec(x_2);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_1);
lean_ctor_set(x_7, 1, x_6);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__0___boxed), 5, 2);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, x_7);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__6(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = lean_ctor_get(x_2, 0);
lean_inc(x_3);
x_4 = lean_ctor_get(x_2, 1);
lean_inc(x_4);
lean_dec(x_2);
x_5 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__5), 2, 1);
lean_closure_set(x_5, 0, x_3);
x_6 = lean_box(0);
x_7 = lean_apply_2(x_1, x_6, x_4);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__6), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__8(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_ctor_get(x_2, 1);
lean_inc(x_3);
lean_dec(x_2);
x_4 = lean_box(0);
x_5 = lean_apply_2(x_1, x_4, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__9(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__8), 2, 1);
lean_closure_set(x_6, 0, x_4);
x_7 = lean_apply_1(x_3, x_5);
x_8 = lean_alloc_closure((void*)(l_Lean_Core_instMonadCoreM___lam__1), 7, 4);
lean_closure_set(x_8, 0, lean_box(0));
lean_closure_set(x_8, 1, lean_box(0));
lean_closure_set(x_8, 2, x_7);
lean_closure_set(x_8, 3, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__1), 5, 0);
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__4), 5, 0);
x_8 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__7), 5, 0);
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__9), 5, 0);
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
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
lean_inc(x_29);
x_32 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set(x_33, 4, x_9);
x_34 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = lean_box(0);
x_37 = l_instInhabitedOfMonad___redArg(x_35, x_36);
x_38 = lean_panic_fn(x_37, x_1);
x_39 = lean_apply_4(x_38, x_2, x_3, x_4, x_5);
return x_39;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_8; lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_3);
lean_ctor_set(x_8, 1, x_4);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_3);
x_10 = !lean_is_exclusive(x_2);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_35; uint8_t x_36; lean_object* x_37; 
x_11 = lean_ctor_get(x_2, 0);
x_12 = lean_ctor_get(x_2, 1);
x_13 = lean_box(0);
x_14 = lean_box(0);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_14);
lean_ctor_set(x_2, 0, x_13);
x_35 = lean_box(0);
x_36 = lean_unbox(x_35);
lean_inc(x_1);
x_37 = l_Lean_Environment_find_x3f(x_1, x_11, x_36);
if (lean_obj_tag(x_37) == 0)
{
lean_inc(x_6);
lean_inc(x_5);
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_34;
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_37);
if (x_38 == 0)
{
lean_object* x_39; 
x_39 = lean_ctor_get(x_37, 0);
if (lean_obj_tag(x_39) == 6)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec(x_39);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
lean_dec(x_40);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Lean_Expr_isForall(x_42);
lean_dec(x_42);
if (x_43 == 0)
{
lean_free_object(x_37);
{
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_2);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_45 = lean_box(0);
lean_ctor_set(x_37, 0, x_45);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_37);
lean_ctor_set(x_46, 1, x_14);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_4);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_7);
return x_48;
}
}
else
{
lean_free_object(x_37);
lean_dec(x_39);
lean_inc(x_6);
lean_inc(x_5);
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_34;
}
}
else
{
lean_object* x_49; 
x_49 = lean_ctor_get(x_37, 0);
lean_inc(x_49);
lean_dec(x_37);
if (lean_obj_tag(x_49) == 6)
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_ctor_get(x_49, 0);
lean_inc(x_50);
lean_dec(x_49);
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
lean_dec(x_51);
x_53 = l_Lean_Expr_isForall(x_52);
lean_dec(x_52);
if (x_53 == 0)
{
{
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_2;
x_2 = _tmp_1;
x_3 = _tmp_2;
}
goto _start;
}
else
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; 
lean_dec(x_2);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_55 = lean_box(0);
x_56 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_56, 0, x_55);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_14);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_4);
x_59 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_59, 0, x_58);
lean_ctor_set(x_59, 1, x_7);
return x_59;
}
}
else
{
lean_dec(x_49);
lean_inc(x_6);
lean_inc(x_5);
x_15 = x_4;
x_16 = x_5;
x_17 = x_6;
x_18 = x_7;
goto block_34;
}
}
}
block_34:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_19 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_20 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerEnumToScalarType", 34, 34);
x_21 = lean_unsigned_to_nat(78u);
x_22 = lean_unsigned_to_nat(57u);
x_23 = lean_mk_string_unchecked("expected valid constructor name", 31, 31);
x_24 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_19, x_20, x_21, x_22, x_23);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
x_25 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0(x_24, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_25) == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 1);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
{
lean_object* _tmp_1 = x_12;
lean_object* _tmp_2 = x_2;
lean_object* _tmp_3 = x_28;
lean_object* _tmp_6 = x_27;
x_2 = _tmp_1;
x_3 = _tmp_2;
x_4 = _tmp_3;
x_7 = _tmp_6;
}
goto _start;
}
else
{
uint8_t x_30; 
lean_dec(x_2);
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
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
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_85; uint8_t x_86; lean_object* x_87; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = lean_ctor_get(x_2, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_2);
x_62 = lean_box(0);
x_63 = lean_box(0);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_62);
lean_ctor_set(x_64, 1, x_63);
x_85 = lean_box(0);
x_86 = lean_unbox(x_85);
lean_inc(x_1);
x_87 = l_Lean_Environment_find_x3f(x_1, x_60, x_86);
if (lean_obj_tag(x_87) == 0)
{
lean_inc(x_6);
lean_inc(x_5);
x_65 = x_4;
x_66 = x_5;
x_67 = x_6;
x_68 = x_7;
goto block_84;
}
else
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_87, 0);
lean_inc(x_88);
if (lean_is_exclusive(x_87)) {
 lean_ctor_release(x_87, 0);
 x_89 = x_87;
} else {
 lean_dec_ref(x_87);
 x_89 = lean_box(0);
}
if (lean_obj_tag(x_88) == 6)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_88, 0);
lean_inc(x_90);
lean_dec(x_88);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_ctor_get(x_91, 2);
lean_inc(x_92);
lean_dec(x_91);
x_93 = l_Lean_Expr_isForall(x_92);
lean_dec(x_92);
if (x_93 == 0)
{
lean_dec(x_89);
x_2 = x_61;
x_3 = x_64;
goto _start;
}
else
{
lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_95 = lean_box(0);
if (lean_is_scalar(x_89)) {
 x_96 = lean_alloc_ctor(1, 1, 0);
} else {
 x_96 = x_89;
}
lean_ctor_set(x_96, 0, x_95);
x_97 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_97, 0, x_96);
lean_ctor_set(x_97, 1, x_63);
x_98 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_4);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_7);
return x_99;
}
}
else
{
lean_dec(x_89);
lean_dec(x_88);
lean_inc(x_6);
lean_inc(x_5);
x_65 = x_4;
x_66 = x_5;
x_67 = x_6;
x_68 = x_7;
goto block_84;
}
}
block_84:
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_70 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerEnumToScalarType", 34, 34);
x_71 = lean_unsigned_to_nat(78u);
x_72 = lean_unsigned_to_nat(57u);
x_73 = lean_mk_string_unchecked("expected valid constructor name", 31, 31);
x_74 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_69, x_70, x_71, x_72, x_73);
lean_dec(x_73);
lean_dec(x_70);
lean_dec(x_69);
x_75 = l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0(x_74, x_65, x_66, x_67, x_68);
if (lean_obj_tag(x_75) == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_75, 0);
lean_inc(x_76);
x_77 = lean_ctor_get(x_75, 1);
lean_inc(x_77);
lean_dec(x_75);
x_78 = lean_ctor_get(x_76, 1);
lean_inc(x_78);
lean_dec(x_76);
x_2 = x_61;
x_3 = x_64;
x_4 = x_78;
x_7 = x_77;
goto _start;
}
else
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_64);
lean_dec(x_61);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
x_80 = lean_ctor_get(x_75, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_75, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_75)) {
 lean_ctor_release(x_75, 0);
 lean_ctor_release(x_75, 1);
 x_82 = x_75;
} else {
 lean_dec_ref(x_75);
 x_82 = lean_box(0);
}
if (lean_is_scalar(x_82)) {
 x_83 = lean_alloc_ctor(1, 2, 0);
} else {
 x_83 = x_82;
}
lean_ctor_set(x_83, 0, x_80);
lean_ctor_set(x_83, 1, x_81);
return x_83;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerEnumToScalarType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_15; lean_object* x_16; uint8_t x_17; lean_object* x_18; 
x_6 = lean_st_ref_get(x_4, x_5);
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
if (lean_is_exclusive(x_6)) {
 lean_ctor_release(x_6, 0);
 lean_ctor_release(x_6, 1);
 x_9 = x_6;
} else {
 lean_dec_ref(x_6);
 x_9 = lean_box(0);
}
x_15 = lean_ctor_get(x_7, 0);
lean_inc(x_15);
lean_dec(x_7);
x_16 = lean_box(0);
x_17 = lean_unbox(x_16);
lean_inc(x_15);
x_18 = l_Lean_Environment_find_x3f(x_15, x_1, x_17);
if (lean_obj_tag(x_18) == 0)
{
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_10 = x_2;
goto block_14;
}
else
{
uint8_t x_19; 
x_19 = !lean_is_exclusive(x_18);
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = lean_ctor_get(x_18, 0);
if (lean_obj_tag(x_20) == 5)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
lean_dec(x_9);
x_21 = lean_ctor_get(x_20, 0);
lean_inc(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 4);
lean_inc(x_22);
lean_dec(x_21);
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
lean_inc(x_22);
x_26 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(x_15, x_22, x_25, x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_37; 
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
x_30 = lean_ctor_get(x_27, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_31);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_32 = x_27;
} else {
 lean_dec_ref(x_27);
 x_32 = lean_box(0);
}
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
lean_dec(x_30);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_38 = l_List_lengthTR(lean_box(0), x_22);
lean_dec(x_22);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_nat_dec_eq(x_38, x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_41 = lean_unsigned_to_nat(2u);
x_42 = lean_unsigned_to_nat(8u);
x_43 = lean_nat_pow(x_41, x_42);
x_44 = lean_nat_dec_lt(x_38, x_43);
lean_dec(x_43);
if (x_44 == 0)
{
lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_45 = lean_unsigned_to_nat(16u);
x_46 = lean_nat_pow(x_41, x_45);
x_47 = lean_nat_dec_lt(x_38, x_46);
lean_dec(x_46);
if (x_47 == 0)
{
lean_object* x_48; lean_object* x_49; uint8_t x_50; 
x_48 = lean_unsigned_to_nat(32u);
x_49 = lean_nat_pow(x_41, x_48);
x_50 = lean_nat_dec_lt(x_38, x_49);
lean_dec(x_49);
lean_dec(x_38);
if (x_50 == 0)
{
lean_object* x_51; 
lean_free_object(x_18);
x_51 = lean_box(0);
x_33 = x_51;
goto block_36;
}
else
{
lean_object* x_52; 
x_52 = lean_box(3);
lean_ctor_set(x_18, 0, x_52);
x_33 = x_18;
goto block_36;
}
}
else
{
lean_object* x_53; 
lean_dec(x_38);
x_53 = lean_box(2);
lean_ctor_set(x_18, 0, x_53);
x_33 = x_18;
goto block_36;
}
}
else
{
lean_object* x_54; 
lean_dec(x_38);
x_54 = lean_box(1);
lean_ctor_set(x_18, 0, x_54);
x_33 = x_18;
goto block_36;
}
}
else
{
lean_object* x_55; 
lean_dec(x_38);
lean_free_object(x_18);
x_55 = lean_box(0);
x_33 = x_55;
goto block_36;
}
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
lean_dec(x_32);
lean_dec(x_29);
lean_dec(x_22);
lean_free_object(x_18);
x_56 = lean_ctor_get(x_37, 0);
lean_inc(x_56);
lean_dec(x_37);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_31);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_57);
lean_ctor_set(x_58, 1, x_28);
return x_58;
}
block_36:
{
lean_object* x_34; lean_object* x_35; 
if (lean_is_scalar(x_32)) {
 x_34 = lean_alloc_ctor(0, 2, 0);
} else {
 x_34 = x_32;
}
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_31);
if (lean_is_scalar(x_29)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_29;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_28);
return x_35;
}
}
else
{
uint8_t x_59; 
lean_dec(x_22);
lean_free_object(x_18);
x_59 = !lean_is_exclusive(x_26);
if (x_59 == 0)
{
return x_26;
}
else
{
lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_60 = lean_ctor_get(x_26, 0);
x_61 = lean_ctor_get(x_26, 1);
lean_inc(x_61);
lean_inc(x_60);
lean_dec(x_26);
x_62 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_62, 0, x_60);
lean_ctor_set(x_62, 1, x_61);
return x_62;
}
}
}
else
{
lean_free_object(x_18);
lean_dec(x_20);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_10 = x_2;
goto block_14;
}
}
else
{
lean_object* x_63; 
x_63 = lean_ctor_get(x_18, 0);
lean_inc(x_63);
lean_dec(x_18);
if (lean_obj_tag(x_63) == 5)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_9);
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
lean_dec(x_63);
x_65 = lean_ctor_get(x_64, 4);
lean_inc(x_65);
lean_dec(x_64);
x_66 = lean_box(0);
x_67 = lean_box(0);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_66);
lean_ctor_set(x_68, 1, x_67);
lean_inc(x_65);
x_69 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___redArg(x_15, x_65, x_68, x_2, x_3, x_4, x_8);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_80; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
x_71 = lean_ctor_get(x_69, 1);
lean_inc(x_71);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_72 = x_69;
} else {
 lean_dec_ref(x_69);
 x_72 = lean_box(0);
}
x_73 = lean_ctor_get(x_70, 0);
lean_inc(x_73);
x_74 = lean_ctor_get(x_70, 1);
lean_inc(x_74);
if (lean_is_exclusive(x_70)) {
 lean_ctor_release(x_70, 0);
 lean_ctor_release(x_70, 1);
 x_75 = x_70;
} else {
 lean_dec_ref(x_70);
 x_75 = lean_box(0);
}
x_80 = lean_ctor_get(x_73, 0);
lean_inc(x_80);
lean_dec(x_73);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; uint8_t x_83; 
x_81 = l_List_lengthTR(lean_box(0), x_65);
lean_dec(x_65);
x_82 = lean_unsigned_to_nat(1u);
x_83 = lean_nat_dec_eq(x_81, x_82);
if (x_83 == 0)
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; uint8_t x_87; 
x_84 = lean_unsigned_to_nat(2u);
x_85 = lean_unsigned_to_nat(8u);
x_86 = lean_nat_pow(x_84, x_85);
x_87 = lean_nat_dec_lt(x_81, x_86);
lean_dec(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_88 = lean_unsigned_to_nat(16u);
x_89 = lean_nat_pow(x_84, x_88);
x_90 = lean_nat_dec_lt(x_81, x_89);
lean_dec(x_89);
if (x_90 == 0)
{
lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_91 = lean_unsigned_to_nat(32u);
x_92 = lean_nat_pow(x_84, x_91);
x_93 = lean_nat_dec_lt(x_81, x_92);
lean_dec(x_92);
lean_dec(x_81);
if (x_93 == 0)
{
lean_object* x_94; 
x_94 = lean_box(0);
x_76 = x_94;
goto block_79;
}
else
{
lean_object* x_95; lean_object* x_96; 
x_95 = lean_box(3);
x_96 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_96, 0, x_95);
x_76 = x_96;
goto block_79;
}
}
else
{
lean_object* x_97; lean_object* x_98; 
lean_dec(x_81);
x_97 = lean_box(2);
x_98 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_98, 0, x_97);
x_76 = x_98;
goto block_79;
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_81);
x_99 = lean_box(1);
x_100 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_100, 0, x_99);
x_76 = x_100;
goto block_79;
}
}
else
{
lean_object* x_101; 
lean_dec(x_81);
x_101 = lean_box(0);
x_76 = x_101;
goto block_79;
}
}
else
{
lean_object* x_102; lean_object* x_103; lean_object* x_104; 
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_65);
x_102 = lean_ctor_get(x_80, 0);
lean_inc(x_102);
lean_dec(x_80);
x_103 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_74);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_71);
return x_104;
}
block_79:
{
lean_object* x_77; lean_object* x_78; 
if (lean_is_scalar(x_75)) {
 x_77 = lean_alloc_ctor(0, 2, 0);
} else {
 x_77 = x_75;
}
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_74);
if (lean_is_scalar(x_72)) {
 x_78 = lean_alloc_ctor(0, 2, 0);
} else {
 x_78 = x_72;
}
lean_ctor_set(x_78, 0, x_77);
lean_ctor_set(x_78, 1, x_71);
return x_78;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_65);
x_105 = lean_ctor_get(x_69, 0);
lean_inc(x_105);
x_106 = lean_ctor_get(x_69, 1);
lean_inc(x_106);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_107 = x_69;
} else {
 lean_dec_ref(x_69);
 x_107 = lean_box(0);
}
if (lean_is_scalar(x_107)) {
 x_108 = lean_alloc_ctor(1, 2, 0);
} else {
 x_108 = x_107;
}
lean_ctor_set(x_108, 0, x_105);
lean_ctor_set(x_108, 1, x_106);
return x_108;
}
}
else
{
lean_dec(x_63);
lean_dec(x_15);
lean_dec(x_4);
lean_dec(x_3);
x_10 = x_2;
goto block_14;
}
}
}
block_14:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
if (lean_is_scalar(x_9)) {
 x_13 = lean_alloc_ctor(0, 2, 0);
} else {
 x_13 = x_9;
}
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_8);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerType_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__1), 5, 0);
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__4), 5, 0);
x_8 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__7), 5, 0);
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__9), 5, 0);
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
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
lean_inc(x_29);
x_32 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set(x_33, 4, x_9);
x_34 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_IR_instInhabitedIRType;
x_37 = l_instInhabitedOfMonad___redArg(x_35, x_36);
x_38 = lean_panic_fn(x_37, x_1);
x_39 = lean_apply_4(x_38, x_2, x_3, x_4, x_5);
return x_39;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_1, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_8, 0);
lean_inc(x_9);
if (lean_obj_tag(x_9) == 0)
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_7, 0);
lean_dec(x_11);
x_12 = !lean_is_exclusive(x_8);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; 
x_13 = lean_ctor_get(x_8, 0);
lean_dec(x_13);
x_14 = lean_box(7);
lean_ctor_set(x_8, 0, x_14);
return x_7;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_15 = lean_ctor_get(x_8, 1);
lean_inc(x_15);
lean_dec(x_8);
x_16 = lean_box(7);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_15);
lean_ctor_set(x_7, 0, x_17);
return x_7;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_18 = lean_ctor_get(x_7, 1);
lean_inc(x_18);
lean_dec(x_7);
x_19 = lean_ctor_get(x_8, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_20 = x_8;
} else {
 lean_dec_ref(x_8);
 x_20 = lean_box(0);
}
x_21 = lean_box(7);
if (lean_is_scalar(x_20)) {
 x_22 = lean_alloc_ctor(0, 2, 0);
} else {
 x_22 = x_20;
}
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_19);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8_t x_24; 
x_24 = !lean_is_exclusive(x_7);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_ctor_get(x_7, 0);
lean_dec(x_25);
x_26 = !lean_is_exclusive(x_8);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; 
x_27 = lean_ctor_get(x_8, 0);
lean_dec(x_27);
x_28 = lean_ctor_get(x_9, 0);
lean_inc(x_28);
lean_dec(x_9);
lean_ctor_set(x_8, 0, x_28);
return x_7;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_ctor_get(x_8, 1);
lean_inc(x_29);
lean_dec(x_8);
x_30 = lean_ctor_get(x_9, 0);
lean_inc(x_30);
lean_dec(x_9);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
lean_ctor_set(x_7, 0, x_31);
return x_7;
}
}
else
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_7, 1);
lean_inc(x_32);
lean_dec(x_7);
x_33 = lean_ctor_get(x_8, 1);
lean_inc(x_33);
if (lean_is_exclusive(x_8)) {
 lean_ctor_release(x_8, 0);
 lean_ctor_release(x_8, 1);
 x_34 = x_8;
} else {
 lean_dec_ref(x_8);
 x_34 = lean_box(0);
}
x_35 = lean_ctor_get(x_9, 0);
lean_inc(x_35);
lean_dec(x_9);
if (lean_is_scalar(x_34)) {
 x_36 = lean_alloc_ctor(0, 2, 0);
} else {
 x_36 = x_34;
}
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_33);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_32);
return x_37;
}
}
}
else
{
uint8_t x_38; 
x_38 = !lean_is_exclusive(x_7);
if (x_38 == 0)
{
return x_7;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_7, 0);
x_40 = lean_ctor_get(x_7, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_7);
x_41 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_41, 0, x_39);
lean_ctor_set(x_41, 1, x_40);
return x_41;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(1);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_box(7);
x_7 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_7, 0, x_6);
lean_ctor_set(x_7, 1, x_2);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_5);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_6) == 1)
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_6, 0);
lean_inc(x_7);
switch (lean_obj_tag(x_7)) {
case 0:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_6, 1);
lean_inc(x_8);
x_9 = lean_mk_string_unchecked("UInt8", 5, 5);
x_10 = lean_string_dec_eq(x_8, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_mk_string_unchecked("Bool", 4, 4);
x_12 = lean_string_dec_eq(x_8, x_11);
lean_dec(x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_mk_string_unchecked("UInt16", 6, 6);
x_14 = lean_string_dec_eq(x_8, x_13);
lean_dec(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_mk_string_unchecked("UInt32", 6, 6);
x_16 = lean_string_dec_eq(x_8, x_15);
lean_dec(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_mk_string_unchecked("UInt64", 6, 6);
x_18 = lean_string_dec_eq(x_8, x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_mk_string_unchecked("USize", 5, 5);
x_20 = lean_string_dec_eq(x_8, x_19);
lean_dec(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_mk_string_unchecked("Float", 5, 5);
x_22 = lean_string_dec_eq(x_8, x_21);
lean_dec(x_21);
if (x_22 == 0)
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_mk_string_unchecked("Float32", 7, 7);
x_24 = lean_string_dec_eq(x_8, x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = lean_mk_string_unchecked("lcErased", 8, 8);
x_26 = lean_string_dec_eq(x_8, x_25);
lean_dec(x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_27 = lean_box(0);
x_28 = l_Lean_Name_str___override(x_27, x_8);
x_29 = l_Lean_IR_ToIR_lowerType___lam__0(x_6, x_28, x_2, x_3, x_4, x_5);
lean_dec(x_28);
return x_29;
}
else
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_30 = lean_box(6);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_2);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_5);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_33 = lean_box(9);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_2);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_5);
return x_35;
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set(x_37, 1, x_2);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_37);
lean_ctor_set(x_38, 1, x_5);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_39 = lean_box(5);
x_40 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_2);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_5);
return x_41;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_42 = lean_box(4);
x_43 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_43, 0, x_42);
lean_ctor_set(x_43, 1, x_2);
x_44 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_44, 0, x_43);
lean_ctor_set(x_44, 1, x_5);
return x_44;
}
}
else
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_45 = lean_box(3);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_46);
lean_ctor_set(x_47, 1, x_5);
return x_47;
}
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_8);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
x_48 = lean_box(2);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_5);
return x_50;
}
}
else
{
lean_object* x_51; lean_object* x_52; 
lean_dec(x_8);
lean_dec(x_6);
x_51 = lean_box(0);
x_52 = l_Lean_IR_ToIR_lowerType___lam__1(x_51, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_52;
}
}
else
{
lean_object* x_53; lean_object* x_54; 
lean_dec(x_8);
lean_dec(x_6);
x_53 = lean_box(0);
x_54 = l_Lean_IR_ToIR_lowerType___lam__1(x_53, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_54;
}
}
case 1:
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; 
x_55 = lean_ctor_get(x_6, 1);
lean_inc(x_55);
x_56 = lean_ctor_get(x_7, 0);
lean_inc(x_56);
x_57 = lean_ctor_get(x_7, 1);
lean_inc(x_57);
lean_dec(x_7);
x_58 = l_Lean_Name_str___override(x_56, x_57);
x_59 = l_Lean_Name_str___override(x_58, x_55);
x_60 = l_Lean_IR_ToIR_lowerType___lam__0(x_6, x_59, x_2, x_3, x_4, x_5);
lean_dec(x_59);
return x_60;
}
default: 
{
lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_61 = lean_ctor_get(x_6, 1);
lean_inc(x_61);
x_62 = lean_ctor_get(x_7, 0);
lean_inc(x_62);
x_63 = lean_ctor_get(x_7, 1);
lean_inc(x_63);
lean_dec(x_7);
x_64 = l_Lean_Name_num___override(x_62, x_63);
x_65 = l_Lean_Name_str___override(x_64, x_61);
x_66 = l_Lean_IR_ToIR_lowerType___lam__0(x_6, x_65, x_2, x_3, x_4, x_5);
lean_dec(x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; 
lean_inc(x_6);
x_67 = l_Lean_IR_ToIR_lowerType___lam__0(x_6, x_6, x_2, x_3, x_4, x_5);
lean_dec(x_6);
return x_67;
}
}
case 5:
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_1, 0);
lean_inc(x_68);
lean_dec(x_1);
x_69 = l_Lean_Expr_headBeta(x_68);
switch (lean_obj_tag(x_69)) {
case 0:
{
lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
x_71 = l_Lean_Expr_bvar___override(x_70);
x_72 = l_Lean_IR_ToIR_lowerType___lam__2(x_71, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_71);
return x_72;
}
case 1:
{
lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_73 = lean_ctor_get(x_69, 0);
lean_inc(x_73);
lean_dec(x_69);
x_74 = l_Lean_Expr_fvar___override(x_73);
x_75 = l_Lean_IR_ToIR_lowerType___lam__2(x_74, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_74);
return x_75;
}
case 2:
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_69, 0);
lean_inc(x_76);
lean_dec(x_69);
x_77 = l_Lean_Expr_mvar___override(x_76);
x_78 = l_Lean_IR_ToIR_lowerType___lam__2(x_77, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_77);
return x_78;
}
case 3:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; 
x_79 = lean_ctor_get(x_69, 0);
lean_inc(x_79);
lean_dec(x_69);
x_80 = l_Lean_Expr_sort___override(x_79);
x_81 = l_Lean_IR_ToIR_lowerType___lam__2(x_80, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_80);
return x_81;
}
case 4:
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_69, 0);
lean_inc(x_82);
lean_dec(x_69);
x_83 = l_Lean_IR_ToIR_lowerEnumToScalarType(x_82, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_83) == 0)
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_83, 0);
lean_inc(x_84);
x_85 = lean_ctor_get(x_84, 0);
lean_inc(x_85);
if (lean_obj_tag(x_85) == 0)
{
uint8_t x_86; 
x_86 = !lean_is_exclusive(x_83);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_83, 0);
lean_dec(x_87);
x_88 = !lean_is_exclusive(x_84);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_84, 0);
lean_dec(x_89);
x_90 = lean_box(7);
lean_ctor_set(x_84, 0, x_90);
return x_83;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_84, 1);
lean_inc(x_91);
lean_dec(x_84);
x_92 = lean_box(7);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_83, 0, x_93);
return x_83;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_94 = lean_ctor_get(x_83, 1);
lean_inc(x_94);
lean_dec(x_83);
x_95 = lean_ctor_get(x_84, 1);
lean_inc(x_95);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_96 = x_84;
} else {
 lean_dec_ref(x_84);
 x_96 = lean_box(0);
}
x_97 = lean_box(7);
if (lean_is_scalar(x_96)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_96;
}
lean_ctor_set(x_98, 0, x_97);
lean_ctor_set(x_98, 1, x_95);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_94);
return x_99;
}
}
else
{
uint8_t x_100; 
x_100 = !lean_is_exclusive(x_83);
if (x_100 == 0)
{
lean_object* x_101; uint8_t x_102; 
x_101 = lean_ctor_get(x_83, 0);
lean_dec(x_101);
x_102 = !lean_is_exclusive(x_84);
if (x_102 == 0)
{
lean_object* x_103; lean_object* x_104; 
x_103 = lean_ctor_get(x_84, 0);
lean_dec(x_103);
x_104 = lean_ctor_get(x_85, 0);
lean_inc(x_104);
lean_dec(x_85);
lean_ctor_set(x_84, 0, x_104);
return x_83;
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; 
x_105 = lean_ctor_get(x_84, 1);
lean_inc(x_105);
lean_dec(x_84);
x_106 = lean_ctor_get(x_85, 0);
lean_inc(x_106);
lean_dec(x_85);
x_107 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_105);
lean_ctor_set(x_83, 0, x_107);
return x_83;
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_108 = lean_ctor_get(x_83, 1);
lean_inc(x_108);
lean_dec(x_83);
x_109 = lean_ctor_get(x_84, 1);
lean_inc(x_109);
if (lean_is_exclusive(x_84)) {
 lean_ctor_release(x_84, 0);
 lean_ctor_release(x_84, 1);
 x_110 = x_84;
} else {
 lean_dec_ref(x_84);
 x_110 = lean_box(0);
}
x_111 = lean_ctor_get(x_85, 0);
lean_inc(x_111);
lean_dec(x_85);
if (lean_is_scalar(x_110)) {
 x_112 = lean_alloc_ctor(0, 2, 0);
} else {
 x_112 = x_110;
}
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_109);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_112);
lean_ctor_set(x_113, 1, x_108);
return x_113;
}
}
}
else
{
uint8_t x_114; 
x_114 = !lean_is_exclusive(x_83);
if (x_114 == 0)
{
return x_83;
}
else
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; 
x_115 = lean_ctor_get(x_83, 0);
x_116 = lean_ctor_get(x_83, 1);
lean_inc(x_116);
lean_inc(x_115);
lean_dec(x_83);
x_117 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
return x_117;
}
}
}
case 5:
{
lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
x_118 = lean_ctor_get(x_69, 0);
lean_inc(x_118);
x_119 = lean_ctor_get(x_69, 1);
lean_inc(x_119);
lean_dec(x_69);
x_120 = l_Lean_Expr_app___override(x_118, x_119);
x_121 = l_Lean_IR_ToIR_lowerType___lam__2(x_120, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_120);
return x_121;
}
case 6:
{
lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; lean_object* x_126; lean_object* x_127; 
x_122 = lean_ctor_get(x_69, 0);
lean_inc(x_122);
x_123 = lean_ctor_get(x_69, 1);
lean_inc(x_123);
x_124 = lean_ctor_get(x_69, 2);
lean_inc(x_124);
x_125 = lean_ctor_get_uint8(x_69, sizeof(void*)*3 + 8);
lean_dec(x_69);
x_126 = l_Lean_Expr_lam___override(x_122, x_123, x_124, x_125);
x_127 = l_Lean_IR_ToIR_lowerType___lam__2(x_126, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_126);
return x_127;
}
case 7:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; uint8_t x_131; lean_object* x_132; lean_object* x_133; 
x_128 = lean_ctor_get(x_69, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_69, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_69, 2);
lean_inc(x_130);
x_131 = lean_ctor_get_uint8(x_69, sizeof(void*)*3 + 8);
lean_dec(x_69);
x_132 = l_Lean_Expr_forallE___override(x_128, x_129, x_130, x_131);
x_133 = l_Lean_IR_ToIR_lowerType___lam__2(x_132, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_132);
return x_133;
}
case 8:
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; uint8_t x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_69, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_69, 1);
lean_inc(x_135);
x_136 = lean_ctor_get(x_69, 2);
lean_inc(x_136);
x_137 = lean_ctor_get(x_69, 3);
lean_inc(x_137);
x_138 = lean_ctor_get_uint8(x_69, sizeof(void*)*4 + 8);
lean_dec(x_69);
x_139 = l_Lean_Expr_letE___override(x_134, x_135, x_136, x_137, x_138);
x_140 = l_Lean_IR_ToIR_lowerType___lam__2(x_139, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_139);
return x_140;
}
case 9:
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_141 = lean_ctor_get(x_69, 0);
lean_inc(x_141);
lean_dec(x_69);
x_142 = l_Lean_Expr_lit___override(x_141);
x_143 = l_Lean_IR_ToIR_lowerType___lam__2(x_142, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_142);
return x_143;
}
case 10:
{
lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; 
x_144 = lean_ctor_get(x_69, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_69, 1);
lean_inc(x_145);
lean_dec(x_69);
x_146 = l_Lean_Expr_mdata___override(x_144, x_145);
x_147 = l_Lean_IR_ToIR_lowerType___lam__2(x_146, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_146);
return x_147;
}
default: 
{
lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_148 = lean_ctor_get(x_69, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_69, 1);
lean_inc(x_149);
x_150 = lean_ctor_get(x_69, 2);
lean_inc(x_150);
lean_dec(x_69);
x_151 = l_Lean_Expr_proj___override(x_148, x_149, x_150);
x_152 = l_Lean_IR_ToIR_lowerType___lam__2(x_151, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_151);
return x_152;
}
}
}
case 7:
{
lean_object* x_153; lean_object* x_154; lean_object* x_155; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_153 = lean_box(7);
x_154 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_154, 0, x_153);
lean_ctor_set(x_154, 1, x_2);
x_155 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_155, 0, x_154);
lean_ctor_set(x_155, 1, x_5);
return x_155;
}
default: 
{
lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; 
lean_dec(x_1);
x_156 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_157 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerType", 22, 22);
x_158 = lean_unsigned_to_nat(117u);
x_159 = lean_unsigned_to_nat(9u);
x_160 = lean_mk_string_unchecked("invalid type", 12, 12);
x_161 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_156, x_157, x_158, x_159, x_160);
lean_dec(x_160);
lean_dec(x_157);
lean_dec(x_156);
x_162 = l_panic___at___Lean_IR_ToIR_lowerType_spec__0(x_161, x_2, x_3, x_4, x_5);
return x_162;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_IR_ToIR_lowerType___lam__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerType___lam__1(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerType___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerType___lam__2(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_getCtorInfo_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__1), 5, 0);
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__4), 5, 0);
x_8 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__7), 5, 0);
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__9), 5, 0);
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
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
lean_inc(x_29);
x_32 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set(x_33, 4, x_9);
x_34 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_IR_instInhabitedCtorInfo;
x_37 = l_Array_instInhabited(lean_box(0));
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_36);
lean_ctor_set(x_38, 1, x_37);
x_39 = l_instInhabitedOfMonad___redArg(x_35, x_38);
x_40 = lean_panic_fn(x_39, x_1);
x_41 = lean_apply_4(x_40, x_2, x_3, x_4, x_5);
return x_41;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_getCtorInfo(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
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
x_11 = lean_ir_get_ctor_layout(x_10, x_1);
lean_dec(x_10);
if (lean_obj_tag(x_11) == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_11);
lean_free_object(x_6);
lean_dec(x_1);
x_12 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_13 = lean_mk_string_unchecked("Lean.IR.ToIR.getCtorInfo", 24, 24);
x_14 = lean_unsigned_to_nat(130u);
x_15 = lean_unsigned_to_nat(17u);
x_16 = lean_mk_string_unchecked("unrecognized constructor", 24, 24);
x_17 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_12, x_13, x_14, x_15, x_16);
lean_dec(x_16);
lean_dec(x_13);
lean_dec(x_12);
x_18 = l_panic___at___Lean_IR_ToIR_getCtorInfo_spec__0(x_17, x_2, x_3, x_4, x_9);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_4);
lean_dec(x_3);
x_19 = lean_ctor_get(x_11, 0);
lean_inc(x_19);
lean_dec(x_11);
x_20 = lean_ctor_get(x_19, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_19, 2);
lean_inc(x_21);
x_22 = lean_ctor_get(x_19, 3);
lean_inc(x_22);
x_23 = lean_ctor_get(x_19, 4);
lean_inc(x_23);
x_24 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_20);
lean_ctor_set(x_24, 2, x_21);
lean_ctor_set(x_24, 3, x_22);
lean_ctor_set(x_24, 4, x_23);
x_25 = lean_ctor_get(x_19, 1);
lean_inc(x_25);
lean_dec(x_19);
x_26 = lean_array_mk(x_25);
x_27 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_2);
lean_ctor_set(x_6, 0, x_28);
return x_6;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_6, 0);
x_30 = lean_ctor_get(x_6, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_6);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ir_get_ctor_layout(x_31, x_1);
lean_dec(x_31);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
lean_dec(x_32);
lean_dec(x_1);
x_33 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_34 = lean_mk_string_unchecked("Lean.IR.ToIR.getCtorInfo", 24, 24);
x_35 = lean_unsigned_to_nat(130u);
x_36 = lean_unsigned_to_nat(17u);
x_37 = lean_mk_string_unchecked("unrecognized constructor", 24, 24);
x_38 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_33, x_34, x_35, x_36, x_37);
lean_dec(x_37);
lean_dec(x_34);
lean_dec(x_33);
x_39 = l_panic___at___Lean_IR_ToIR_getCtorInfo_spec__0(x_38, x_2, x_3, x_4, x_30);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
lean_dec(x_3);
x_40 = lean_ctor_get(x_32, 0);
lean_inc(x_40);
lean_dec(x_32);
x_41 = lean_ctor_get(x_40, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_40, 2);
lean_inc(x_42);
x_43 = lean_ctor_get(x_40, 3);
lean_inc(x_43);
x_44 = lean_ctor_get(x_40, 4);
lean_inc(x_44);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_1);
lean_ctor_set(x_45, 1, x_41);
lean_ctor_set(x_45, 2, x_42);
lean_ctor_set(x_45, 3, x_43);
lean_ctor_set(x_45, 4, x_44);
x_46 = lean_ctor_get(x_40, 1);
lean_inc(x_46);
lean_dec(x_40);
x_47 = lean_array_mk(x_46);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_45);
lean_ctor_set(x_48, 1, x_47);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_2);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_30);
return x_50;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__1), 5, 0);
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__4), 5, 0);
x_8 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__7), 5, 0);
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__9), 5, 0);
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
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
lean_inc(x_29);
x_32 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set(x_33, 4, x_9);
x_34 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_IR_instInhabitedArg;
x_37 = l_instInhabitedOfMonad___redArg(x_35, x_36);
x_38 = lean_panic_fn(x_37, x_1);
x_39 = lean_apply_4(x_38, x_2, x_3, x_4, x_5);
return x_39;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = !lean_is_exclusive(x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint64_t x_12; lean_object* x_13; uint64_t x_14; uint64_t x_15; uint64_t x_16; lean_object* x_17; uint64_t x_18; uint64_t x_19; uint64_t x_20; size_t x_21; size_t x_22; lean_object* x_23; size_t x_24; size_t x_25; size_t x_26; lean_object* x_27; lean_object* x_28; 
x_8 = lean_ctor_get(x_1, 0);
x_9 = lean_ctor_get(x_6, 1);
x_10 = lean_ctor_get(x_6, 0);
lean_dec(x_10);
x_11 = lean_array_get_size(x_9);
x_12 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_8);
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
x_27 = lean_array_uget(x_9, x_26);
lean_dec(x_9);
x_28 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_8, x_27);
lean_dec(x_27);
if (lean_obj_tag(x_28) == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
lean_free_object(x_6);
x_29 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_30 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerArg", 21, 21);
x_31 = lean_unsigned_to_nat(138u);
x_32 = lean_unsigned_to_nat(37u);
x_33 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_34 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_29, x_30, x_31, x_32, x_33);
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_29);
x_35 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_34, x_2, x_3, x_4, x_5);
return x_35;
}
else
{
lean_object* x_36; 
x_36 = lean_ctor_get(x_28, 0);
lean_inc(x_36);
lean_dec(x_28);
switch (lean_obj_tag(x_36)) {
case 0:
{
uint8_t x_37; 
lean_dec(x_4);
lean_dec(x_3);
x_37 = !lean_is_exclusive(x_36);
if (x_37 == 0)
{
lean_object* x_38; 
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_6);
lean_ctor_set(x_38, 1, x_5);
return x_38;
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_36, 0);
lean_inc(x_39);
lean_dec(x_36);
x_40 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_40);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_6);
lean_ctor_set(x_41, 1, x_5);
return x_41;
}
}
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
lean_dec(x_36);
lean_free_object(x_6);
x_42 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_43 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerArg", 21, 21);
x_44 = lean_unsigned_to_nat(138u);
x_45 = lean_unsigned_to_nat(37u);
x_46 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_47 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_42, x_43, x_44, x_45, x_46);
lean_dec(x_46);
lean_dec(x_43);
lean_dec(x_42);
x_48 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_47, x_2, x_3, x_4, x_5);
return x_48;
}
default: 
{
lean_object* x_49; lean_object* x_50; 
lean_dec(x_4);
lean_dec(x_3);
x_49 = lean_box(1);
lean_ctor_set(x_6, 1, x_2);
lean_ctor_set(x_6, 0, x_49);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_6);
lean_ctor_set(x_50, 1, x_5);
return x_50;
}
}
}
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint64_t x_54; lean_object* x_55; uint64_t x_56; uint64_t x_57; uint64_t x_58; lean_object* x_59; uint64_t x_60; uint64_t x_61; uint64_t x_62; size_t x_63; size_t x_64; lean_object* x_65; size_t x_66; size_t x_67; size_t x_68; lean_object* x_69; lean_object* x_70; 
x_51 = lean_ctor_get(x_1, 0);
x_52 = lean_ctor_get(x_6, 1);
lean_inc(x_52);
lean_dec(x_6);
x_53 = lean_array_get_size(x_52);
x_54 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_51);
x_55 = lean_unsigned_to_nat(32u);
x_56 = lean_uint64_of_nat(x_55);
x_57 = lean_uint64_shift_right(x_54, x_56);
x_58 = lean_uint64_xor(x_54, x_57);
x_59 = lean_unsigned_to_nat(16u);
x_60 = lean_uint64_of_nat(x_59);
x_61 = lean_uint64_shift_right(x_58, x_60);
x_62 = lean_uint64_xor(x_58, x_61);
x_63 = lean_uint64_to_usize(x_62);
x_64 = lean_usize_of_nat(x_53);
lean_dec(x_53);
x_65 = lean_unsigned_to_nat(1u);
x_66 = lean_usize_of_nat(x_65);
x_67 = lean_usize_sub(x_64, x_66);
x_68 = lean_usize_land(x_63, x_67);
x_69 = lean_array_uget(x_52, x_68);
lean_dec(x_52);
x_70 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_51, x_69);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_71 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_72 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerArg", 21, 21);
x_73 = lean_unsigned_to_nat(138u);
x_74 = lean_unsigned_to_nat(37u);
x_75 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_76 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_71, x_72, x_73, x_74, x_75);
lean_dec(x_75);
lean_dec(x_72);
lean_dec(x_71);
x_77 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_76, x_2, x_3, x_4, x_5);
return x_77;
}
else
{
lean_object* x_78; 
x_78 = lean_ctor_get(x_70, 0);
lean_inc(x_78);
lean_dec(x_70);
switch (lean_obj_tag(x_78)) {
case 0:
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_4);
lean_dec(x_3);
x_79 = lean_ctor_get(x_78, 0);
lean_inc(x_79);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 x_80 = x_78;
} else {
 lean_dec_ref(x_78);
 x_80 = lean_box(0);
}
if (lean_is_scalar(x_80)) {
 x_81 = lean_alloc_ctor(0, 1, 0);
} else {
 x_81 = x_80;
}
lean_ctor_set(x_81, 0, x_79);
x_82 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_2);
x_83 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_83, 0, x_82);
lean_ctor_set(x_83, 1, x_5);
return x_83;
}
case 1:
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
lean_dec(x_78);
x_84 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_85 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerArg", 21, 21);
x_86 = lean_unsigned_to_nat(138u);
x_87 = lean_unsigned_to_nat(37u);
x_88 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_89 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_84, x_85, x_86, x_87, x_88);
lean_dec(x_88);
lean_dec(x_85);
lean_dec(x_84);
x_90 = l_panic___at___Lean_IR_ToIR_lowerArg_spec__0(x_89, x_2, x_3, x_4, x_5);
return x_90;
}
default: 
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_4);
lean_dec(x_3);
x_91 = lean_box(1);
x_92 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_92, 0, x_91);
lean_ctor_set(x_92, 1, x_2);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_5);
return x_93;
}
}
}
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; 
lean_dec(x_4);
lean_dec(x_3);
x_94 = lean_box(1);
x_95 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_95, 0, x_94);
lean_ctor_set(x_95, 1, x_2);
x_96 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_96, 0, x_95);
lean_ctor_set(x_96, 1, x_5);
return x_96;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_IR_ToIR_lowerArg(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_1);
return x_6;
}
}
static lean_object* _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = lean_box(0);
x_2 = lean_box(0);
x_3 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_3, 0, x_1);
lean_ctor_set(x_3, 1, x_2);
lean_ctor_set(x_3, 2, x_2);
lean_ctor_set(x_3, 3, x_2);
lean_ctor_set(x_3, 4, x_2);
x_4 = l_Array_empty(lean_box(0));
x_5 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_5, 0, x_3);
lean_ctor_set(x_5, 1, x_4);
x_6 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_6, 0, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; 
lean_dec(x_1);
x_4 = lean_box(1);
x_5 = lean_box(6);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_4);
lean_ctor_set(x_6, 1, x_5);
return x_6;
}
case 1:
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_3);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_9);
x_10 = lean_box(7);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_3);
lean_ctor_set(x_11, 1, x_10);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_12 = lean_ctor_get(x_3, 0);
lean_inc(x_12);
lean_dec(x_3);
x_13 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_1);
x_14 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_14, 0, x_13);
x_15 = lean_box(7);
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_14);
lean_ctor_set(x_16, 1, x_15);
return x_16;
}
}
case 2:
{
uint8_t x_17; 
x_17 = !lean_is_exclusive(x_3);
if (x_17 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_ctor_get(x_3, 0);
x_19 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_1);
lean_ctor_set_tag(x_3, 0);
lean_ctor_set(x_3, 0, x_19);
x_20 = lean_box(5);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_3);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_3, 0);
lean_inc(x_22);
lean_dec(x_3);
x_23 = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(x_23, 0, x_22);
lean_ctor_set(x_23, 1, x_1);
x_24 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_24, 0, x_23);
x_25 = lean_box(5);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
return x_26;
}
}
default: 
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_3);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_28 = lean_ctor_get(x_3, 2);
x_29 = lean_ctor_get(x_3, 0);
lean_dec(x_29);
x_30 = lean_ctor_get(x_2, 2);
x_31 = lean_ctor_get(x_2, 3);
x_32 = lean_nat_add(x_30, x_31);
lean_ctor_set_tag(x_3, 5);
lean_ctor_set(x_3, 2, x_1);
lean_ctor_set(x_3, 0, x_32);
x_33 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_33, 0, x_3);
x_34 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_34, 0, x_33);
lean_ctor_set(x_34, 1, x_28);
return x_34;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_35 = lean_ctor_get(x_3, 1);
x_36 = lean_ctor_get(x_3, 2);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_3);
x_37 = lean_ctor_get(x_2, 2);
x_38 = lean_ctor_get(x_2, 3);
x_39 = lean_nat_add(x_37, x_38);
x_40 = lean_alloc_ctor(5, 3, 0);
lean_ctor_set(x_40, 0, x_39);
lean_ctor_set(x_40, 1, x_35);
lean_ctor_set(x_40, 2, x_1);
x_41 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_42, 0, x_41);
lean_ctor_set(x_42, 1, x_36);
return x_42;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerProj___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_IR_ToIR_lowerProj(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerParam(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = l_Lean_IR_ToIR_bindVar___redArg(x_6, x_2, x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
x_9 = lean_ctor_get(x_7, 1);
lean_inc(x_9);
lean_dec(x_7);
x_10 = lean_ctor_get(x_8, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_8, 1);
lean_inc(x_11);
lean_dec(x_8);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
x_13 = l_Lean_IR_ToIR_lowerType(x_12, x_11, x_3, x_4, x_9);
if (lean_obj_tag(x_13) == 0)
{
uint8_t x_14; 
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; uint8_t x_16; 
x_15 = lean_ctor_get(x_13, 0);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_19 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_19, 0, x_10);
lean_ctor_set(x_19, 1, x_17);
lean_ctor_set_uint8(x_19, sizeof(void*)*2, x_18);
lean_ctor_set(x_15, 0, x_19);
return x_13;
}
else
{
lean_object* x_20; lean_object* x_21; uint8_t x_22; lean_object* x_23; lean_object* x_24; 
x_20 = lean_ctor_get(x_15, 0);
x_21 = lean_ctor_get(x_15, 1);
lean_inc(x_21);
lean_inc(x_20);
lean_dec(x_15);
x_22 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_23 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_23, 0, x_10);
lean_ctor_set(x_23, 1, x_20);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_22);
x_24 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_24, 0, x_23);
lean_ctor_set(x_24, 1, x_21);
lean_ctor_set(x_13, 0, x_24);
return x_13;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_25 = lean_ctor_get(x_13, 0);
x_26 = lean_ctor_get(x_13, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_13);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_25, 1);
lean_inc(x_28);
if (lean_is_exclusive(x_25)) {
 lean_ctor_release(x_25, 0);
 lean_ctor_release(x_25, 1);
 x_29 = x_25;
} else {
 lean_dec_ref(x_25);
 x_29 = lean_box(0);
}
x_30 = lean_ctor_get_uint8(x_1, sizeof(void*)*3);
lean_dec(x_1);
x_31 = lean_alloc_ctor(0, 2, 1);
lean_ctor_set(x_31, 0, x_10);
lean_ctor_set(x_31, 1, x_27);
lean_ctor_set_uint8(x_31, sizeof(void*)*2, x_30);
if (lean_is_scalar(x_29)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_29;
}
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_28);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_26);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_dec(x_10);
lean_dec(x_1);
x_34 = !lean_is_exclusive(x_13);
if (x_34 == 0)
{
return x_13;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_13, 0);
x_36 = lean_ctor_get(x_13, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_13);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_6 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__1), 5, 0);
x_7 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__4), 5, 0);
x_8 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__7), 5, 0);
x_9 = lean_alloc_closure((void*)(l_panic___at___Lean_IR_ToIR_lowerEnumToScalarType_spec__0___lam__9), 5, 0);
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
x_28 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_28, 0, x_18);
lean_ctor_set(x_28, 1, x_10);
lean_ctor_set(x_28, 2, x_21);
lean_ctor_set(x_28, 3, x_24);
lean_ctor_set(x_28, 4, x_27);
x_29 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_29, 0, x_28);
lean_ctor_set(x_29, 1, x_11);
lean_inc(x_29);
x_30 = lean_alloc_closure((void*)(l_StateT_map), 8, 3);
lean_closure_set(x_30, 0, lean_box(0));
lean_closure_set(x_30, 1, lean_box(0));
lean_closure_set(x_30, 2, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_6);
lean_inc(x_29);
x_32 = lean_alloc_closure((void*)(l_StateT_pure), 6, 3);
lean_closure_set(x_32, 0, lean_box(0));
lean_closure_set(x_32, 1, lean_box(0));
lean_closure_set(x_32, 2, x_29);
x_33 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_33, 0, x_31);
lean_ctor_set(x_33, 1, x_32);
lean_ctor_set(x_33, 2, x_7);
lean_ctor_set(x_33, 3, x_8);
lean_ctor_set(x_33, 4, x_9);
x_34 = lean_alloc_closure((void*)(l_StateT_bind), 8, 3);
lean_closure_set(x_34, 0, lean_box(0));
lean_closure_set(x_34, 1, lean_box(0));
lean_closure_set(x_34, 2, x_29);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_IR_instInhabitedFnBody;
x_37 = l_instInhabitedOfMonad___redArg(x_35, x_36);
x_38 = lean_panic_fn(x_37, x_1);
x_39 = lean_apply_4(x_38, x_2, x_3, x_4, x_5);
return x_39;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_23; lean_object* x_24; lean_object* x_67; lean_object* x_74; uint8_t x_75; 
x_74 = lean_array_get_size(x_4);
x_75 = lean_nat_dec_lt(x_6, x_74);
lean_dec(x_74);
if (x_75 == 0)
{
lean_object* x_76; 
x_76 = lean_box(0);
x_67 = x_76;
goto block_73;
}
else
{
lean_object* x_77; lean_object* x_78; 
x_77 = lean_array_fget(x_4, x_6);
x_78 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_78, 0, x_77);
x_67 = x_78;
goto block_73;
}
block_22:
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_15 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_16 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerAlt.loop", 26, 26);
x_17 = lean_unsigned_to_nat(367u);
x_18 = lean_unsigned_to_nat(18u);
x_19 = lean_mk_string_unchecked("mismatched fields and params", 28, 28);
x_20 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_15, x_16, x_17, x_18, x_19);
lean_dec(x_19);
lean_dec(x_16);
lean_dec(x_15);
x_21 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_20, x_11, x_12, x_13, x_14);
return x_21;
}
block_66:
{
if (lean_obj_tag(x_23) == 0)
{
lean_dec(x_6);
lean_dec(x_1);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; 
x_25 = l_Lean_IR_ToIR_lowerCode(x_2, x_7, x_8, x_9, x_10);
return x_25;
}
else
{
lean_dec(x_24);
lean_dec(x_2);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
goto block_22;
}
}
else
{
if (lean_obj_tag(x_24) == 0)
{
lean_dec(x_23);
lean_dec(x_6);
lean_dec(x_2);
lean_dec(x_1);
x_11 = x_7;
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
goto block_22;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; 
x_26 = lean_ctor_get(x_23, 0);
lean_inc(x_26);
lean_dec(x_23);
x_27 = lean_ctor_get(x_24, 0);
lean_inc(x_27);
lean_dec(x_24);
lean_inc(x_1);
x_28 = l_Lean_IR_ToIR_lowerProj(x_1, x_3, x_27);
x_29 = lean_ctor_get(x_28, 0);
lean_inc(x_29);
if (lean_obj_tag(x_29) == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; 
x_30 = lean_ctor_get(x_28, 1);
lean_inc(x_30);
lean_dec(x_28);
x_31 = lean_ctor_get(x_29, 0);
lean_inc(x_31);
lean_dec(x_29);
x_32 = lean_ctor_get(x_26, 0);
lean_inc(x_32);
lean_dec(x_26);
x_33 = l_Lean_IR_ToIR_bindVar___redArg(x_32, x_7, x_10);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
x_37 = lean_ctor_get(x_34, 1);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_6, x_38);
lean_dec(x_6);
x_40 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_39, x_37, x_8, x_9, x_35);
if (lean_obj_tag(x_40) == 0)
{
uint8_t x_41; 
x_41 = !lean_is_exclusive(x_40);
if (x_41 == 0)
{
lean_object* x_42; uint8_t x_43; 
x_42 = lean_ctor_get(x_40, 0);
x_43 = !lean_is_exclusive(x_42);
if (x_43 == 0)
{
lean_object* x_44; lean_object* x_45; 
x_44 = lean_ctor_get(x_42, 0);
x_45 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_45, 0, x_36);
lean_ctor_set(x_45, 1, x_30);
lean_ctor_set(x_45, 2, x_31);
lean_ctor_set(x_45, 3, x_44);
lean_ctor_set(x_42, 0, x_45);
return x_40;
}
else
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_46 = lean_ctor_get(x_42, 0);
x_47 = lean_ctor_get(x_42, 1);
lean_inc(x_47);
lean_inc(x_46);
lean_dec(x_42);
x_48 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_48, 0, x_36);
lean_ctor_set(x_48, 1, x_30);
lean_ctor_set(x_48, 2, x_31);
lean_ctor_set(x_48, 3, x_46);
x_49 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_47);
lean_ctor_set(x_40, 0, x_49);
return x_40;
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_50 = lean_ctor_get(x_40, 0);
x_51 = lean_ctor_get(x_40, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_40);
x_52 = lean_ctor_get(x_50, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_50, 1);
lean_inc(x_53);
if (lean_is_exclusive(x_50)) {
 lean_ctor_release(x_50, 0);
 lean_ctor_release(x_50, 1);
 x_54 = x_50;
} else {
 lean_dec_ref(x_50);
 x_54 = lean_box(0);
}
x_55 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_55, 0, x_36);
lean_ctor_set(x_55, 1, x_30);
lean_ctor_set(x_55, 2, x_31);
lean_ctor_set(x_55, 3, x_52);
if (lean_is_scalar(x_54)) {
 x_56 = lean_alloc_ctor(0, 2, 0);
} else {
 x_56 = x_54;
}
lean_ctor_set(x_56, 0, x_55);
lean_ctor_set(x_56, 1, x_53);
x_57 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_57, 0, x_56);
lean_ctor_set(x_57, 1, x_51);
return x_57;
}
}
else
{
lean_dec(x_36);
lean_dec(x_31);
lean_dec(x_30);
return x_40;
}
}
else
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
lean_dec(x_28);
x_58 = lean_ctor_get(x_26, 0);
lean_inc(x_58);
lean_dec(x_26);
x_59 = l_Lean_IR_ToIR_bindErased___redArg(x_58, x_7, x_10);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = lean_ctor_get(x_60, 1);
lean_inc(x_62);
lean_dec(x_60);
x_63 = lean_unsigned_to_nat(1u);
x_64 = lean_nat_add(x_6, x_63);
lean_dec(x_6);
x_6 = x_64;
x_7 = x_62;
x_10 = x_61;
goto _start;
}
}
}
}
block_73:
{
lean_object* x_68; uint8_t x_69; 
x_68 = lean_array_get_size(x_5);
x_69 = lean_nat_dec_lt(x_6, x_68);
lean_dec(x_68);
if (x_69 == 0)
{
lean_object* x_70; 
x_70 = lean_box(0);
x_23 = x_67;
x_24 = x_70;
goto block_66;
}
else
{
lean_object* x_71; lean_object* x_72; 
x_71 = lean_array_fget(x_5, x_6);
x_72 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_72, 0, x_71);
x_23 = x_67;
x_24 = x_72;
goto block_66;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_ToIR_lowerParam(x_11, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_18, x_2, x_15);
x_2 = x_21;
x_3 = x_22;
x_4 = x_16;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(size_t x_1, size_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_2, x_1);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_3);
lean_ctor_set(x_9, 1, x_4);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_9);
lean_ctor_set(x_10, 1, x_7);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_array_uget(x_3, x_2);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_ToIR_lowerArg(x_11, x_4, x_5, x_6, x_7);
lean_dec(x_11);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_20; size_t x_21; lean_object* x_22; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
x_15 = lean_ctor_get(x_13, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_13, 1);
lean_inc(x_16);
lean_dec(x_13);
x_17 = lean_box(0);
x_18 = lean_array_uset(x_3, x_2, x_17);
x_19 = lean_unsigned_to_nat(1u);
x_20 = lean_usize_of_nat(x_19);
x_21 = lean_usize_add(x_2, x_20);
x_22 = lean_array_uset(x_18, x_2, x_15);
x_2 = x_21;
x_3 = x_22;
x_4 = x_16;
x_7 = x_14;
goto _start;
}
else
{
uint8_t x_24; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
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
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; 
x_9 = lean_usize_dec_lt(x_3, x_2);
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
x_10 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_10, 0, x_4);
lean_ctor_set(x_10, 1, x_5);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_10);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_uget(x_4, x_3);
lean_inc(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_13 = lean_apply_5(x_1, x_12, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_13) == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; size_t x_21; size_t x_22; lean_object* x_23; 
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_ctor_get(x_14, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_14, 1);
lean_inc(x_17);
lean_dec(x_14);
x_18 = lean_box(0);
x_19 = lean_array_uset(x_4, x_3, x_18);
x_20 = lean_unsigned_to_nat(1u);
x_21 = lean_usize_of_nat(x_20);
x_22 = lean_usize_add(x_3, x_21);
x_23 = lean_array_uset(x_19, x_3, x_16);
x_3 = x_22;
x_4 = x_23;
x_5 = x_17;
x_8 = x_15;
goto _start;
}
else
{
uint8_t x_25; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
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
}
LEAN_EXPORT lean_object* l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = l_Lean_IR_instInhabitedArg;
x_3 = lean_panic_fn(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerCode(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_30; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
x_36 = lean_ctor_get(x_1, 1);
lean_inc(x_36);
lean_dec(x_1);
x_37 = l_Lean_IR_ToIR_lowerLet(x_35, x_36, x_2, x_3, x_4, x_5);
return x_37;
}
case 1:
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; 
lean_dec(x_1);
x_38 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_39 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_40 = lean_unsigned_to_nat(188u);
x_41 = lean_unsigned_to_nat(15u);
x_42 = lean_mk_string_unchecked("all local functions should be λ-lifted", 39, 38);
x_43 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_38, x_39, x_40, x_41, x_42);
lean_dec(x_42);
lean_dec(x_39);
lean_dec(x_38);
x_44 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_43, x_2, x_3, x_4, x_5);
return x_44;
}
case 2:
{
lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; size_t x_54; lean_object* x_55; size_t x_56; lean_object* x_57; 
x_45 = lean_ctor_get(x_1, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_1, 1);
lean_inc(x_46);
lean_dec(x_1);
x_47 = lean_ctor_get(x_45, 0);
lean_inc(x_47);
x_48 = l_Lean_IR_ToIR_bindJoinPoint___redArg(x_47, x_2, x_5);
x_49 = lean_ctor_get(x_48, 0);
lean_inc(x_49);
x_50 = lean_ctor_get(x_48, 1);
lean_inc(x_50);
lean_dec(x_48);
x_51 = lean_ctor_get(x_49, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_49, 1);
lean_inc(x_52);
lean_dec(x_49);
x_53 = lean_ctor_get(x_45, 2);
lean_inc(x_53);
x_54 = lean_array_size(x_53);
x_55 = lean_unsigned_to_nat(0u);
x_56 = lean_usize_of_nat(x_55);
lean_inc(x_4);
lean_inc(x_3);
x_57 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_54, x_56, x_53, x_52, x_3, x_4, x_50);
if (lean_obj_tag(x_57) == 0)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_58 = lean_ctor_get(x_57, 0);
lean_inc(x_58);
x_59 = lean_ctor_get(x_57, 1);
lean_inc(x_59);
lean_dec(x_57);
x_60 = lean_ctor_get(x_58, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_58, 1);
lean_inc(x_61);
lean_dec(x_58);
x_62 = lean_ctor_get(x_45, 4);
lean_inc(x_62);
lean_dec(x_45);
lean_inc(x_4);
lean_inc(x_3);
x_63 = l_Lean_IR_ToIR_lowerCode(x_62, x_61, x_3, x_4, x_59);
if (lean_obj_tag(x_63) == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_64 = lean_ctor_get(x_63, 0);
lean_inc(x_64);
x_65 = lean_ctor_get(x_63, 1);
lean_inc(x_65);
lean_dec(x_63);
x_66 = lean_ctor_get(x_64, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_64, 1);
lean_inc(x_67);
lean_dec(x_64);
x_68 = l_Lean_IR_ToIR_lowerCode(x_46, x_67, x_3, x_4, x_65);
if (lean_obj_tag(x_68) == 0)
{
uint8_t x_69; 
x_69 = !lean_is_exclusive(x_68);
if (x_69 == 0)
{
lean_object* x_70; uint8_t x_71; 
x_70 = lean_ctor_get(x_68, 0);
x_71 = !lean_is_exclusive(x_70);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_70, 0);
x_73 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_73, 0, x_51);
lean_ctor_set(x_73, 1, x_60);
lean_ctor_set(x_73, 2, x_66);
lean_ctor_set(x_73, 3, x_72);
lean_ctor_set(x_70, 0, x_73);
return x_68;
}
else
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_74 = lean_ctor_get(x_70, 0);
x_75 = lean_ctor_get(x_70, 1);
lean_inc(x_75);
lean_inc(x_74);
lean_dec(x_70);
x_76 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_76, 0, x_51);
lean_ctor_set(x_76, 1, x_60);
lean_ctor_set(x_76, 2, x_66);
lean_ctor_set(x_76, 3, x_74);
x_77 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_77, 0, x_76);
lean_ctor_set(x_77, 1, x_75);
lean_ctor_set(x_68, 0, x_77);
return x_68;
}
}
else
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_78 = lean_ctor_get(x_68, 0);
x_79 = lean_ctor_get(x_68, 1);
lean_inc(x_79);
lean_inc(x_78);
lean_dec(x_68);
x_80 = lean_ctor_get(x_78, 0);
lean_inc(x_80);
x_81 = lean_ctor_get(x_78, 1);
lean_inc(x_81);
if (lean_is_exclusive(x_78)) {
 lean_ctor_release(x_78, 0);
 lean_ctor_release(x_78, 1);
 x_82 = x_78;
} else {
 lean_dec_ref(x_78);
 x_82 = lean_box(0);
}
x_83 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_83, 0, x_51);
lean_ctor_set(x_83, 1, x_60);
lean_ctor_set(x_83, 2, x_66);
lean_ctor_set(x_83, 3, x_80);
if (lean_is_scalar(x_82)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_82;
}
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_84, 1, x_81);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_79);
return x_85;
}
}
else
{
lean_dec(x_66);
lean_dec(x_60);
lean_dec(x_51);
return x_68;
}
}
else
{
lean_dec(x_60);
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_4);
lean_dec(x_3);
return x_63;
}
}
else
{
uint8_t x_86; 
lean_dec(x_51);
lean_dec(x_46);
lean_dec(x_45);
lean_dec(x_4);
lean_dec(x_3);
x_86 = !lean_is_exclusive(x_57);
if (x_86 == 0)
{
return x_57;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_57, 0);
x_88 = lean_ctor_get(x_57, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_57);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
case 3:
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; uint8_t x_93; 
x_90 = lean_ctor_get(x_2, 0);
lean_inc(x_90);
x_91 = lean_ctor_get(x_1, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_1, 1);
lean_inc(x_92);
lean_dec(x_1);
x_93 = !lean_is_exclusive(x_90);
if (x_93 == 0)
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; uint64_t x_97; lean_object* x_98; uint64_t x_99; uint64_t x_100; uint64_t x_101; lean_object* x_102; uint64_t x_103; uint64_t x_104; uint64_t x_105; size_t x_106; size_t x_107; lean_object* x_108; size_t x_109; size_t x_110; size_t x_111; lean_object* x_112; lean_object* x_113; 
x_94 = lean_ctor_get(x_90, 1);
x_95 = lean_ctor_get(x_90, 0);
lean_dec(x_95);
x_96 = lean_array_get_size(x_94);
x_97 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_91);
x_98 = lean_unsigned_to_nat(32u);
x_99 = lean_uint64_of_nat(x_98);
x_100 = lean_uint64_shift_right(x_97, x_99);
x_101 = lean_uint64_xor(x_97, x_100);
x_102 = lean_unsigned_to_nat(16u);
x_103 = lean_uint64_of_nat(x_102);
x_104 = lean_uint64_shift_right(x_101, x_103);
x_105 = lean_uint64_xor(x_101, x_104);
x_106 = lean_uint64_to_usize(x_105);
x_107 = lean_usize_of_nat(x_96);
lean_dec(x_96);
x_108 = lean_unsigned_to_nat(1u);
x_109 = lean_usize_of_nat(x_108);
x_110 = lean_usize_sub(x_107, x_109);
x_111 = lean_usize_land(x_106, x_110);
x_112 = lean_array_uget(x_94, x_111);
lean_dec(x_94);
x_113 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_91, x_112);
lean_dec(x_112);
lean_dec(x_91);
if (lean_obj_tag(x_113) == 0)
{
lean_free_object(x_90);
lean_dec(x_92);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
goto block_17;
}
else
{
lean_object* x_114; 
x_114 = lean_ctor_get(x_113, 0);
lean_inc(x_114);
lean_dec(x_113);
switch (lean_obj_tag(x_114)) {
case 0:
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; 
lean_dec(x_114);
lean_free_object(x_90);
lean_dec(x_92);
x_115 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_116 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_117 = lean_unsigned_to_nat(172u);
x_118 = lean_unsigned_to_nat(46u);
x_119 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_120 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_115, x_116, x_117, x_118, x_119);
lean_dec(x_119);
lean_dec(x_116);
lean_dec(x_115);
x_121 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_120, x_2, x_3, x_4, x_5);
return x_121;
}
case 1:
{
lean_object* x_122; size_t x_123; lean_object* x_124; size_t x_125; lean_object* x_126; 
x_122 = lean_ctor_get(x_114, 0);
lean_inc(x_122);
lean_dec(x_114);
x_123 = lean_array_size(x_92);
x_124 = lean_unsigned_to_nat(0u);
x_125 = lean_usize_of_nat(x_124);
x_126 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_123, x_125, x_92, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_126) == 0)
{
uint8_t x_127; 
x_127 = !lean_is_exclusive(x_126);
if (x_127 == 0)
{
lean_object* x_128; uint8_t x_129; 
x_128 = lean_ctor_get(x_126, 0);
x_129 = !lean_is_exclusive(x_128);
if (x_129 == 0)
{
lean_object* x_130; 
x_130 = lean_ctor_get(x_128, 0);
lean_ctor_set_tag(x_90, 12);
lean_ctor_set(x_90, 1, x_130);
lean_ctor_set(x_90, 0, x_122);
lean_ctor_set(x_128, 0, x_90);
return x_126;
}
else
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; 
x_131 = lean_ctor_get(x_128, 0);
x_132 = lean_ctor_get(x_128, 1);
lean_inc(x_132);
lean_inc(x_131);
lean_dec(x_128);
lean_ctor_set_tag(x_90, 12);
lean_ctor_set(x_90, 1, x_131);
lean_ctor_set(x_90, 0, x_122);
x_133 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_133, 0, x_90);
lean_ctor_set(x_133, 1, x_132);
lean_ctor_set(x_126, 0, x_133);
return x_126;
}
}
else
{
lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_134 = lean_ctor_get(x_126, 0);
x_135 = lean_ctor_get(x_126, 1);
lean_inc(x_135);
lean_inc(x_134);
lean_dec(x_126);
x_136 = lean_ctor_get(x_134, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_134, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_134)) {
 lean_ctor_release(x_134, 0);
 lean_ctor_release(x_134, 1);
 x_138 = x_134;
} else {
 lean_dec_ref(x_134);
 x_138 = lean_box(0);
}
lean_ctor_set_tag(x_90, 12);
lean_ctor_set(x_90, 1, x_136);
lean_ctor_set(x_90, 0, x_122);
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_90);
lean_ctor_set(x_139, 1, x_137);
x_140 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_135);
return x_140;
}
}
else
{
uint8_t x_141; 
lean_dec(x_122);
lean_free_object(x_90);
x_141 = !lean_is_exclusive(x_126);
if (x_141 == 0)
{
return x_126;
}
else
{
lean_object* x_142; lean_object* x_143; lean_object* x_144; 
x_142 = lean_ctor_get(x_126, 0);
x_143 = lean_ctor_get(x_126, 1);
lean_inc(x_143);
lean_inc(x_142);
lean_dec(x_126);
x_144 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_144, 0, x_142);
lean_ctor_set(x_144, 1, x_143);
return x_144;
}
}
}
default: 
{
lean_free_object(x_90);
lean_dec(x_92);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
goto block_17;
}
}
}
}
else
{
lean_object* x_145; lean_object* x_146; uint64_t x_147; lean_object* x_148; uint64_t x_149; uint64_t x_150; uint64_t x_151; lean_object* x_152; uint64_t x_153; uint64_t x_154; uint64_t x_155; size_t x_156; size_t x_157; lean_object* x_158; size_t x_159; size_t x_160; size_t x_161; lean_object* x_162; lean_object* x_163; 
x_145 = lean_ctor_get(x_90, 1);
lean_inc(x_145);
lean_dec(x_90);
x_146 = lean_array_get_size(x_145);
x_147 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_91);
x_148 = lean_unsigned_to_nat(32u);
x_149 = lean_uint64_of_nat(x_148);
x_150 = lean_uint64_shift_right(x_147, x_149);
x_151 = lean_uint64_xor(x_147, x_150);
x_152 = lean_unsigned_to_nat(16u);
x_153 = lean_uint64_of_nat(x_152);
x_154 = lean_uint64_shift_right(x_151, x_153);
x_155 = lean_uint64_xor(x_151, x_154);
x_156 = lean_uint64_to_usize(x_155);
x_157 = lean_usize_of_nat(x_146);
lean_dec(x_146);
x_158 = lean_unsigned_to_nat(1u);
x_159 = lean_usize_of_nat(x_158);
x_160 = lean_usize_sub(x_157, x_159);
x_161 = lean_usize_land(x_156, x_160);
x_162 = lean_array_uget(x_145, x_161);
lean_dec(x_145);
x_163 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_91, x_162);
lean_dec(x_162);
lean_dec(x_91);
if (lean_obj_tag(x_163) == 0)
{
lean_dec(x_92);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
goto block_17;
}
else
{
lean_object* x_164; 
x_164 = lean_ctor_get(x_163, 0);
lean_inc(x_164);
lean_dec(x_163);
switch (lean_obj_tag(x_164)) {
case 0:
{
lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; 
lean_dec(x_164);
lean_dec(x_92);
x_165 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_166 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_167 = lean_unsigned_to_nat(172u);
x_168 = lean_unsigned_to_nat(46u);
x_169 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_170 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_165, x_166, x_167, x_168, x_169);
lean_dec(x_169);
lean_dec(x_166);
lean_dec(x_165);
x_171 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_170, x_2, x_3, x_4, x_5);
return x_171;
}
case 1:
{
lean_object* x_172; size_t x_173; lean_object* x_174; size_t x_175; lean_object* x_176; 
x_172 = lean_ctor_get(x_164, 0);
lean_inc(x_172);
lean_dec(x_164);
x_173 = lean_array_size(x_92);
x_174 = lean_unsigned_to_nat(0u);
x_175 = lean_usize_of_nat(x_174);
x_176 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_173, x_175, x_92, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_176) == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; 
x_177 = lean_ctor_get(x_176, 0);
lean_inc(x_177);
x_178 = lean_ctor_get(x_176, 1);
lean_inc(x_178);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_179 = x_176;
} else {
 lean_dec_ref(x_176);
 x_179 = lean_box(0);
}
x_180 = lean_ctor_get(x_177, 0);
lean_inc(x_180);
x_181 = lean_ctor_get(x_177, 1);
lean_inc(x_181);
if (lean_is_exclusive(x_177)) {
 lean_ctor_release(x_177, 0);
 lean_ctor_release(x_177, 1);
 x_182 = x_177;
} else {
 lean_dec_ref(x_177);
 x_182 = lean_box(0);
}
x_183 = lean_alloc_ctor(12, 2, 0);
lean_ctor_set(x_183, 0, x_172);
lean_ctor_set(x_183, 1, x_180);
if (lean_is_scalar(x_182)) {
 x_184 = lean_alloc_ctor(0, 2, 0);
} else {
 x_184 = x_182;
}
lean_ctor_set(x_184, 0, x_183);
lean_ctor_set(x_184, 1, x_181);
if (lean_is_scalar(x_179)) {
 x_185 = lean_alloc_ctor(0, 2, 0);
} else {
 x_185 = x_179;
}
lean_ctor_set(x_185, 0, x_184);
lean_ctor_set(x_185, 1, x_178);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; 
lean_dec(x_172);
x_186 = lean_ctor_get(x_176, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_176, 1);
lean_inc(x_187);
if (lean_is_exclusive(x_176)) {
 lean_ctor_release(x_176, 0);
 lean_ctor_release(x_176, 1);
 x_188 = x_176;
} else {
 lean_dec_ref(x_176);
 x_188 = lean_box(0);
}
if (lean_is_scalar(x_188)) {
 x_189 = lean_alloc_ctor(1, 2, 0);
} else {
 x_189 = x_188;
}
lean_ctor_set(x_189, 0, x_186);
lean_ctor_set(x_189, 1, x_187);
return x_189;
}
}
default: 
{
lean_dec(x_92);
x_6 = x_2;
x_7 = x_3;
x_8 = x_4;
x_9 = x_5;
goto block_17;
}
}
}
}
}
case 4:
{
lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; uint64_t x_195; lean_object* x_196; uint64_t x_197; uint64_t x_198; uint64_t x_199; lean_object* x_200; uint64_t x_201; uint64_t x_202; uint64_t x_203; size_t x_204; size_t x_205; lean_object* x_206; size_t x_207; size_t x_208; size_t x_209; lean_object* x_210; lean_object* x_211; 
x_190 = lean_ctor_get(x_2, 0);
lean_inc(x_190);
x_191 = lean_ctor_get(x_1, 0);
lean_inc(x_191);
lean_dec(x_1);
x_192 = lean_ctor_get(x_190, 1);
lean_inc(x_192);
lean_dec(x_190);
x_193 = lean_ctor_get(x_191, 2);
lean_inc(x_193);
x_194 = lean_array_get_size(x_192);
x_195 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_193);
x_196 = lean_unsigned_to_nat(32u);
x_197 = lean_uint64_of_nat(x_196);
x_198 = lean_uint64_shift_right(x_195, x_197);
x_199 = lean_uint64_xor(x_195, x_198);
x_200 = lean_unsigned_to_nat(16u);
x_201 = lean_uint64_of_nat(x_200);
x_202 = lean_uint64_shift_right(x_199, x_201);
x_203 = lean_uint64_xor(x_199, x_202);
x_204 = lean_uint64_to_usize(x_203);
x_205 = lean_usize_of_nat(x_194);
lean_dec(x_194);
x_206 = lean_unsigned_to_nat(1u);
x_207 = lean_usize_of_nat(x_206);
x_208 = lean_usize_sub(x_205, x_207);
x_209 = lean_usize_land(x_204, x_208);
x_210 = lean_array_uget(x_192, x_209);
lean_dec(x_192);
x_211 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_193, x_210);
lean_dec(x_210);
lean_dec(x_193);
if (lean_obj_tag(x_211) == 0)
{
lean_dec(x_191);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_29;
}
else
{
lean_object* x_212; 
x_212 = lean_ctor_get(x_211, 0);
lean_inc(x_212);
lean_dec(x_211);
switch (lean_obj_tag(x_212)) {
case 0:
{
lean_object* x_213; lean_object* x_214; lean_object* x_215; 
x_213 = lean_ctor_get(x_212, 0);
lean_inc(x_213);
lean_dec(x_212);
x_214 = lean_ctor_get(x_191, 1);
lean_inc(x_214);
lean_inc(x_4);
lean_inc(x_3);
x_215 = l_Lean_IR_ToIR_lowerType(x_214, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_215) == 0)
{
lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; size_t x_222; lean_object* x_223; size_t x_224; lean_object* x_225; 
x_216 = lean_ctor_get(x_215, 0);
lean_inc(x_216);
x_217 = lean_ctor_get(x_215, 1);
lean_inc(x_217);
lean_dec(x_215);
x_218 = lean_ctor_get(x_216, 0);
lean_inc(x_218);
x_219 = lean_ctor_get(x_216, 1);
lean_inc(x_219);
lean_dec(x_216);
lean_inc(x_213);
x_220 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerAlt), 6, 1);
lean_closure_set(x_220, 0, x_213);
x_221 = lean_ctor_get(x_191, 3);
lean_inc(x_221);
x_222 = lean_array_size(x_221);
x_223 = lean_unsigned_to_nat(0u);
x_224 = lean_usize_of_nat(x_223);
x_225 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_220, x_222, x_224, x_221, x_219, x_3, x_4, x_217);
if (lean_obj_tag(x_225) == 0)
{
uint8_t x_226; 
x_226 = !lean_is_exclusive(x_225);
if (x_226 == 0)
{
lean_object* x_227; uint8_t x_228; 
x_227 = lean_ctor_get(x_225, 0);
x_228 = !lean_is_exclusive(x_227);
if (x_228 == 0)
{
lean_object* x_229; lean_object* x_230; lean_object* x_231; 
x_229 = lean_ctor_get(x_227, 0);
x_230 = lean_ctor_get(x_191, 0);
lean_inc(x_230);
lean_dec(x_191);
x_231 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_231, 0, x_230);
lean_ctor_set(x_231, 1, x_213);
lean_ctor_set(x_231, 2, x_218);
lean_ctor_set(x_231, 3, x_229);
lean_ctor_set(x_227, 0, x_231);
return x_225;
}
else
{
lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; 
x_232 = lean_ctor_get(x_227, 0);
x_233 = lean_ctor_get(x_227, 1);
lean_inc(x_233);
lean_inc(x_232);
lean_dec(x_227);
x_234 = lean_ctor_get(x_191, 0);
lean_inc(x_234);
lean_dec(x_191);
x_235 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_235, 0, x_234);
lean_ctor_set(x_235, 1, x_213);
lean_ctor_set(x_235, 2, x_218);
lean_ctor_set(x_235, 3, x_232);
x_236 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_236, 0, x_235);
lean_ctor_set(x_236, 1, x_233);
lean_ctor_set(x_225, 0, x_236);
return x_225;
}
}
else
{
lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_237 = lean_ctor_get(x_225, 0);
x_238 = lean_ctor_get(x_225, 1);
lean_inc(x_238);
lean_inc(x_237);
lean_dec(x_225);
x_239 = lean_ctor_get(x_237, 0);
lean_inc(x_239);
x_240 = lean_ctor_get(x_237, 1);
lean_inc(x_240);
if (lean_is_exclusive(x_237)) {
 lean_ctor_release(x_237, 0);
 lean_ctor_release(x_237, 1);
 x_241 = x_237;
} else {
 lean_dec_ref(x_237);
 x_241 = lean_box(0);
}
x_242 = lean_ctor_get(x_191, 0);
lean_inc(x_242);
lean_dec(x_191);
x_243 = lean_alloc_ctor(10, 4, 0);
lean_ctor_set(x_243, 0, x_242);
lean_ctor_set(x_243, 1, x_213);
lean_ctor_set(x_243, 2, x_218);
lean_ctor_set(x_243, 3, x_239);
if (lean_is_scalar(x_241)) {
 x_244 = lean_alloc_ctor(0, 2, 0);
} else {
 x_244 = x_241;
}
lean_ctor_set(x_244, 0, x_243);
lean_ctor_set(x_244, 1, x_240);
x_245 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_245, 0, x_244);
lean_ctor_set(x_245, 1, x_238);
return x_245;
}
}
else
{
uint8_t x_246; 
lean_dec(x_218);
lean_dec(x_213);
lean_dec(x_191);
x_246 = !lean_is_exclusive(x_225);
if (x_246 == 0)
{
return x_225;
}
else
{
lean_object* x_247; lean_object* x_248; lean_object* x_249; 
x_247 = lean_ctor_get(x_225, 0);
x_248 = lean_ctor_get(x_225, 1);
lean_inc(x_248);
lean_inc(x_247);
lean_dec(x_225);
x_249 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_249, 0, x_247);
lean_ctor_set(x_249, 1, x_248);
return x_249;
}
}
}
else
{
uint8_t x_250; 
lean_dec(x_213);
lean_dec(x_191);
lean_dec(x_4);
lean_dec(x_3);
x_250 = !lean_is_exclusive(x_215);
if (x_250 == 0)
{
return x_215;
}
else
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_215, 0);
x_252 = lean_ctor_get(x_215, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_215);
x_253 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_253, 0, x_251);
lean_ctor_set(x_253, 1, x_252);
return x_253;
}
}
}
case 1:
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; 
lean_dec(x_212);
lean_dec(x_191);
x_254 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_255 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_256 = lean_unsigned_to_nat(180u);
x_257 = lean_unsigned_to_nat(52u);
x_258 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_259 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_254, x_255, x_256, x_257, x_258);
lean_dec(x_258);
lean_dec(x_255);
lean_dec(x_254);
x_260 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_259, x_2, x_3, x_4, x_5);
return x_260;
}
default: 
{
lean_dec(x_191);
x_18 = x_2;
x_19 = x_3;
x_20 = x_4;
x_21 = x_5;
goto block_29;
}
}
}
}
case 5:
{
lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; uint64_t x_265; lean_object* x_266; uint64_t x_267; uint64_t x_268; uint64_t x_269; lean_object* x_270; uint64_t x_271; uint64_t x_272; uint64_t x_273; size_t x_274; size_t x_275; lean_object* x_276; size_t x_277; size_t x_278; size_t x_279; lean_object* x_280; lean_object* x_281; 
lean_dec(x_4);
lean_dec(x_3);
x_261 = lean_ctor_get(x_2, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_1, 0);
lean_inc(x_262);
lean_dec(x_1);
x_263 = lean_ctor_get(x_261, 1);
lean_inc(x_263);
lean_dec(x_261);
x_264 = lean_array_get_size(x_263);
x_265 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_262);
x_266 = lean_unsigned_to_nat(32u);
x_267 = lean_uint64_of_nat(x_266);
x_268 = lean_uint64_shift_right(x_265, x_267);
x_269 = lean_uint64_xor(x_265, x_268);
x_270 = lean_unsigned_to_nat(16u);
x_271 = lean_uint64_of_nat(x_270);
x_272 = lean_uint64_shift_right(x_269, x_271);
x_273 = lean_uint64_xor(x_269, x_272);
x_274 = lean_uint64_to_usize(x_273);
x_275 = lean_usize_of_nat(x_264);
lean_dec(x_264);
x_276 = lean_unsigned_to_nat(1u);
x_277 = lean_usize_of_nat(x_276);
x_278 = lean_usize_sub(x_275, x_277);
x_279 = lean_usize_land(x_274, x_278);
x_280 = lean_array_uget(x_263, x_279);
lean_dec(x_263);
x_281 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_262, x_280);
lean_dec(x_280);
lean_dec(x_262);
if (lean_obj_tag(x_281) == 0)
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; lean_object* x_287; lean_object* x_288; 
x_282 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_283 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_284 = lean_unsigned_to_nat(185u);
x_285 = lean_unsigned_to_nat(37u);
x_286 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_287 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_282, x_283, x_284, x_285, x_286);
lean_dec(x_286);
lean_dec(x_283);
lean_dec(x_282);
x_288 = l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(x_287);
x_30 = x_288;
goto block_34;
}
else
{
lean_object* x_289; 
x_289 = lean_ctor_get(x_281, 0);
lean_inc(x_289);
lean_dec(x_281);
switch (lean_obj_tag(x_289)) {
case 0:
{
uint8_t x_290; 
x_290 = !lean_is_exclusive(x_289);
if (x_290 == 0)
{
x_30 = x_289;
goto block_34;
}
else
{
lean_object* x_291; lean_object* x_292; 
x_291 = lean_ctor_get(x_289, 0);
lean_inc(x_291);
lean_dec(x_289);
x_292 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_292, 0, x_291);
x_30 = x_292;
goto block_34;
}
}
case 1:
{
lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; lean_object* x_298; lean_object* x_299; 
lean_dec(x_289);
x_293 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_294 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_295 = lean_unsigned_to_nat(185u);
x_296 = lean_unsigned_to_nat(37u);
x_297 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_298 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_293, x_294, x_295, x_296, x_297);
lean_dec(x_297);
lean_dec(x_294);
lean_dec(x_293);
x_299 = l_panic___at___Lean_IR_ToIR_lowerCode_spec__3(x_298);
x_30 = x_299;
goto block_34;
}
default: 
{
lean_object* x_300; 
x_300 = lean_box(1);
x_30 = x_300;
goto block_34;
}
}
}
}
default: 
{
lean_object* x_301; lean_object* x_302; lean_object* x_303; 
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_301 = lean_box(13);
x_302 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_302, 0, x_301);
lean_ctor_set(x_302, 1, x_2);
x_303 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_303, 0, x_302);
lean_ctor_set(x_303, 1, x_5);
return x_303;
}
}
block_17:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_10 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_11 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_12 = lean_unsigned_to_nat(172u);
x_13 = lean_unsigned_to_nat(46u);
x_14 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_15 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_10, x_11, x_12, x_13, x_14);
lean_dec(x_14);
lean_dec(x_11);
lean_dec(x_10);
x_16 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_15, x_6, x_7, x_8, x_9);
return x_16;
}
block_29:
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_22 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_23 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerCode", 22, 22);
x_24 = lean_unsigned_to_nat(180u);
x_25 = lean_unsigned_to_nat(52u);
x_26 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_27 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_22, x_23, x_24, x_25, x_26);
lean_dec(x_26);
lean_dec(x_23);
lean_dec(x_22);
x_28 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_27, x_18, x_19, x_20, x_21);
return x_28;
}
block_34:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_31);
lean_ctor_set(x_32, 1, x_2);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_5);
return x_33;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
x_8 = lean_ctor_get(x_2, 1);
lean_inc(x_8);
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec(x_2);
lean_inc(x_5);
lean_inc(x_4);
x_10 = l_Lean_IR_ToIR_getCtorInfo(x_7, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = !lean_is_exclusive(x_12);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_16 = lean_ctor_get(x_12, 0);
x_17 = lean_ctor_get(x_12, 1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_16, x_8, x_17, x_18, x_14, x_4, x_5, x_13);
lean_dec(x_17);
lean_dec(x_8);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_21, 0);
lean_ctor_set(x_12, 1, x_23);
lean_ctor_set(x_21, 0, x_12);
return x_19;
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_24 = lean_ctor_get(x_21, 0);
x_25 = lean_ctor_get(x_21, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_21);
lean_ctor_set(x_12, 1, x_24);
x_26 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_26, 0, x_12);
lean_ctor_set(x_26, 1, x_25);
lean_ctor_set(x_19, 0, x_26);
return x_19;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_27 = lean_ctor_get(x_19, 0);
x_28 = lean_ctor_get(x_19, 1);
lean_inc(x_28);
lean_inc(x_27);
lean_dec(x_19);
x_29 = lean_ctor_get(x_27, 0);
lean_inc(x_29);
x_30 = lean_ctor_get(x_27, 1);
lean_inc(x_30);
if (lean_is_exclusive(x_27)) {
 lean_ctor_release(x_27, 0);
 lean_ctor_release(x_27, 1);
 x_31 = x_27;
} else {
 lean_dec_ref(x_27);
 x_31 = lean_box(0);
}
lean_ctor_set(x_12, 1, x_29);
if (lean_is_scalar(x_31)) {
 x_32 = lean_alloc_ctor(0, 2, 0);
} else {
 x_32 = x_31;
}
lean_ctor_set(x_32, 0, x_12);
lean_ctor_set(x_32, 1, x_30);
x_33 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_33, 0, x_32);
lean_ctor_set(x_33, 1, x_28);
return x_33;
}
}
else
{
uint8_t x_34; 
lean_free_object(x_12);
lean_dec(x_16);
x_34 = !lean_is_exclusive(x_19);
if (x_34 == 0)
{
return x_19;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_35 = lean_ctor_get(x_19, 0);
x_36 = lean_ctor_get(x_19, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_19);
x_37 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_38 = lean_ctor_get(x_12, 0);
x_39 = lean_ctor_get(x_12, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_12);
x_40 = lean_unsigned_to_nat(0u);
x_41 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_9, x_38, x_8, x_39, x_40, x_14, x_4, x_5, x_13);
lean_dec(x_39);
lean_dec(x_8);
if (lean_obj_tag(x_41) == 0)
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_44 = x_41;
} else {
 lean_dec_ref(x_41);
 x_44 = lean_box(0);
}
x_45 = lean_ctor_get(x_42, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_42, 1);
lean_inc(x_46);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_47 = x_42;
} else {
 lean_dec_ref(x_42);
 x_47 = lean_box(0);
}
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_38);
lean_ctor_set(x_48, 1, x_45);
if (lean_is_scalar(x_47)) {
 x_49 = lean_alloc_ctor(0, 2, 0);
} else {
 x_49 = x_47;
}
lean_ctor_set(x_49, 0, x_48);
lean_ctor_set(x_49, 1, x_46);
if (lean_is_scalar(x_44)) {
 x_50 = lean_alloc_ctor(0, 2, 0);
} else {
 x_50 = x_44;
}
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_43);
return x_50;
}
else
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; 
lean_dec(x_38);
x_51 = lean_ctor_get(x_41, 0);
lean_inc(x_51);
x_52 = lean_ctor_get(x_41, 1);
lean_inc(x_52);
if (lean_is_exclusive(x_41)) {
 lean_ctor_release(x_41, 0);
 lean_ctor_release(x_41, 1);
 x_53 = x_41;
} else {
 lean_dec_ref(x_41);
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
}
else
{
uint8_t x_55; 
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_1);
x_55 = !lean_is_exclusive(x_10);
if (x_55 == 0)
{
return x_10;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_10, 0);
x_57 = lean_ctor_get(x_10, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_10);
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
lean_dec(x_1);
x_59 = !lean_is_exclusive(x_2);
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_ctor_get(x_2, 0);
x_61 = l_Lean_IR_ToIR_lowerCode(x_60, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_61) == 0)
{
uint8_t x_62; 
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
lean_object* x_63; uint8_t x_64; 
x_63 = lean_ctor_get(x_61, 0);
x_64 = !lean_is_exclusive(x_63);
if (x_64 == 0)
{
lean_object* x_65; 
x_65 = lean_ctor_get(x_63, 0);
lean_ctor_set(x_2, 0, x_65);
lean_ctor_set(x_63, 0, x_2);
return x_61;
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; 
x_66 = lean_ctor_get(x_63, 0);
x_67 = lean_ctor_get(x_63, 1);
lean_inc(x_67);
lean_inc(x_66);
lean_dec(x_63);
lean_ctor_set(x_2, 0, x_66);
x_68 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_68, 0, x_2);
lean_ctor_set(x_68, 1, x_67);
lean_ctor_set(x_61, 0, x_68);
return x_61;
}
}
else
{
lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; 
x_69 = lean_ctor_get(x_61, 0);
x_70 = lean_ctor_get(x_61, 1);
lean_inc(x_70);
lean_inc(x_69);
lean_dec(x_61);
x_71 = lean_ctor_get(x_69, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_69, 1);
lean_inc(x_72);
if (lean_is_exclusive(x_69)) {
 lean_ctor_release(x_69, 0);
 lean_ctor_release(x_69, 1);
 x_73 = x_69;
} else {
 lean_dec_ref(x_69);
 x_73 = lean_box(0);
}
lean_ctor_set(x_2, 0, x_71);
if (lean_is_scalar(x_73)) {
 x_74 = lean_alloc_ctor(0, 2, 0);
} else {
 x_74 = x_73;
}
lean_ctor_set(x_74, 0, x_2);
lean_ctor_set(x_74, 1, x_72);
x_75 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_75, 0, x_74);
lean_ctor_set(x_75, 1, x_70);
return x_75;
}
}
else
{
uint8_t x_76; 
lean_free_object(x_2);
x_76 = !lean_is_exclusive(x_61);
if (x_76 == 0)
{
return x_61;
}
else
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_77 = lean_ctor_get(x_61, 0);
x_78 = lean_ctor_get(x_61, 1);
lean_inc(x_78);
lean_inc(x_77);
lean_dec(x_61);
x_79 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_79, 0, x_77);
lean_ctor_set(x_79, 1, x_78);
return x_79;
}
}
}
else
{
lean_object* x_80; lean_object* x_81; 
x_80 = lean_ctor_get(x_2, 0);
lean_inc(x_80);
lean_dec(x_2);
x_81 = l_Lean_IR_ToIR_lowerCode(x_80, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_81) == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; 
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
x_85 = lean_ctor_get(x_82, 0);
lean_inc(x_85);
x_86 = lean_ctor_get(x_82, 1);
lean_inc(x_86);
if (lean_is_exclusive(x_82)) {
 lean_ctor_release(x_82, 0);
 lean_ctor_release(x_82, 1);
 x_87 = x_82;
} else {
 lean_dec_ref(x_82);
 x_87 = lean_box(0);
}
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_85);
if (lean_is_scalar(x_87)) {
 x_89 = lean_alloc_ctor(0, 2, 0);
} else {
 x_89 = x_87;
}
lean_ctor_set(x_89, 0, x_88);
lean_ctor_set(x_89, 1, x_86);
if (lean_is_scalar(x_84)) {
 x_90 = lean_alloc_ctor(0, 2, 0);
} else {
 x_90 = x_84;
}
lean_ctor_set(x_90, 0, x_89);
lean_ctor_set(x_90, 1, x_83);
return x_90;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; 
x_91 = lean_ctor_get(x_81, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_81, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_81)) {
 lean_ctor_release(x_81, 0);
 lean_ctor_release(x_81, 1);
 x_93 = x_81;
} else {
 lean_dec_ref(x_81);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; uint8_t x_6; 
x_5 = l_Lean_addMessageContextPartial___at___Lean_throwError___at___Lean_Core_instantiateValueLevelParams_spec__0_spec__0(x_1, x_2, x_3, x_4);
x_6 = !lean_is_exclusive(x_5);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = lean_ctor_get(x_5, 0);
x_8 = lean_ctor_get(x_2, 5);
lean_inc(x_8);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set_tag(x_5, 1);
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
x_12 = lean_ctor_get(x_2, 5);
lean_inc(x_12);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_10);
x_14 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_11);
return x_14;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_2, x_4, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_4, 1);
x_20 = lean_nat_dec_lt(x_6, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_dec(x_6);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_5);
lean_ctor_set(x_21, 1, x_7);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_box(0);
x_24 = lean_box(0);
x_25 = lean_array_get(x_24, x_1, x_6);
if (lean_obj_tag(x_25) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; lean_object* x_35; uint64_t x_36; uint64_t x_37; uint64_t x_38; size_t x_39; size_t x_40; lean_object* x_41; size_t x_42; size_t x_43; size_t x_44; lean_object* x_45; lean_object* x_46; 
x_26 = lean_ctor_get(x_7, 0);
lean_inc(x_26);
x_27 = lean_ctor_get(x_25, 0);
lean_inc(x_27);
lean_dec(x_25);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = lean_array_get_size(x_28);
x_30 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_27);
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
x_46 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_27, x_45);
lean_dec(x_45);
lean_dec(x_27);
if (lean_obj_tag(x_46) == 0)
{
x_9 = x_5;
x_10 = x_7;
x_11 = x_8;
goto block_15;
}
else
{
lean_object* x_47; 
x_47 = lean_ctor_get(x_46, 0);
lean_inc(x_47);
lean_dec(x_46);
if (lean_obj_tag(x_47) == 0)
{
lean_object* x_48; lean_object* x_49; lean_object* x_53; 
x_48 = lean_ctor_get(x_47, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_47)) {
 lean_ctor_release(x_47, 0);
 x_49 = x_47;
} else {
 lean_dec_ref(x_47);
 x_49 = lean_box(0);
}
x_53 = lean_array_get(x_23, x_2, x_6);
if (lean_obj_tag(x_53) == 1)
{
lean_dec(x_53);
goto block_52;
}
else
{
lean_dec(x_53);
if (x_3 == 0)
{
lean_dec(x_49);
lean_dec(x_48);
x_9 = x_5;
x_10 = x_7;
x_11 = x_8;
goto block_15;
}
else
{
goto block_52;
}
}
block_52:
{
lean_object* x_50; lean_object* x_51; 
if (lean_is_scalar(x_49)) {
 x_50 = lean_alloc_ctor(0, 1, 0);
} else {
 x_50 = x_49;
}
lean_ctor_set(x_50, 0, x_48);
x_51 = lean_array_push(x_5, x_50);
x_9 = x_51;
x_10 = x_7;
x_11 = x_8;
goto block_15;
}
}
else
{
lean_dec(x_47);
x_9 = x_5;
x_10 = x_7;
x_11 = x_8;
goto block_15;
}
}
}
else
{
lean_object* x_54; 
lean_dec(x_25);
x_54 = lean_array_get(x_23, x_2, x_6);
if (lean_obj_tag(x_54) == 1)
{
lean_dec(x_54);
goto block_18;
}
else
{
lean_dec(x_54);
if (x_3 == 0)
{
x_9 = x_5;
x_10 = x_7;
x_11 = x_8;
goto block_15;
}
else
{
goto block_18;
}
}
}
}
block_15:
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_4, 2);
x_13 = lean_nat_add(x_6, x_12);
lean_dec(x_6);
x_5 = x_9;
x_6 = x_13;
x_7 = x_10;
x_8 = x_11;
goto _start;
}
block_18:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_box(1);
x_17 = lean_array_push(x_5, x_16);
x_9 = x_17;
x_10 = x_7;
x_11 = x_8;
goto block_15;
}
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1(lean_object* x_1, lean_object* x_2, uint8_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_9, x_12);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_IR_ToIR_bindErased___redArg(x_8, x_4, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_IR_ToIR_lowerCode(x_2, x_12, x_5, x_6, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
x_9 = l_Lean_IR_ToIR_bindVar___redArg(x_8, x_4, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 0);
lean_inc(x_12);
x_13 = lean_ctor_get(x_10, 1);
lean_inc(x_13);
lean_dec(x_10);
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_38; 
lean_dec(x_1);
x_38 = lean_box(7);
x_14 = x_38;
x_15 = x_13;
x_16 = x_5;
x_17 = x_6;
x_18 = x_11;
goto block_37;
}
case 3:
{
lean_object* x_39; 
lean_dec(x_1);
x_39 = lean_box(7);
x_14 = x_39;
x_15 = x_13;
x_16 = x_5;
x_17 = x_6;
x_18 = x_11;
goto block_37;
}
case 7:
{
lean_object* x_40; 
lean_dec(x_1);
x_40 = lean_box(7);
x_14 = x_40;
x_15 = x_13;
x_16 = x_5;
x_17 = x_6;
x_18 = x_11;
goto block_37;
}
default: 
{
lean_object* x_41; lean_object* x_42; 
x_41 = lean_ctor_get(x_1, 2);
lean_inc(x_41);
lean_dec(x_1);
lean_inc(x_6);
lean_inc(x_5);
x_42 = l_Lean_IR_ToIR_lowerType(x_41, x_13, x_5, x_6, x_11);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
x_44 = lean_ctor_get(x_42, 1);
lean_inc(x_44);
lean_dec(x_42);
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
lean_dec(x_43);
x_14 = x_45;
x_15 = x_46;
x_16 = x_5;
x_17 = x_6;
x_18 = x_44;
goto block_37;
}
else
{
uint8_t x_47; 
lean_dec(x_12);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_3);
lean_dec(x_2);
x_47 = !lean_is_exclusive(x_42);
if (x_47 == 0)
{
return x_42;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; 
x_48 = lean_ctor_get(x_42, 0);
x_49 = lean_ctor_get(x_42, 1);
lean_inc(x_49);
lean_inc(x_48);
lean_dec(x_42);
x_50 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_50, 0, x_48);
lean_ctor_set(x_50, 1, x_49);
return x_50;
}
}
}
}
block_37:
{
lean_object* x_19; 
x_19 = l_Lean_IR_ToIR_lowerCode(x_2, x_15, x_16, x_17, x_18);
if (lean_obj_tag(x_19) == 0)
{
uint8_t x_20; 
x_20 = !lean_is_exclusive(x_19);
if (x_20 == 0)
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_19, 0);
x_22 = !lean_is_exclusive(x_21);
if (x_22 == 0)
{
lean_object* x_23; lean_object* x_24; 
x_23 = lean_ctor_get(x_21, 0);
x_24 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_24, 0, x_12);
lean_ctor_set(x_24, 1, x_14);
lean_ctor_set(x_24, 2, x_3);
lean_ctor_set(x_24, 3, x_23);
lean_ctor_set(x_21, 0, x_24);
return x_19;
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_25 = lean_ctor_get(x_21, 0);
x_26 = lean_ctor_get(x_21, 1);
lean_inc(x_26);
lean_inc(x_25);
lean_dec(x_21);
x_27 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_27, 0, x_12);
lean_ctor_set(x_27, 1, x_14);
lean_ctor_set(x_27, 2, x_3);
lean_ctor_set(x_27, 3, x_25);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_26);
lean_ctor_set(x_19, 0, x_28);
return x_19;
}
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_29 = lean_ctor_get(x_19, 0);
x_30 = lean_ctor_get(x_19, 1);
lean_inc(x_30);
lean_inc(x_29);
lean_dec(x_19);
x_31 = lean_ctor_get(x_29, 0);
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
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_12);
lean_ctor_set(x_34, 1, x_14);
lean_ctor_set(x_34, 2, x_3);
lean_ctor_set(x_34, 3, x_31);
if (lean_is_scalar(x_33)) {
 x_35 = lean_alloc_ctor(0, 2, 0);
} else {
 x_35 = x_33;
}
lean_ctor_set(x_35, 0, x_34);
lean_ctor_set(x_35, 1, x_32);
x_36 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_36, 0, x_35);
lean_ctor_set(x_36, 1, x_30);
return x_36;
}
}
else
{
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_3);
return x_19;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__2(lean_object* x_1) {
_start:
{
lean_object* x_2; uint8_t x_3; 
x_2 = lean_box(0);
x_3 = lean_unbox(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_9 = lean_ctor_get(x_1, 0);
lean_inc(x_9);
x_10 = l_Lean_IR_ToIR_bindVar___redArg(x_9, x_5, x_8);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = l_Lean_IR_ToIR_newVar___redArg(x_14, x_12);
lean_dec(x_14);
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
lean_dec(x_15);
x_18 = lean_ctor_get(x_16, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_16, 1);
lean_inc(x_19);
if (lean_is_exclusive(x_16)) {
 lean_ctor_release(x_16, 0);
 lean_ctor_release(x_16, 1);
 x_20 = x_16;
} else {
 lean_dec_ref(x_16);
 x_20 = lean_box(0);
}
switch (lean_obj_tag(x_3)) {
case 0:
{
lean_object* x_54; 
lean_dec(x_1);
x_54 = lean_box(7);
x_21 = x_54;
x_22 = x_19;
x_23 = x_6;
x_24 = x_7;
x_25 = x_17;
goto block_53;
}
case 3:
{
lean_object* x_55; 
lean_dec(x_1);
x_55 = lean_box(7);
x_21 = x_55;
x_22 = x_19;
x_23 = x_6;
x_24 = x_7;
x_25 = x_17;
goto block_53;
}
case 7:
{
lean_object* x_56; 
lean_dec(x_1);
x_56 = lean_box(7);
x_21 = x_56;
x_22 = x_19;
x_23 = x_6;
x_24 = x_7;
x_25 = x_17;
goto block_53;
}
default: 
{
lean_object* x_57; lean_object* x_58; 
x_57 = lean_ctor_get(x_1, 2);
lean_inc(x_57);
lean_dec(x_1);
lean_inc(x_7);
lean_inc(x_6);
x_58 = l_Lean_IR_ToIR_lowerType(x_57, x_19, x_6, x_7, x_17);
if (lean_obj_tag(x_58) == 0)
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; 
x_59 = lean_ctor_get(x_58, 0);
lean_inc(x_59);
x_60 = lean_ctor_get(x_58, 1);
lean_inc(x_60);
lean_dec(x_58);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
lean_dec(x_59);
x_21 = x_61;
x_22 = x_62;
x_23 = x_6;
x_24 = x_7;
x_25 = x_60;
goto block_53;
}
else
{
uint8_t x_63; 
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_63 = !lean_is_exclusive(x_58);
if (x_63 == 0)
{
return x_58;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
x_64 = lean_ctor_get(x_58, 0);
x_65 = lean_ctor_get(x_58, 1);
lean_inc(x_65);
lean_inc(x_64);
lean_dec(x_58);
x_66 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_66, 0, x_64);
lean_ctor_set(x_66, 1, x_65);
return x_66;
}
}
}
}
block_53:
{
lean_object* x_26; 
x_26 = l_Lean_IR_ToIR_lowerCode(x_2, x_22, x_23, x_24, x_25);
if (lean_obj_tag(x_26) == 0)
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_26);
if (x_27 == 0)
{
lean_object* x_28; uint8_t x_29; 
x_28 = lean_ctor_get(x_26, 0);
x_29 = !lean_is_exclusive(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_ctor_get(x_28, 0);
x_31 = lean_box(7);
lean_inc(x_18);
if (lean_is_scalar(x_20)) {
 x_32 = lean_alloc_ctor(8, 2, 0);
} else {
 x_32 = x_20;
 lean_ctor_set_tag(x_32, 8);
}
lean_ctor_set(x_32, 0, x_18);
lean_ctor_set(x_32, 1, x_4);
x_33 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_33, 0, x_13);
lean_ctor_set(x_33, 1, x_21);
lean_ctor_set(x_33, 2, x_32);
lean_ctor_set(x_33, 3, x_30);
x_34 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_34, 0, x_18);
lean_ctor_set(x_34, 1, x_31);
lean_ctor_set(x_34, 2, x_3);
lean_ctor_set(x_34, 3, x_33);
lean_ctor_set(x_28, 0, x_34);
return x_26;
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_35 = lean_ctor_get(x_28, 0);
x_36 = lean_ctor_get(x_28, 1);
lean_inc(x_36);
lean_inc(x_35);
lean_dec(x_28);
x_37 = lean_box(7);
lean_inc(x_18);
if (lean_is_scalar(x_20)) {
 x_38 = lean_alloc_ctor(8, 2, 0);
} else {
 x_38 = x_20;
 lean_ctor_set_tag(x_38, 8);
}
lean_ctor_set(x_38, 0, x_18);
lean_ctor_set(x_38, 1, x_4);
x_39 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_39, 0, x_13);
lean_ctor_set(x_39, 1, x_21);
lean_ctor_set(x_39, 2, x_38);
lean_ctor_set(x_39, 3, x_35);
x_40 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_40, 0, x_18);
lean_ctor_set(x_40, 1, x_37);
lean_ctor_set(x_40, 2, x_3);
lean_ctor_set(x_40, 3, x_39);
x_41 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_41, 0, x_40);
lean_ctor_set(x_41, 1, x_36);
lean_ctor_set(x_26, 0, x_41);
return x_26;
}
}
else
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_42 = lean_ctor_get(x_26, 0);
x_43 = lean_ctor_get(x_26, 1);
lean_inc(x_43);
lean_inc(x_42);
lean_dec(x_26);
x_44 = lean_ctor_get(x_42, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_42, 1);
lean_inc(x_45);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 lean_ctor_release(x_42, 1);
 x_46 = x_42;
} else {
 lean_dec_ref(x_42);
 x_46 = lean_box(0);
}
x_47 = lean_box(7);
lean_inc(x_18);
if (lean_is_scalar(x_20)) {
 x_48 = lean_alloc_ctor(8, 2, 0);
} else {
 x_48 = x_20;
 lean_ctor_set_tag(x_48, 8);
}
lean_ctor_set(x_48, 0, x_18);
lean_ctor_set(x_48, 1, x_4);
x_49 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_49, 0, x_13);
lean_ctor_set(x_49, 1, x_21);
lean_ctor_set(x_49, 2, x_48);
lean_ctor_set(x_49, 3, x_44);
x_50 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_50, 0, x_18);
lean_ctor_set(x_50, 1, x_47);
lean_ctor_set(x_50, 2, x_3);
lean_ctor_set(x_50, 3, x_49);
if (lean_is_scalar(x_46)) {
 x_51 = lean_alloc_ctor(0, 2, 0);
} else {
 x_51 = x_46;
}
lean_ctor_set(x_51, 0, x_50);
lean_ctor_set(x_51, 1, x_45);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_51);
lean_ctor_set(x_52, 1, x_43);
return x_52;
}
}
else
{
lean_dec(x_21);
lean_dec(x_20);
lean_dec(x_18);
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
return x_26;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; 
lean_inc(x_3);
x_9 = l_Lean_Compiler_LCNF_getMonoDecl_x3f___redArg(x_3, x_7, x_8);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
if (lean_obj_tag(x_10) == 0)
{
uint8_t x_11; 
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_11 = !lean_is_exclusive(x_9);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; 
x_12 = lean_ctor_get(x_9, 0);
lean_dec(x_12);
x_13 = lean_box(0);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_5);
lean_ctor_set(x_9, 0, x_14);
return x_9;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
x_15 = lean_ctor_get(x_9, 1);
lean_inc(x_15);
lean_dec(x_9);
x_16 = lean_box(0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_16);
lean_ctor_set(x_17, 1, x_5);
x_18 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_18, 0, x_17);
lean_ctor_set(x_18, 1, x_15);
return x_18;
}
}
else
{
lean_object* x_19; uint8_t x_20; 
x_19 = lean_ctor_get(x_9, 1);
lean_inc(x_19);
lean_dec(x_9);
x_20 = !lean_is_exclusive(x_10);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; 
x_21 = lean_ctor_get(x_10, 0);
x_22 = lean_array_get_size(x_4);
x_23 = lean_ctor_get(x_21, 3);
lean_inc(x_23);
lean_dec(x_21);
x_24 = lean_array_get_size(x_23);
lean_dec(x_23);
x_25 = lean_nat_dec_lt(x_22, x_24);
if (x_25 == 0)
{
uint8_t x_26; 
x_26 = lean_nat_dec_eq(x_22, x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
lean_dec(x_2);
x_27 = lean_unsigned_to_nat(0u);
lean_inc(x_24);
x_28 = l_Array_extract(lean_box(0), x_4, x_27, x_24);
x_29 = l_Array_extract(lean_box(0), x_4, x_24, x_22);
lean_dec(x_4);
x_30 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_30, 0, x_3);
lean_ctor_set(x_30, 1, x_28);
x_31 = lean_apply_6(x_1, x_30, x_29, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_31) == 0)
{
uint8_t x_32; 
x_32 = !lean_is_exclusive(x_31);
if (x_32 == 0)
{
lean_object* x_33; uint8_t x_34; 
x_33 = lean_ctor_get(x_31, 0);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; 
x_35 = lean_ctor_get(x_33, 0);
lean_ctor_set(x_10, 0, x_35);
lean_ctor_set(x_33, 0, x_10);
return x_31;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_33, 0);
x_37 = lean_ctor_get(x_33, 1);
lean_inc(x_37);
lean_inc(x_36);
lean_dec(x_33);
lean_ctor_set(x_10, 0, x_36);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_10);
lean_ctor_set(x_38, 1, x_37);
lean_ctor_set(x_31, 0, x_38);
return x_31;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_39 = lean_ctor_get(x_31, 0);
x_40 = lean_ctor_get(x_31, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_31);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_41);
if (lean_is_scalar(x_43)) {
 x_44 = lean_alloc_ctor(0, 2, 0);
} else {
 x_44 = x_43;
}
lean_ctor_set(x_44, 0, x_10);
lean_ctor_set(x_44, 1, x_42);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_44);
lean_ctor_set(x_45, 1, x_40);
return x_45;
}
}
else
{
uint8_t x_46; 
lean_free_object(x_10);
x_46 = !lean_is_exclusive(x_31);
if (x_46 == 0)
{
return x_31;
}
else
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; 
x_47 = lean_ctor_get(x_31, 0);
x_48 = lean_ctor_get(x_31, 1);
lean_inc(x_48);
lean_inc(x_47);
lean_dec(x_31);
x_49 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_49, 0, x_47);
lean_ctor_set(x_49, 1, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_50 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_50, 0, x_3);
lean_ctor_set(x_50, 1, x_4);
x_51 = lean_apply_5(x_2, x_50, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_53, 0);
lean_ctor_set(x_10, 0, x_55);
lean_ctor_set(x_53, 0, x_10);
return x_51;
}
else
{
lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_56 = lean_ctor_get(x_53, 0);
x_57 = lean_ctor_get(x_53, 1);
lean_inc(x_57);
lean_inc(x_56);
lean_dec(x_53);
lean_ctor_set(x_10, 0, x_56);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_10);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_51, 0, x_58);
return x_51;
}
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
x_59 = lean_ctor_get(x_51, 0);
x_60 = lean_ctor_get(x_51, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_51);
x_61 = lean_ctor_get(x_59, 0);
lean_inc(x_61);
x_62 = lean_ctor_get(x_59, 1);
lean_inc(x_62);
if (lean_is_exclusive(x_59)) {
 lean_ctor_release(x_59, 0);
 lean_ctor_release(x_59, 1);
 x_63 = x_59;
} else {
 lean_dec_ref(x_59);
 x_63 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_61);
if (lean_is_scalar(x_63)) {
 x_64 = lean_alloc_ctor(0, 2, 0);
} else {
 x_64 = x_63;
}
lean_ctor_set(x_64, 0, x_10);
lean_ctor_set(x_64, 1, x_62);
x_65 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_60);
return x_65;
}
}
else
{
uint8_t x_66; 
lean_free_object(x_10);
x_66 = !lean_is_exclusive(x_51);
if (x_66 == 0)
{
return x_51;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
x_67 = lean_ctor_get(x_51, 0);
x_68 = lean_ctor_get(x_51, 1);
lean_inc(x_68);
lean_inc(x_67);
lean_dec(x_51);
x_69 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_69, 0, x_67);
lean_ctor_set(x_69, 1, x_68);
return x_69;
}
}
}
}
else
{
lean_object* x_70; lean_object* x_71; 
lean_dec(x_24);
lean_dec(x_22);
lean_dec(x_1);
x_70 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_70, 0, x_3);
lean_ctor_set(x_70, 1, x_4);
x_71 = lean_apply_5(x_2, x_70, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_71) == 0)
{
uint8_t x_72; 
x_72 = !lean_is_exclusive(x_71);
if (x_72 == 0)
{
lean_object* x_73; uint8_t x_74; 
x_73 = lean_ctor_get(x_71, 0);
x_74 = !lean_is_exclusive(x_73);
if (x_74 == 0)
{
lean_object* x_75; 
x_75 = lean_ctor_get(x_73, 0);
lean_ctor_set(x_10, 0, x_75);
lean_ctor_set(x_73, 0, x_10);
return x_71;
}
else
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_76 = lean_ctor_get(x_73, 0);
x_77 = lean_ctor_get(x_73, 1);
lean_inc(x_77);
lean_inc(x_76);
lean_dec(x_73);
lean_ctor_set(x_10, 0, x_76);
x_78 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_78, 0, x_10);
lean_ctor_set(x_78, 1, x_77);
lean_ctor_set(x_71, 0, x_78);
return x_71;
}
}
else
{
lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; 
x_79 = lean_ctor_get(x_71, 0);
x_80 = lean_ctor_get(x_71, 1);
lean_inc(x_80);
lean_inc(x_79);
lean_dec(x_71);
x_81 = lean_ctor_get(x_79, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_79, 1);
lean_inc(x_82);
if (lean_is_exclusive(x_79)) {
 lean_ctor_release(x_79, 0);
 lean_ctor_release(x_79, 1);
 x_83 = x_79;
} else {
 lean_dec_ref(x_79);
 x_83 = lean_box(0);
}
lean_ctor_set(x_10, 0, x_81);
if (lean_is_scalar(x_83)) {
 x_84 = lean_alloc_ctor(0, 2, 0);
} else {
 x_84 = x_83;
}
lean_ctor_set(x_84, 0, x_10);
lean_ctor_set(x_84, 1, x_82);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_84);
lean_ctor_set(x_85, 1, x_80);
return x_85;
}
}
else
{
uint8_t x_86; 
lean_free_object(x_10);
x_86 = !lean_is_exclusive(x_71);
if (x_86 == 0)
{
return x_71;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; 
x_87 = lean_ctor_get(x_71, 0);
x_88 = lean_ctor_get(x_71, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_71);
x_89 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
return x_89;
}
}
}
}
else
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; 
x_90 = lean_ctor_get(x_10, 0);
lean_inc(x_90);
lean_dec(x_10);
x_91 = lean_array_get_size(x_4);
x_92 = lean_ctor_get(x_90, 3);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_array_get_size(x_92);
lean_dec(x_92);
x_94 = lean_nat_dec_lt(x_91, x_93);
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = lean_nat_dec_eq(x_91, x_93);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
lean_dec(x_2);
x_96 = lean_unsigned_to_nat(0u);
lean_inc(x_93);
x_97 = l_Array_extract(lean_box(0), x_4, x_96, x_93);
x_98 = l_Array_extract(lean_box(0), x_4, x_93, x_91);
lean_dec(x_4);
x_99 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_99, 0, x_3);
lean_ctor_set(x_99, 1, x_97);
x_100 = lean_apply_6(x_1, x_99, x_98, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_100) == 0)
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
x_101 = lean_ctor_get(x_100, 0);
lean_inc(x_101);
x_102 = lean_ctor_get(x_100, 1);
lean_inc(x_102);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_103 = x_100;
} else {
 lean_dec_ref(x_100);
 x_103 = lean_box(0);
}
x_104 = lean_ctor_get(x_101, 0);
lean_inc(x_104);
x_105 = lean_ctor_get(x_101, 1);
lean_inc(x_105);
if (lean_is_exclusive(x_101)) {
 lean_ctor_release(x_101, 0);
 lean_ctor_release(x_101, 1);
 x_106 = x_101;
} else {
 lean_dec_ref(x_101);
 x_106 = lean_box(0);
}
x_107 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_107, 0, x_104);
if (lean_is_scalar(x_106)) {
 x_108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_108 = x_106;
}
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_108, 1, x_105);
if (lean_is_scalar(x_103)) {
 x_109 = lean_alloc_ctor(0, 2, 0);
} else {
 x_109 = x_103;
}
lean_ctor_set(x_109, 0, x_108);
lean_ctor_set(x_109, 1, x_102);
return x_109;
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; 
x_110 = lean_ctor_get(x_100, 0);
lean_inc(x_110);
x_111 = lean_ctor_get(x_100, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_100)) {
 lean_ctor_release(x_100, 0);
 lean_ctor_release(x_100, 1);
 x_112 = x_100;
} else {
 lean_dec_ref(x_100);
 x_112 = lean_box(0);
}
if (lean_is_scalar(x_112)) {
 x_113 = lean_alloc_ctor(1, 2, 0);
} else {
 x_113 = x_112;
}
lean_ctor_set(x_113, 0, x_110);
lean_ctor_set(x_113, 1, x_111);
return x_113;
}
}
else
{
lean_object* x_114; lean_object* x_115; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_1);
x_114 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_114, 0, x_3);
lean_ctor_set(x_114, 1, x_4);
x_115 = lean_apply_5(x_2, x_114, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_115) == 0)
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; 
x_116 = lean_ctor_get(x_115, 0);
lean_inc(x_116);
x_117 = lean_ctor_get(x_115, 1);
lean_inc(x_117);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_118 = x_115;
} else {
 lean_dec_ref(x_115);
 x_118 = lean_box(0);
}
x_119 = lean_ctor_get(x_116, 0);
lean_inc(x_119);
x_120 = lean_ctor_get(x_116, 1);
lean_inc(x_120);
if (lean_is_exclusive(x_116)) {
 lean_ctor_release(x_116, 0);
 lean_ctor_release(x_116, 1);
 x_121 = x_116;
} else {
 lean_dec_ref(x_116);
 x_121 = lean_box(0);
}
x_122 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_122, 0, x_119);
if (lean_is_scalar(x_121)) {
 x_123 = lean_alloc_ctor(0, 2, 0);
} else {
 x_123 = x_121;
}
lean_ctor_set(x_123, 0, x_122);
lean_ctor_set(x_123, 1, x_120);
if (lean_is_scalar(x_118)) {
 x_124 = lean_alloc_ctor(0, 2, 0);
} else {
 x_124 = x_118;
}
lean_ctor_set(x_124, 0, x_123);
lean_ctor_set(x_124, 1, x_117);
return x_124;
}
else
{
lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; 
x_125 = lean_ctor_get(x_115, 0);
lean_inc(x_125);
x_126 = lean_ctor_get(x_115, 1);
lean_inc(x_126);
if (lean_is_exclusive(x_115)) {
 lean_ctor_release(x_115, 0);
 lean_ctor_release(x_115, 1);
 x_127 = x_115;
} else {
 lean_dec_ref(x_115);
 x_127 = lean_box(0);
}
if (lean_is_scalar(x_127)) {
 x_128 = lean_alloc_ctor(1, 2, 0);
} else {
 x_128 = x_127;
}
lean_ctor_set(x_128, 0, x_125);
lean_ctor_set(x_128, 1, x_126);
return x_128;
}
}
}
else
{
lean_object* x_129; lean_object* x_130; 
lean_dec(x_93);
lean_dec(x_91);
lean_dec(x_1);
x_129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_129, 0, x_3);
lean_ctor_set(x_129, 1, x_4);
x_130 = lean_apply_5(x_2, x_129, x_5, x_6, x_7, x_19);
if (lean_obj_tag(x_130) == 0)
{
lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
x_131 = lean_ctor_get(x_130, 0);
lean_inc(x_131);
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
x_134 = lean_ctor_get(x_131, 0);
lean_inc(x_134);
x_135 = lean_ctor_get(x_131, 1);
lean_inc(x_135);
if (lean_is_exclusive(x_131)) {
 lean_ctor_release(x_131, 0);
 lean_ctor_release(x_131, 1);
 x_136 = x_131;
} else {
 lean_dec_ref(x_131);
 x_136 = lean_box(0);
}
x_137 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_137, 0, x_134);
if (lean_is_scalar(x_136)) {
 x_138 = lean_alloc_ctor(0, 2, 0);
} else {
 x_138 = x_136;
}
lean_ctor_set(x_138, 0, x_137);
lean_ctor_set(x_138, 1, x_135);
if (lean_is_scalar(x_133)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_133;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_132);
return x_139;
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; 
x_140 = lean_ctor_get(x_130, 0);
lean_inc(x_140);
x_141 = lean_ctor_get(x_130, 1);
lean_inc(x_141);
if (lean_is_exclusive(x_130)) {
 lean_ctor_release(x_130, 0);
 lean_ctor_release(x_130, 1);
 x_142 = x_130;
} else {
 lean_dec_ref(x_130);
 x_142 = lean_box(0);
}
if (lean_is_scalar(x_142)) {
 x_143 = lean_alloc_ctor(1, 2, 0);
} else {
 x_143 = x_142;
}
lean_ctor_set(x_143, 0, x_140);
lean_ctor_set(x_143, 1, x_141);
return x_143;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_1, 0);
lean_inc(x_8);
lean_dec(x_1);
x_9 = l_Lean_IR_ToIR_bindVarToVarId___redArg(x_8, x_3, x_4, x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = l_Lean_IR_ToIR_lowerCode(x_2, x_12, x_5, x_6, x_11);
return x_13;
}
}
LEAN_EXPORT uint8_t l_Lean_IR_ToIR_lowerLet___lam__6(uint8_t x_1, lean_object* x_2) {
_start:
{
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; size_t x_23; lean_object* x_24; size_t x_25; lean_object* x_26; 
x_23 = lean_array_size(x_12);
x_24 = lean_unsigned_to_nat(0u);
x_25 = lean_usize_of_nat(x_24);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_12);
x_26 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_23, x_25, x_12, x_13, x_14, x_15, x_16);
if (lean_obj_tag(x_26) == 0)
{
lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_27 = lean_ctor_get(x_26, 0);
lean_inc(x_27);
x_28 = lean_ctor_get(x_26, 1);
lean_inc(x_28);
lean_dec(x_26);
x_29 = !lean_is_exclusive(x_27);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_30 = lean_ctor_get(x_27, 0);
x_31 = lean_ctor_get(x_27, 1);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_32 = lean_apply_6(x_1, x_10, x_30, x_31, x_14, x_15, x_28);
if (lean_obj_tag(x_32) == 0)
{
lean_object* x_33; lean_object* x_34; 
x_33 = lean_ctor_get(x_32, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; uint8_t x_36; 
x_35 = lean_ctor_get(x_32, 1);
lean_inc(x_35);
lean_dec(x_32);
x_36 = !lean_is_exclusive(x_33);
if (x_36 == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; uint8_t x_40; 
x_37 = lean_ctor_get(x_33, 1);
x_38 = lean_ctor_get(x_33, 0);
lean_dec(x_38);
x_39 = lean_st_ref_get(x_15, x_35);
x_40 = !lean_is_exclusive(x_39);
if (x_40 == 0)
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; uint8_t x_45; lean_object* x_46; 
x_41 = lean_ctor_get(x_39, 0);
x_42 = lean_ctor_get(x_39, 1);
x_43 = lean_ctor_get(x_41, 0);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_box(0);
x_45 = lean_unbox(x_44);
lean_inc(x_10);
lean_inc(x_43);
x_46 = l_Lean_Environment_find_x3f(x_43, x_10, x_45);
if (lean_obj_tag(x_46) == 0)
{
lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; 
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_47 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_48 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_49 = lean_unsigned_to_nat(338u);
x_50 = lean_unsigned_to_nat(16u);
x_51 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
x_52 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_47, x_48, x_49, x_50, x_51);
lean_dec(x_51);
lean_dec(x_48);
lean_dec(x_47);
x_53 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_52, x_37, x_14, x_15, x_42);
return x_53;
}
else
{
uint8_t x_54; 
x_54 = !lean_is_exclusive(x_46);
if (x_54 == 0)
{
lean_object* x_55; 
x_55 = lean_ctor_get(x_46, 0);
switch (lean_obj_tag(x_55)) {
case 0:
{
uint8_t x_56; 
lean_dec(x_43);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_57 = lean_ctor_get(x_55, 0);
lean_dec(x_57);
x_58 = lean_mk_string_unchecked("Quot", 4, 4);
x_59 = lean_mk_string_unchecked("lcInv", 5, 5);
x_60 = l_Lean_Name_mkStr2(x_58, x_59);
x_61 = lean_name_eq(x_10, x_60);
lean_dec(x_60);
if (x_61 == 0)
{
lean_object* x_62; lean_object* x_63; uint8_t x_64; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_62 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
x_63 = l_Lean_Name_mkStr1(x_62);
x_64 = lean_name_eq(x_10, x_63);
lean_dec(x_63);
if (x_64 == 0)
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; 
lean_free_object(x_39);
lean_free_object(x_33);
lean_inc(x_10);
x_65 = l_Lean_IR_ToIR_findDecl___redArg(x_10, x_37, x_15, x_42);
x_66 = lean_ctor_get(x_65, 0);
lean_inc(x_66);
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
if (lean_obj_tag(x_67) == 0)
{
uint8_t x_68; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_69 = lean_ctor_get(x_66, 1);
lean_dec(x_69);
x_70 = lean_ctor_get(x_66, 0);
lean_dec(x_70);
x_71 = !lean_is_exclusive(x_65);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; uint8_t x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
x_72 = lean_ctor_get(x_65, 1);
x_73 = lean_ctor_get(x_65, 0);
lean_dec(x_73);
x_74 = lean_box(x_64);
x_75 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_75, 0, x_74);
x_76 = lean_mk_string_unchecked("axiom '", 7, 7);
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_76);
x_77 = lean_box(1);
x_78 = lean_unbox(x_77);
x_79 = l_Lean_Name_toString(x_10, x_78, x_75);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_79);
lean_ctor_set_tag(x_66, 5);
lean_ctor_set(x_66, 1, x_46);
lean_ctor_set(x_66, 0, x_55);
x_80 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_81 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set_tag(x_65, 5);
lean_ctor_set(x_65, 1, x_81);
x_82 = l_Lean_MessageData_ofFormat(x_65);
x_83 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_82, x_14, x_15, x_72);
lean_dec(x_15);
lean_dec(x_14);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_84 = lean_ctor_get(x_65, 1);
lean_inc(x_84);
lean_dec(x_65);
x_85 = lean_box(x_64);
x_86 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_86, 0, x_85);
x_87 = lean_mk_string_unchecked("axiom '", 7, 7);
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_87);
x_88 = lean_box(1);
x_89 = lean_unbox(x_88);
x_90 = l_Lean_Name_toString(x_10, x_89, x_86);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_90);
lean_ctor_set_tag(x_66, 5);
lean_ctor_set(x_66, 1, x_46);
lean_ctor_set(x_66, 0, x_55);
x_91 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_92 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_92, 0, x_91);
x_93 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_93, 0, x_66);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_MessageData_ofFormat(x_93);
x_95 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_94, x_14, x_15, x_84);
lean_dec(x_15);
lean_dec(x_14);
return x_95;
}
}
else
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; uint8_t x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; 
lean_dec(x_66);
x_96 = lean_ctor_get(x_65, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_97 = x_65;
} else {
 lean_dec_ref(x_65);
 x_97 = lean_box(0);
}
x_98 = lean_box(x_64);
x_99 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_99, 0, x_98);
x_100 = lean_mk_string_unchecked("axiom '", 7, 7);
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_100);
x_101 = lean_box(1);
x_102 = lean_unbox(x_101);
x_103 = l_Lean_Name_toString(x_10, x_102, x_99);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_103);
x_104 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_104, 0, x_55);
lean_ctor_set(x_104, 1, x_46);
x_105 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_106 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_106, 0, x_105);
if (lean_is_scalar(x_97)) {
 x_107 = lean_alloc_ctor(5, 2, 0);
} else {
 x_107 = x_97;
 lean_ctor_set_tag(x_107, 5);
}
lean_ctor_set(x_107, 0, x_104);
lean_ctor_set(x_107, 1, x_106);
x_108 = l_Lean_MessageData_ofFormat(x_107);
x_109 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_108, x_14, x_15, x_96);
lean_dec(x_15);
lean_dec(x_14);
return x_109;
}
}
else
{
lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_128; 
lean_free_object(x_55);
lean_free_object(x_46);
x_110 = lean_ctor_get(x_65, 1);
lean_inc(x_110);
lean_dec(x_65);
x_111 = lean_ctor_get(x_66, 1);
lean_inc(x_111);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 lean_ctor_release(x_66, 1);
 x_112 = x_66;
} else {
 lean_dec_ref(x_66);
 x_112 = lean_box(0);
}
x_113 = lean_ctor_get(x_67, 0);
lean_inc(x_113);
lean_dec(x_67);
x_114 = lean_array_get_size(x_30);
x_128 = lean_ctor_get(x_113, 1);
lean_inc(x_128);
lean_dec(x_113);
x_115 = x_128;
goto block_127;
block_127:
{
lean_object* x_116; uint8_t x_117; 
x_116 = lean_array_get_size(x_115);
lean_dec(x_115);
x_117 = lean_nat_dec_lt(x_114, x_116);
if (x_117 == 0)
{
uint8_t x_118; 
x_118 = lean_nat_dec_eq(x_114, x_116);
if (x_118 == 0)
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; 
lean_dec(x_3);
lean_inc(x_116);
x_119 = l_Array_extract(lean_box(0), x_30, x_24, x_116);
x_120 = l_Array_extract(lean_box(0), x_30, x_116, x_114);
lean_dec(x_30);
if (lean_is_scalar(x_112)) {
 x_121 = lean_alloc_ctor(6, 2, 0);
} else {
 x_121 = x_112;
 lean_ctor_set_tag(x_121, 6);
}
lean_ctor_set(x_121, 0, x_10);
lean_ctor_set(x_121, 1, x_119);
x_122 = lean_apply_6(x_2, x_121, x_120, x_111, x_14, x_15, x_110);
return x_122;
}
else
{
lean_object* x_123; lean_object* x_124; 
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_2);
if (lean_is_scalar(x_112)) {
 x_123 = lean_alloc_ctor(6, 2, 0);
} else {
 x_123 = x_112;
 lean_ctor_set_tag(x_123, 6);
}
lean_ctor_set(x_123, 0, x_10);
lean_ctor_set(x_123, 1, x_30);
x_124 = lean_apply_5(x_3, x_123, x_111, x_14, x_15, x_110);
return x_124;
}
}
else
{
lean_object* x_125; lean_object* x_126; 
lean_dec(x_116);
lean_dec(x_114);
lean_dec(x_2);
if (lean_is_scalar(x_112)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_112;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_10);
lean_ctor_set(x_125, 1, x_30);
x_126 = lean_apply_5(x_3, x_125, x_111, x_14, x_15, x_110);
return x_126;
}
}
}
}
else
{
lean_object* x_129; 
lean_free_object(x_55);
lean_free_object(x_46);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_129 = lean_box(13);
lean_ctor_set(x_33, 0, x_129);
lean_ctor_set(x_39, 0, x_33);
return x_39;
}
}
else
{
lean_object* x_130; lean_object* x_131; 
lean_free_object(x_55);
lean_free_object(x_46);
lean_free_object(x_39);
lean_free_object(x_33);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_130 = lean_unsigned_to_nat(2u);
x_131 = lean_array_get(x_4, x_30, x_130);
lean_dec(x_30);
if (lean_obj_tag(x_131) == 0)
{
lean_object* x_132; lean_object* x_133; 
lean_dec(x_6);
x_132 = lean_ctor_get(x_131, 0);
lean_inc(x_132);
lean_dec(x_131);
x_133 = lean_apply_5(x_5, x_132, x_37, x_14, x_15, x_42);
return x_133;
}
else
{
lean_object* x_134; lean_object* x_135; 
lean_dec(x_5);
x_134 = lean_box(0);
x_135 = lean_apply_5(x_6, x_134, x_37, x_14, x_15, x_42);
return x_135;
}
}
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; uint8_t x_139; 
lean_dec(x_55);
x_136 = lean_mk_string_unchecked("Quot", 4, 4);
x_137 = lean_mk_string_unchecked("lcInv", 5, 5);
x_138 = l_Lean_Name_mkStr2(x_136, x_137);
x_139 = lean_name_eq(x_10, x_138);
lean_dec(x_138);
if (x_139 == 0)
{
lean_object* x_140; lean_object* x_141; uint8_t x_142; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_140 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
x_141 = l_Lean_Name_mkStr1(x_140);
x_142 = lean_name_eq(x_10, x_141);
lean_dec(x_141);
if (x_142 == 0)
{
lean_object* x_143; lean_object* x_144; lean_object* x_145; 
lean_free_object(x_39);
lean_free_object(x_33);
lean_inc(x_10);
x_143 = l_Lean_IR_ToIR_findDecl___redArg(x_10, x_37, x_15, x_42);
x_144 = lean_ctor_get(x_143, 0);
lean_inc(x_144);
x_145 = lean_ctor_get(x_144, 0);
lean_inc(x_145);
if (lean_obj_tag(x_145) == 0)
{
lean_object* x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_146 = x_144;
} else {
 lean_dec_ref(x_144);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_143, 1);
lean_inc(x_147);
if (lean_is_exclusive(x_143)) {
 lean_ctor_release(x_143, 0);
 lean_ctor_release(x_143, 1);
 x_148 = x_143;
} else {
 lean_dec_ref(x_143);
 x_148 = lean_box(0);
}
x_149 = lean_box(x_142);
x_150 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_150, 0, x_149);
x_151 = lean_mk_string_unchecked("axiom '", 7, 7);
x_152 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_152, 0, x_151);
x_153 = lean_box(1);
x_154 = lean_unbox(x_153);
x_155 = l_Lean_Name_toString(x_10, x_154, x_150);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_155);
if (lean_is_scalar(x_146)) {
 x_156 = lean_alloc_ctor(5, 2, 0);
} else {
 x_156 = x_146;
 lean_ctor_set_tag(x_156, 5);
}
lean_ctor_set(x_156, 0, x_152);
lean_ctor_set(x_156, 1, x_46);
x_157 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_158 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_158, 0, x_157);
if (lean_is_scalar(x_148)) {
 x_159 = lean_alloc_ctor(5, 2, 0);
} else {
 x_159 = x_148;
 lean_ctor_set_tag(x_159, 5);
}
lean_ctor_set(x_159, 0, x_156);
lean_ctor_set(x_159, 1, x_158);
x_160 = l_Lean_MessageData_ofFormat(x_159);
x_161 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_160, x_14, x_15, x_147);
lean_dec(x_15);
lean_dec(x_14);
return x_161;
}
else
{
lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_180; 
lean_free_object(x_46);
x_162 = lean_ctor_get(x_143, 1);
lean_inc(x_162);
lean_dec(x_143);
x_163 = lean_ctor_get(x_144, 1);
lean_inc(x_163);
if (lean_is_exclusive(x_144)) {
 lean_ctor_release(x_144, 0);
 lean_ctor_release(x_144, 1);
 x_164 = x_144;
} else {
 lean_dec_ref(x_144);
 x_164 = lean_box(0);
}
x_165 = lean_ctor_get(x_145, 0);
lean_inc(x_165);
lean_dec(x_145);
x_166 = lean_array_get_size(x_30);
x_180 = lean_ctor_get(x_165, 1);
lean_inc(x_180);
lean_dec(x_165);
x_167 = x_180;
goto block_179;
block_179:
{
lean_object* x_168; uint8_t x_169; 
x_168 = lean_array_get_size(x_167);
lean_dec(x_167);
x_169 = lean_nat_dec_lt(x_166, x_168);
if (x_169 == 0)
{
uint8_t x_170; 
x_170 = lean_nat_dec_eq(x_166, x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; 
lean_dec(x_3);
lean_inc(x_168);
x_171 = l_Array_extract(lean_box(0), x_30, x_24, x_168);
x_172 = l_Array_extract(lean_box(0), x_30, x_168, x_166);
lean_dec(x_30);
if (lean_is_scalar(x_164)) {
 x_173 = lean_alloc_ctor(6, 2, 0);
} else {
 x_173 = x_164;
 lean_ctor_set_tag(x_173, 6);
}
lean_ctor_set(x_173, 0, x_10);
lean_ctor_set(x_173, 1, x_171);
x_174 = lean_apply_6(x_2, x_173, x_172, x_163, x_14, x_15, x_162);
return x_174;
}
else
{
lean_object* x_175; lean_object* x_176; 
lean_dec(x_168);
lean_dec(x_166);
lean_dec(x_2);
if (lean_is_scalar(x_164)) {
 x_175 = lean_alloc_ctor(6, 2, 0);
} else {
 x_175 = x_164;
 lean_ctor_set_tag(x_175, 6);
}
lean_ctor_set(x_175, 0, x_10);
lean_ctor_set(x_175, 1, x_30);
x_176 = lean_apply_5(x_3, x_175, x_163, x_14, x_15, x_162);
return x_176;
}
}
else
{
lean_object* x_177; lean_object* x_178; 
lean_dec(x_168);
lean_dec(x_166);
lean_dec(x_2);
if (lean_is_scalar(x_164)) {
 x_177 = lean_alloc_ctor(7, 2, 0);
} else {
 x_177 = x_164;
 lean_ctor_set_tag(x_177, 7);
}
lean_ctor_set(x_177, 0, x_10);
lean_ctor_set(x_177, 1, x_30);
x_178 = lean_apply_5(x_3, x_177, x_163, x_14, x_15, x_162);
return x_178;
}
}
}
}
else
{
lean_object* x_181; 
lean_free_object(x_46);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_181 = lean_box(13);
lean_ctor_set(x_33, 0, x_181);
lean_ctor_set(x_39, 0, x_33);
return x_39;
}
}
else
{
lean_object* x_182; lean_object* x_183; 
lean_free_object(x_46);
lean_free_object(x_39);
lean_free_object(x_33);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_182 = lean_unsigned_to_nat(2u);
x_183 = lean_array_get(x_4, x_30, x_182);
lean_dec(x_30);
if (lean_obj_tag(x_183) == 0)
{
lean_object* x_184; lean_object* x_185; 
lean_dec(x_6);
x_184 = lean_ctor_get(x_183, 0);
lean_inc(x_184);
lean_dec(x_183);
x_185 = lean_apply_5(x_5, x_184, x_37, x_14, x_15, x_42);
return x_185;
}
else
{
lean_object* x_186; lean_object* x_187; 
lean_dec(x_5);
x_186 = lean_box(0);
x_187 = lean_apply_5(x_6, x_186, x_37, x_14, x_15, x_42);
return x_187;
}
}
}
}
case 2:
{
lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; 
lean_free_object(x_46);
lean_dec(x_55);
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_188 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_189 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_190 = lean_unsigned_to_nat(337u);
x_191 = lean_unsigned_to_nat(30u);
x_192 = lean_mk_string_unchecked("thm unsupported by code generator", 33, 33);
x_193 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_188, x_189, x_190, x_191, x_192);
lean_dec(x_192);
lean_dec(x_189);
lean_dec(x_188);
x_194 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_193, x_37, x_14, x_15, x_42);
return x_194;
}
case 4:
{
uint8_t x_195; 
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_195 = !lean_is_exclusive(x_55);
if (x_195 == 0)
{
lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; uint8_t x_200; 
x_196 = lean_ctor_get(x_55, 0);
lean_dec(x_196);
x_197 = lean_mk_string_unchecked("Quot", 4, 4);
x_198 = lean_mk_string_unchecked("mk", 2, 2);
x_199 = l_Lean_Name_mkStr2(x_197, x_198);
x_200 = lean_name_eq(x_10, x_199);
lean_dec(x_199);
if (x_200 == 0)
{
lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; uint8_t x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; 
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_201 = lean_box(x_200);
x_202 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_202, 0, x_201);
x_203 = lean_mk_string_unchecked("quot ", 5, 5);
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_203);
x_204 = lean_box(1);
x_205 = lean_unbox(x_204);
x_206 = l_Lean_Name_toString(x_10, x_205, x_202);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_206);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_46);
lean_ctor_set(x_27, 0, x_55);
x_207 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
x_208 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_208, 0, x_207);
x_209 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_209, 0, x_27);
lean_ctor_set(x_209, 1, x_208);
x_210 = l_Lean_MessageData_ofFormat(x_209);
x_211 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_210, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_211;
}
else
{
lean_object* x_212; lean_object* x_213; 
lean_free_object(x_55);
lean_free_object(x_46);
lean_free_object(x_27);
lean_dec(x_10);
x_212 = lean_unsigned_to_nat(2u);
x_213 = lean_array_get(x_4, x_30, x_212);
lean_dec(x_30);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; 
lean_dec(x_6);
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
lean_dec(x_213);
x_215 = lean_apply_5(x_5, x_214, x_37, x_14, x_15, x_42);
return x_215;
}
else
{
lean_object* x_216; lean_object* x_217; 
lean_dec(x_5);
x_216 = lean_box(0);
x_217 = lean_apply_5(x_6, x_216, x_37, x_14, x_15, x_42);
return x_217;
}
}
}
else
{
lean_object* x_218; lean_object* x_219; lean_object* x_220; uint8_t x_221; 
lean_dec(x_55);
x_218 = lean_mk_string_unchecked("Quot", 4, 4);
x_219 = lean_mk_string_unchecked("mk", 2, 2);
x_220 = l_Lean_Name_mkStr2(x_218, x_219);
x_221 = lean_name_eq(x_10, x_220);
lean_dec(x_220);
if (x_221 == 0)
{
lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; uint8_t x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; 
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_222 = lean_box(x_221);
x_223 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_223, 0, x_222);
x_224 = lean_mk_string_unchecked("quot ", 5, 5);
x_225 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = lean_box(1);
x_227 = lean_unbox(x_226);
x_228 = l_Lean_Name_toString(x_10, x_227, x_223);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_228);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_46);
lean_ctor_set(x_27, 0, x_225);
x_229 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
x_230 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_230, 0, x_229);
x_231 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_231, 0, x_27);
lean_ctor_set(x_231, 1, x_230);
x_232 = l_Lean_MessageData_ofFormat(x_231);
x_233 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_232, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_233;
}
else
{
lean_object* x_234; lean_object* x_235; 
lean_free_object(x_46);
lean_free_object(x_27);
lean_dec(x_10);
x_234 = lean_unsigned_to_nat(2u);
x_235 = lean_array_get(x_4, x_30, x_234);
lean_dec(x_30);
if (lean_obj_tag(x_235) == 0)
{
lean_object* x_236; lean_object* x_237; 
lean_dec(x_6);
x_236 = lean_ctor_get(x_235, 0);
lean_inc(x_236);
lean_dec(x_235);
x_237 = lean_apply_5(x_5, x_236, x_37, x_14, x_15, x_42);
return x_237;
}
else
{
lean_object* x_238; lean_object* x_239; 
lean_dec(x_5);
x_238 = lean_box(0);
x_239 = lean_apply_5(x_6, x_238, x_37, x_14, x_15, x_42);
return x_239;
}
}
}
}
case 5:
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; 
lean_free_object(x_46);
lean_dec(x_55);
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_240 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_241 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_242 = lean_unsigned_to_nat(336u);
x_243 = lean_unsigned_to_nat(33u);
x_244 = lean_mk_string_unchecked("induct unsupported by code generator", 36, 36);
x_245 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_240, x_241, x_242, x_243, x_244);
lean_dec(x_244);
lean_dec(x_241);
lean_dec(x_240);
x_246 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_245, x_37, x_14, x_15, x_42);
return x_246;
}
case 6:
{
lean_object* x_247; uint8_t x_248; 
lean_free_object(x_46);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_247 = lean_ctor_get(x_55, 0);
lean_inc(x_247);
lean_dec(x_55);
lean_inc(x_10);
x_248 = l_Lean_isExtern(x_43, x_10);
if (x_248 == 0)
{
lean_object* x_249; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
x_249 = l_Lean_IR_ToIR_getCtorInfo(x_10, x_37, x_14, x_15, x_42);
if (lean_obj_tag(x_249) == 0)
{
lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; uint8_t x_272; 
x_250 = lean_ctor_get(x_249, 0);
lean_inc(x_250);
x_251 = lean_ctor_get(x_250, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_249, 1);
lean_inc(x_252);
lean_dec(x_249);
x_253 = lean_ctor_get(x_250, 1);
lean_inc(x_253);
lean_dec(x_250);
x_254 = lean_ctor_get(x_251, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_251, 1);
lean_inc(x_255);
lean_dec(x_251);
x_256 = lean_ctor_get(x_247, 3);
lean_inc(x_256);
lean_dec(x_247);
x_257 = lean_array_get_size(x_12);
x_258 = l_Array_extract(lean_box(0), x_12, x_256, x_257);
lean_dec(x_12);
x_259 = lean_mk_empty_array_with_capacity(x_24);
x_260 = lean_array_get_size(x_255);
x_261 = lean_unsigned_to_nat(1u);
x_262 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_262, 0, x_24);
lean_ctor_set(x_262, 1, x_260);
lean_ctor_set(x_262, 2, x_261);
x_263 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_258, x_255, x_248, x_262, x_259, x_24, x_253, x_252);
lean_dec(x_262);
x_264 = lean_ctor_get(x_263, 0);
lean_inc(x_264);
x_265 = lean_ctor_get(x_263, 1);
lean_inc(x_265);
lean_dec(x_263);
x_266 = lean_ctor_get(x_264, 0);
lean_inc(x_266);
x_267 = lean_ctor_get(x_264, 1);
lean_inc(x_267);
lean_dec(x_264);
x_268 = lean_ctor_get(x_7, 0);
lean_inc(x_268);
lean_dec(x_7);
x_269 = l_Lean_IR_ToIR_bindVar___redArg(x_268, x_267, x_265);
x_270 = lean_ctor_get(x_269, 0);
lean_inc(x_270);
x_271 = lean_ctor_get(x_269, 1);
lean_inc(x_271);
lean_dec(x_269);
x_272 = !lean_is_exclusive(x_270);
if (x_272 == 0)
{
lean_object* x_273; lean_object* x_274; lean_object* x_275; 
x_273 = lean_ctor_get(x_270, 0);
x_274 = lean_ctor_get(x_270, 1);
lean_inc(x_273);
x_275 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_8, x_254, x_255, x_258, x_273, x_274, x_14, x_15, x_271);
lean_dec(x_258);
lean_dec(x_255);
if (lean_obj_tag(x_275) == 0)
{
uint8_t x_276; 
x_276 = !lean_is_exclusive(x_275);
if (x_276 == 0)
{
lean_object* x_277; uint8_t x_278; 
x_277 = lean_ctor_get(x_275, 0);
x_278 = !lean_is_exclusive(x_277);
if (x_278 == 0)
{
lean_object* x_279; lean_object* x_280; lean_object* x_281; 
x_279 = lean_ctor_get(x_277, 0);
x_280 = lean_box(7);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set(x_270, 0, x_254);
x_281 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_281, 0, x_273);
lean_ctor_set(x_281, 1, x_280);
lean_ctor_set(x_281, 2, x_270);
lean_ctor_set(x_281, 3, x_279);
lean_ctor_set(x_277, 0, x_281);
return x_275;
}
else
{
lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; 
x_282 = lean_ctor_get(x_277, 0);
x_283 = lean_ctor_get(x_277, 1);
lean_inc(x_283);
lean_inc(x_282);
lean_dec(x_277);
x_284 = lean_box(7);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set(x_270, 0, x_254);
x_285 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_285, 0, x_273);
lean_ctor_set(x_285, 1, x_284);
lean_ctor_set(x_285, 2, x_270);
lean_ctor_set(x_285, 3, x_282);
x_286 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
lean_ctor_set(x_275, 0, x_286);
return x_275;
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; 
x_287 = lean_ctor_get(x_275, 0);
x_288 = lean_ctor_get(x_275, 1);
lean_inc(x_288);
lean_inc(x_287);
lean_dec(x_275);
x_289 = lean_ctor_get(x_287, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_287, 1);
lean_inc(x_290);
if (lean_is_exclusive(x_287)) {
 lean_ctor_release(x_287, 0);
 lean_ctor_release(x_287, 1);
 x_291 = x_287;
} else {
 lean_dec_ref(x_287);
 x_291 = lean_box(0);
}
x_292 = lean_box(7);
lean_ctor_set(x_270, 1, x_266);
lean_ctor_set(x_270, 0, x_254);
x_293 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_293, 0, x_273);
lean_ctor_set(x_293, 1, x_292);
lean_ctor_set(x_293, 2, x_270);
lean_ctor_set(x_293, 3, x_289);
if (lean_is_scalar(x_291)) {
 x_294 = lean_alloc_ctor(0, 2, 0);
} else {
 x_294 = x_291;
}
lean_ctor_set(x_294, 0, x_293);
lean_ctor_set(x_294, 1, x_290);
x_295 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_295, 0, x_294);
lean_ctor_set(x_295, 1, x_288);
return x_295;
}
}
else
{
lean_free_object(x_270);
lean_dec(x_273);
lean_dec(x_266);
lean_dec(x_254);
return x_275;
}
}
else
{
lean_object* x_296; lean_object* x_297; lean_object* x_298; 
x_296 = lean_ctor_get(x_270, 0);
x_297 = lean_ctor_get(x_270, 1);
lean_inc(x_297);
lean_inc(x_296);
lean_dec(x_270);
lean_inc(x_296);
x_298 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_8, x_254, x_255, x_258, x_296, x_297, x_14, x_15, x_271);
lean_dec(x_258);
lean_dec(x_255);
if (lean_obj_tag(x_298) == 0)
{
lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; 
x_299 = lean_ctor_get(x_298, 0);
lean_inc(x_299);
x_300 = lean_ctor_get(x_298, 1);
lean_inc(x_300);
if (lean_is_exclusive(x_298)) {
 lean_ctor_release(x_298, 0);
 lean_ctor_release(x_298, 1);
 x_301 = x_298;
} else {
 lean_dec_ref(x_298);
 x_301 = lean_box(0);
}
x_302 = lean_ctor_get(x_299, 0);
lean_inc(x_302);
x_303 = lean_ctor_get(x_299, 1);
lean_inc(x_303);
if (lean_is_exclusive(x_299)) {
 lean_ctor_release(x_299, 0);
 lean_ctor_release(x_299, 1);
 x_304 = x_299;
} else {
 lean_dec_ref(x_299);
 x_304 = lean_box(0);
}
x_305 = lean_box(7);
x_306 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_306, 0, x_254);
lean_ctor_set(x_306, 1, x_266);
x_307 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_307, 0, x_296);
lean_ctor_set(x_307, 1, x_305);
lean_ctor_set(x_307, 2, x_306);
lean_ctor_set(x_307, 3, x_302);
if (lean_is_scalar(x_304)) {
 x_308 = lean_alloc_ctor(0, 2, 0);
} else {
 x_308 = x_304;
}
lean_ctor_set(x_308, 0, x_307);
lean_ctor_set(x_308, 1, x_303);
if (lean_is_scalar(x_301)) {
 x_309 = lean_alloc_ctor(0, 2, 0);
} else {
 x_309 = x_301;
}
lean_ctor_set(x_309, 0, x_308);
lean_ctor_set(x_309, 1, x_300);
return x_309;
}
else
{
lean_dec(x_296);
lean_dec(x_266);
lean_dec(x_254);
return x_298;
}
}
}
else
{
uint8_t x_310; 
lean_dec(x_247);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_310 = !lean_is_exclusive(x_249);
if (x_310 == 0)
{
return x_249;
}
else
{
lean_object* x_311; lean_object* x_312; lean_object* x_313; 
x_311 = lean_ctor_get(x_249, 0);
x_312 = lean_ctor_get(x_249, 1);
lean_inc(x_312);
lean_inc(x_311);
lean_dec(x_249);
x_313 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_313, 0, x_311);
lean_ctor_set(x_313, 1, x_312);
return x_313;
}
}
}
else
{
lean_object* x_314; 
lean_dec(x_247);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_314 = lean_apply_6(x_1, x_10, x_30, x_37, x_14, x_15, x_42);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_315, 0);
lean_inc(x_316);
if (lean_obj_tag(x_316) == 0)
{
lean_object* x_317; uint8_t x_318; 
x_317 = lean_ctor_get(x_314, 1);
lean_inc(x_317);
lean_dec(x_314);
x_318 = !lean_is_exclusive(x_315);
if (x_318 == 0)
{
lean_object* x_319; lean_object* x_320; lean_object* x_321; 
x_319 = lean_ctor_get(x_315, 1);
x_320 = lean_ctor_get(x_315, 0);
lean_dec(x_320);
lean_ctor_set_tag(x_315, 6);
lean_ctor_set(x_315, 1, x_30);
lean_ctor_set(x_315, 0, x_10);
x_321 = lean_apply_5(x_3, x_315, x_319, x_14, x_15, x_317);
return x_321;
}
else
{
lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_322 = lean_ctor_get(x_315, 1);
lean_inc(x_322);
lean_dec(x_315);
x_323 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_323, 0, x_10);
lean_ctor_set(x_323, 1, x_30);
x_324 = lean_apply_5(x_3, x_323, x_322, x_14, x_15, x_317);
return x_324;
}
}
else
{
lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_325 = lean_ctor_get(x_314, 1);
lean_inc(x_325);
lean_dec(x_314);
x_326 = lean_ctor_get(x_315, 1);
lean_inc(x_326);
lean_dec(x_315);
x_327 = lean_ctor_get(x_316, 0);
lean_inc(x_327);
lean_dec(x_316);
x_17 = x_327;
x_18 = x_326;
x_19 = x_325;
goto block_22;
}
}
else
{
uint8_t x_328; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_328 = !lean_is_exclusive(x_314);
if (x_328 == 0)
{
return x_314;
}
else
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; 
x_329 = lean_ctor_get(x_314, 0);
x_330 = lean_ctor_get(x_314, 1);
lean_inc(x_330);
lean_inc(x_329);
lean_dec(x_314);
x_331 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_331, 0, x_329);
lean_ctor_set(x_331, 1, x_330);
return x_331;
}
}
}
}
case 7:
{
uint8_t x_332; 
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_332 = !lean_is_exclusive(x_55);
if (x_332 == 0)
{
lean_object* x_333; lean_object* x_334; lean_object* x_335; uint8_t x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; 
x_333 = lean_ctor_get(x_55, 0);
lean_dec(x_333);
x_334 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
lean_ctor_set_tag(x_55, 3);
lean_ctor_set(x_55, 0, x_334);
x_335 = lean_box(1);
x_336 = lean_unbox(x_335);
x_337 = l_Lean_Name_toString(x_10, x_336, x_9);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_337);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_46);
lean_ctor_set(x_27, 0, x_55);
x_338 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_339 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_339, 0, x_338);
x_340 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_340, 0, x_27);
lean_ctor_set(x_340, 1, x_339);
x_341 = l_Lean_MessageData_ofFormat(x_340);
x_342 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_341, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_342;
}
else
{
lean_object* x_343; lean_object* x_344; lean_object* x_345; uint8_t x_346; lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; 
lean_dec(x_55);
x_343 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
x_344 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_344, 0, x_343);
x_345 = lean_box(1);
x_346 = lean_unbox(x_345);
x_347 = l_Lean_Name_toString(x_10, x_346, x_9);
lean_ctor_set_tag(x_46, 3);
lean_ctor_set(x_46, 0, x_347);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_46);
lean_ctor_set(x_27, 0, x_344);
x_348 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_349 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_349, 0, x_348);
x_350 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_350, 0, x_27);
lean_ctor_set(x_350, 1, x_349);
x_351 = l_Lean_MessageData_ofFormat(x_350);
x_352 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_351, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_352;
}
}
default: 
{
lean_object* x_353; 
lean_free_object(x_46);
lean_dec(x_55);
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_353 = lean_apply_6(x_1, x_10, x_30, x_37, x_14, x_15, x_42);
if (lean_obj_tag(x_353) == 0)
{
lean_object* x_354; lean_object* x_355; 
x_354 = lean_ctor_get(x_353, 0);
lean_inc(x_354);
x_355 = lean_ctor_get(x_354, 0);
lean_inc(x_355);
if (lean_obj_tag(x_355) == 0)
{
lean_object* x_356; uint8_t x_357; 
x_356 = lean_ctor_get(x_353, 1);
lean_inc(x_356);
lean_dec(x_353);
x_357 = !lean_is_exclusive(x_354);
if (x_357 == 0)
{
lean_object* x_358; lean_object* x_359; lean_object* x_360; 
x_358 = lean_ctor_get(x_354, 1);
x_359 = lean_ctor_get(x_354, 0);
lean_dec(x_359);
lean_ctor_set_tag(x_354, 6);
lean_ctor_set(x_354, 1, x_30);
lean_ctor_set(x_354, 0, x_10);
x_360 = lean_apply_5(x_3, x_354, x_358, x_14, x_15, x_356);
return x_360;
}
else
{
lean_object* x_361; lean_object* x_362; lean_object* x_363; 
x_361 = lean_ctor_get(x_354, 1);
lean_inc(x_361);
lean_dec(x_354);
x_362 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_362, 0, x_10);
lean_ctor_set(x_362, 1, x_30);
x_363 = lean_apply_5(x_3, x_362, x_361, x_14, x_15, x_356);
return x_363;
}
}
else
{
lean_object* x_364; lean_object* x_365; lean_object* x_366; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_364 = lean_ctor_get(x_353, 1);
lean_inc(x_364);
lean_dec(x_353);
x_365 = lean_ctor_get(x_354, 1);
lean_inc(x_365);
lean_dec(x_354);
x_366 = lean_ctor_get(x_355, 0);
lean_inc(x_366);
lean_dec(x_355);
x_17 = x_366;
x_18 = x_365;
x_19 = x_364;
goto block_22;
}
}
else
{
uint8_t x_367; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_367 = !lean_is_exclusive(x_353);
if (x_367 == 0)
{
return x_353;
}
else
{
lean_object* x_368; lean_object* x_369; lean_object* x_370; 
x_368 = lean_ctor_get(x_353, 0);
x_369 = lean_ctor_get(x_353, 1);
lean_inc(x_369);
lean_inc(x_368);
lean_dec(x_353);
x_370 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_370, 0, x_368);
lean_ctor_set(x_370, 1, x_369);
return x_370;
}
}
}
}
}
else
{
lean_object* x_371; 
x_371 = lean_ctor_get(x_46, 0);
lean_inc(x_371);
lean_dec(x_46);
switch (lean_obj_tag(x_371)) {
case 0:
{
lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; uint8_t x_376; 
lean_dec(x_43);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_372 = x_371;
} else {
 lean_dec_ref(x_371);
 x_372 = lean_box(0);
}
x_373 = lean_mk_string_unchecked("Quot", 4, 4);
x_374 = lean_mk_string_unchecked("lcInv", 5, 5);
x_375 = l_Lean_Name_mkStr2(x_373, x_374);
x_376 = lean_name_eq(x_10, x_375);
lean_dec(x_375);
if (x_376 == 0)
{
lean_object* x_377; lean_object* x_378; uint8_t x_379; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_377 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
x_378 = l_Lean_Name_mkStr1(x_377);
x_379 = lean_name_eq(x_10, x_378);
lean_dec(x_378);
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; 
lean_free_object(x_39);
lean_free_object(x_33);
lean_inc(x_10);
x_380 = l_Lean_IR_ToIR_findDecl___redArg(x_10, x_37, x_15, x_42);
x_381 = lean_ctor_get(x_380, 0);
lean_inc(x_381);
x_382 = lean_ctor_get(x_381, 0);
lean_inc(x_382);
if (lean_obj_tag(x_382) == 0)
{
lean_object* x_383; lean_object* x_384; lean_object* x_385; lean_object* x_386; lean_object* x_387; lean_object* x_388; lean_object* x_389; lean_object* x_390; uint8_t x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_383 = x_381;
} else {
 lean_dec_ref(x_381);
 x_383 = lean_box(0);
}
x_384 = lean_ctor_get(x_380, 1);
lean_inc(x_384);
if (lean_is_exclusive(x_380)) {
 lean_ctor_release(x_380, 0);
 lean_ctor_release(x_380, 1);
 x_385 = x_380;
} else {
 lean_dec_ref(x_380);
 x_385 = lean_box(0);
}
x_386 = lean_box(x_379);
x_387 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_387, 0, x_386);
x_388 = lean_mk_string_unchecked("axiom '", 7, 7);
if (lean_is_scalar(x_372)) {
 x_389 = lean_alloc_ctor(3, 1, 0);
} else {
 x_389 = x_372;
 lean_ctor_set_tag(x_389, 3);
}
lean_ctor_set(x_389, 0, x_388);
x_390 = lean_box(1);
x_391 = lean_unbox(x_390);
x_392 = l_Lean_Name_toString(x_10, x_391, x_387);
x_393 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_393, 0, x_392);
if (lean_is_scalar(x_383)) {
 x_394 = lean_alloc_ctor(5, 2, 0);
} else {
 x_394 = x_383;
 lean_ctor_set_tag(x_394, 5);
}
lean_ctor_set(x_394, 0, x_389);
lean_ctor_set(x_394, 1, x_393);
x_395 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_396 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_396, 0, x_395);
if (lean_is_scalar(x_385)) {
 x_397 = lean_alloc_ctor(5, 2, 0);
} else {
 x_397 = x_385;
 lean_ctor_set_tag(x_397, 5);
}
lean_ctor_set(x_397, 0, x_394);
lean_ctor_set(x_397, 1, x_396);
x_398 = l_Lean_MessageData_ofFormat(x_397);
x_399 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_398, x_14, x_15, x_384);
lean_dec(x_15);
lean_dec(x_14);
return x_399;
}
else
{
lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_418; 
lean_dec(x_372);
x_400 = lean_ctor_get(x_380, 1);
lean_inc(x_400);
lean_dec(x_380);
x_401 = lean_ctor_get(x_381, 1);
lean_inc(x_401);
if (lean_is_exclusive(x_381)) {
 lean_ctor_release(x_381, 0);
 lean_ctor_release(x_381, 1);
 x_402 = x_381;
} else {
 lean_dec_ref(x_381);
 x_402 = lean_box(0);
}
x_403 = lean_ctor_get(x_382, 0);
lean_inc(x_403);
lean_dec(x_382);
x_404 = lean_array_get_size(x_30);
x_418 = lean_ctor_get(x_403, 1);
lean_inc(x_418);
lean_dec(x_403);
x_405 = x_418;
goto block_417;
block_417:
{
lean_object* x_406; uint8_t x_407; 
x_406 = lean_array_get_size(x_405);
lean_dec(x_405);
x_407 = lean_nat_dec_lt(x_404, x_406);
if (x_407 == 0)
{
uint8_t x_408; 
x_408 = lean_nat_dec_eq(x_404, x_406);
if (x_408 == 0)
{
lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; 
lean_dec(x_3);
lean_inc(x_406);
x_409 = l_Array_extract(lean_box(0), x_30, x_24, x_406);
x_410 = l_Array_extract(lean_box(0), x_30, x_406, x_404);
lean_dec(x_30);
if (lean_is_scalar(x_402)) {
 x_411 = lean_alloc_ctor(6, 2, 0);
} else {
 x_411 = x_402;
 lean_ctor_set_tag(x_411, 6);
}
lean_ctor_set(x_411, 0, x_10);
lean_ctor_set(x_411, 1, x_409);
x_412 = lean_apply_6(x_2, x_411, x_410, x_401, x_14, x_15, x_400);
return x_412;
}
else
{
lean_object* x_413; lean_object* x_414; 
lean_dec(x_406);
lean_dec(x_404);
lean_dec(x_2);
if (lean_is_scalar(x_402)) {
 x_413 = lean_alloc_ctor(6, 2, 0);
} else {
 x_413 = x_402;
 lean_ctor_set_tag(x_413, 6);
}
lean_ctor_set(x_413, 0, x_10);
lean_ctor_set(x_413, 1, x_30);
x_414 = lean_apply_5(x_3, x_413, x_401, x_14, x_15, x_400);
return x_414;
}
}
else
{
lean_object* x_415; lean_object* x_416; 
lean_dec(x_406);
lean_dec(x_404);
lean_dec(x_2);
if (lean_is_scalar(x_402)) {
 x_415 = lean_alloc_ctor(7, 2, 0);
} else {
 x_415 = x_402;
 lean_ctor_set_tag(x_415, 7);
}
lean_ctor_set(x_415, 0, x_10);
lean_ctor_set(x_415, 1, x_30);
x_416 = lean_apply_5(x_3, x_415, x_401, x_14, x_15, x_400);
return x_416;
}
}
}
}
else
{
lean_object* x_419; 
lean_dec(x_372);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_419 = lean_box(13);
lean_ctor_set(x_33, 0, x_419);
lean_ctor_set(x_39, 0, x_33);
return x_39;
}
}
else
{
lean_object* x_420; lean_object* x_421; 
lean_dec(x_372);
lean_free_object(x_39);
lean_free_object(x_33);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_420 = lean_unsigned_to_nat(2u);
x_421 = lean_array_get(x_4, x_30, x_420);
lean_dec(x_30);
if (lean_obj_tag(x_421) == 0)
{
lean_object* x_422; lean_object* x_423; 
lean_dec(x_6);
x_422 = lean_ctor_get(x_421, 0);
lean_inc(x_422);
lean_dec(x_421);
x_423 = lean_apply_5(x_5, x_422, x_37, x_14, x_15, x_42);
return x_423;
}
else
{
lean_object* x_424; lean_object* x_425; 
lean_dec(x_5);
x_424 = lean_box(0);
x_425 = lean_apply_5(x_6, x_424, x_37, x_14, x_15, x_42);
return x_425;
}
}
}
case 2:
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; lean_object* x_430; lean_object* x_431; lean_object* x_432; 
lean_dec(x_371);
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_426 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_427 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_428 = lean_unsigned_to_nat(337u);
x_429 = lean_unsigned_to_nat(30u);
x_430 = lean_mk_string_unchecked("thm unsupported by code generator", 33, 33);
x_431 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_426, x_427, x_428, x_429, x_430);
lean_dec(x_430);
lean_dec(x_427);
lean_dec(x_426);
x_432 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_431, x_37, x_14, x_15, x_42);
return x_432;
}
case 4:
{
lean_object* x_433; lean_object* x_434; lean_object* x_435; lean_object* x_436; uint8_t x_437; 
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_433 = x_371;
} else {
 lean_dec_ref(x_371);
 x_433 = lean_box(0);
}
x_434 = lean_mk_string_unchecked("Quot", 4, 4);
x_435 = lean_mk_string_unchecked("mk", 2, 2);
x_436 = l_Lean_Name_mkStr2(x_434, x_435);
x_437 = lean_name_eq(x_10, x_436);
lean_dec(x_436);
if (x_437 == 0)
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; uint8_t x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; lean_object* x_448; lean_object* x_449; lean_object* x_450; 
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_438 = lean_box(x_437);
x_439 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_439, 0, x_438);
x_440 = lean_mk_string_unchecked("quot ", 5, 5);
if (lean_is_scalar(x_433)) {
 x_441 = lean_alloc_ctor(3, 1, 0);
} else {
 x_441 = x_433;
 lean_ctor_set_tag(x_441, 3);
}
lean_ctor_set(x_441, 0, x_440);
x_442 = lean_box(1);
x_443 = lean_unbox(x_442);
x_444 = l_Lean_Name_toString(x_10, x_443, x_439);
x_445 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_445, 0, x_444);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_445);
lean_ctor_set(x_27, 0, x_441);
x_446 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
x_447 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_447, 0, x_446);
x_448 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_448, 0, x_27);
lean_ctor_set(x_448, 1, x_447);
x_449 = l_Lean_MessageData_ofFormat(x_448);
x_450 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_449, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_450;
}
else
{
lean_object* x_451; lean_object* x_452; 
lean_dec(x_433);
lean_free_object(x_27);
lean_dec(x_10);
x_451 = lean_unsigned_to_nat(2u);
x_452 = lean_array_get(x_4, x_30, x_451);
lean_dec(x_30);
if (lean_obj_tag(x_452) == 0)
{
lean_object* x_453; lean_object* x_454; 
lean_dec(x_6);
x_453 = lean_ctor_get(x_452, 0);
lean_inc(x_453);
lean_dec(x_452);
x_454 = lean_apply_5(x_5, x_453, x_37, x_14, x_15, x_42);
return x_454;
}
else
{
lean_object* x_455; lean_object* x_456; 
lean_dec(x_5);
x_455 = lean_box(0);
x_456 = lean_apply_5(x_6, x_455, x_37, x_14, x_15, x_42);
return x_456;
}
}
}
case 5:
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_371);
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_457 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_458 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_459 = lean_unsigned_to_nat(336u);
x_460 = lean_unsigned_to_nat(33u);
x_461 = lean_mk_string_unchecked("induct unsupported by code generator", 36, 36);
x_462 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_457, x_458, x_459, x_460, x_461);
lean_dec(x_461);
lean_dec(x_458);
lean_dec(x_457);
x_463 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_462, x_37, x_14, x_15, x_42);
return x_463;
}
case 6:
{
lean_object* x_464; uint8_t x_465; 
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_464 = lean_ctor_get(x_371, 0);
lean_inc(x_464);
lean_dec(x_371);
lean_inc(x_10);
x_465 = l_Lean_isExtern(x_43, x_10);
if (x_465 == 0)
{
lean_object* x_466; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
x_466 = l_Lean_IR_ToIR_getCtorInfo(x_10, x_37, x_14, x_15, x_42);
if (lean_obj_tag(x_466) == 0)
{
lean_object* x_467; lean_object* x_468; lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; lean_object* x_482; lean_object* x_483; lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; 
x_467 = lean_ctor_get(x_466, 0);
lean_inc(x_467);
x_468 = lean_ctor_get(x_467, 0);
lean_inc(x_468);
x_469 = lean_ctor_get(x_466, 1);
lean_inc(x_469);
lean_dec(x_466);
x_470 = lean_ctor_get(x_467, 1);
lean_inc(x_470);
lean_dec(x_467);
x_471 = lean_ctor_get(x_468, 0);
lean_inc(x_471);
x_472 = lean_ctor_get(x_468, 1);
lean_inc(x_472);
lean_dec(x_468);
x_473 = lean_ctor_get(x_464, 3);
lean_inc(x_473);
lean_dec(x_464);
x_474 = lean_array_get_size(x_12);
x_475 = l_Array_extract(lean_box(0), x_12, x_473, x_474);
lean_dec(x_12);
x_476 = lean_mk_empty_array_with_capacity(x_24);
x_477 = lean_array_get_size(x_472);
x_478 = lean_unsigned_to_nat(1u);
x_479 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_479, 0, x_24);
lean_ctor_set(x_479, 1, x_477);
lean_ctor_set(x_479, 2, x_478);
x_480 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_475, x_472, x_465, x_479, x_476, x_24, x_470, x_469);
lean_dec(x_479);
x_481 = lean_ctor_get(x_480, 0);
lean_inc(x_481);
x_482 = lean_ctor_get(x_480, 1);
lean_inc(x_482);
lean_dec(x_480);
x_483 = lean_ctor_get(x_481, 0);
lean_inc(x_483);
x_484 = lean_ctor_get(x_481, 1);
lean_inc(x_484);
lean_dec(x_481);
x_485 = lean_ctor_get(x_7, 0);
lean_inc(x_485);
lean_dec(x_7);
x_486 = l_Lean_IR_ToIR_bindVar___redArg(x_485, x_484, x_482);
x_487 = lean_ctor_get(x_486, 0);
lean_inc(x_487);
x_488 = lean_ctor_get(x_486, 1);
lean_inc(x_488);
lean_dec(x_486);
x_489 = lean_ctor_get(x_487, 0);
lean_inc(x_489);
x_490 = lean_ctor_get(x_487, 1);
lean_inc(x_490);
if (lean_is_exclusive(x_487)) {
 lean_ctor_release(x_487, 0);
 lean_ctor_release(x_487, 1);
 x_491 = x_487;
} else {
 lean_dec_ref(x_487);
 x_491 = lean_box(0);
}
lean_inc(x_489);
x_492 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_8, x_471, x_472, x_475, x_489, x_490, x_14, x_15, x_488);
lean_dec(x_475);
lean_dec(x_472);
if (lean_obj_tag(x_492) == 0)
{
lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; lean_object* x_498; lean_object* x_499; lean_object* x_500; lean_object* x_501; lean_object* x_502; lean_object* x_503; 
x_493 = lean_ctor_get(x_492, 0);
lean_inc(x_493);
x_494 = lean_ctor_get(x_492, 1);
lean_inc(x_494);
if (lean_is_exclusive(x_492)) {
 lean_ctor_release(x_492, 0);
 lean_ctor_release(x_492, 1);
 x_495 = x_492;
} else {
 lean_dec_ref(x_492);
 x_495 = lean_box(0);
}
x_496 = lean_ctor_get(x_493, 0);
lean_inc(x_496);
x_497 = lean_ctor_get(x_493, 1);
lean_inc(x_497);
if (lean_is_exclusive(x_493)) {
 lean_ctor_release(x_493, 0);
 lean_ctor_release(x_493, 1);
 x_498 = x_493;
} else {
 lean_dec_ref(x_493);
 x_498 = lean_box(0);
}
x_499 = lean_box(7);
if (lean_is_scalar(x_491)) {
 x_500 = lean_alloc_ctor(0, 2, 0);
} else {
 x_500 = x_491;
}
lean_ctor_set(x_500, 0, x_471);
lean_ctor_set(x_500, 1, x_483);
x_501 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_501, 0, x_489);
lean_ctor_set(x_501, 1, x_499);
lean_ctor_set(x_501, 2, x_500);
lean_ctor_set(x_501, 3, x_496);
if (lean_is_scalar(x_498)) {
 x_502 = lean_alloc_ctor(0, 2, 0);
} else {
 x_502 = x_498;
}
lean_ctor_set(x_502, 0, x_501);
lean_ctor_set(x_502, 1, x_497);
if (lean_is_scalar(x_495)) {
 x_503 = lean_alloc_ctor(0, 2, 0);
} else {
 x_503 = x_495;
}
lean_ctor_set(x_503, 0, x_502);
lean_ctor_set(x_503, 1, x_494);
return x_503;
}
else
{
lean_dec(x_491);
lean_dec(x_489);
lean_dec(x_483);
lean_dec(x_471);
return x_492;
}
}
else
{
lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; 
lean_dec(x_464);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_504 = lean_ctor_get(x_466, 0);
lean_inc(x_504);
x_505 = lean_ctor_get(x_466, 1);
lean_inc(x_505);
if (lean_is_exclusive(x_466)) {
 lean_ctor_release(x_466, 0);
 lean_ctor_release(x_466, 1);
 x_506 = x_466;
} else {
 lean_dec_ref(x_466);
 x_506 = lean_box(0);
}
if (lean_is_scalar(x_506)) {
 x_507 = lean_alloc_ctor(1, 2, 0);
} else {
 x_507 = x_506;
}
lean_ctor_set(x_507, 0, x_504);
lean_ctor_set(x_507, 1, x_505);
return x_507;
}
}
else
{
lean_object* x_508; 
lean_dec(x_464);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_508 = lean_apply_6(x_1, x_10, x_30, x_37, x_14, x_15, x_42);
if (lean_obj_tag(x_508) == 0)
{
lean_object* x_509; lean_object* x_510; 
x_509 = lean_ctor_get(x_508, 0);
lean_inc(x_509);
x_510 = lean_ctor_get(x_509, 0);
lean_inc(x_510);
if (lean_obj_tag(x_510) == 0)
{
lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_511 = lean_ctor_get(x_508, 1);
lean_inc(x_511);
lean_dec(x_508);
x_512 = lean_ctor_get(x_509, 1);
lean_inc(x_512);
if (lean_is_exclusive(x_509)) {
 lean_ctor_release(x_509, 0);
 lean_ctor_release(x_509, 1);
 x_513 = x_509;
} else {
 lean_dec_ref(x_509);
 x_513 = lean_box(0);
}
if (lean_is_scalar(x_513)) {
 x_514 = lean_alloc_ctor(6, 2, 0);
} else {
 x_514 = x_513;
 lean_ctor_set_tag(x_514, 6);
}
lean_ctor_set(x_514, 0, x_10);
lean_ctor_set(x_514, 1, x_30);
x_515 = lean_apply_5(x_3, x_514, x_512, x_14, x_15, x_511);
return x_515;
}
else
{
lean_object* x_516; lean_object* x_517; lean_object* x_518; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_516 = lean_ctor_get(x_508, 1);
lean_inc(x_516);
lean_dec(x_508);
x_517 = lean_ctor_get(x_509, 1);
lean_inc(x_517);
lean_dec(x_509);
x_518 = lean_ctor_get(x_510, 0);
lean_inc(x_518);
lean_dec(x_510);
x_17 = x_518;
x_18 = x_517;
x_19 = x_516;
goto block_22;
}
}
else
{
lean_object* x_519; lean_object* x_520; lean_object* x_521; lean_object* x_522; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_519 = lean_ctor_get(x_508, 0);
lean_inc(x_519);
x_520 = lean_ctor_get(x_508, 1);
lean_inc(x_520);
if (lean_is_exclusive(x_508)) {
 lean_ctor_release(x_508, 0);
 lean_ctor_release(x_508, 1);
 x_521 = x_508;
} else {
 lean_dec_ref(x_508);
 x_521 = lean_box(0);
}
if (lean_is_scalar(x_521)) {
 x_522 = lean_alloc_ctor(1, 2, 0);
} else {
 x_522 = x_521;
}
lean_ctor_set(x_522, 0, x_519);
lean_ctor_set(x_522, 1, x_520);
return x_522;
}
}
}
case 7:
{
lean_object* x_523; lean_object* x_524; lean_object* x_525; lean_object* x_526; uint8_t x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; lean_object* x_531; lean_object* x_532; lean_object* x_533; lean_object* x_534; 
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_371)) {
 lean_ctor_release(x_371, 0);
 x_523 = x_371;
} else {
 lean_dec_ref(x_371);
 x_523 = lean_box(0);
}
x_524 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
if (lean_is_scalar(x_523)) {
 x_525 = lean_alloc_ctor(3, 1, 0);
} else {
 x_525 = x_523;
 lean_ctor_set_tag(x_525, 3);
}
lean_ctor_set(x_525, 0, x_524);
x_526 = lean_box(1);
x_527 = lean_unbox(x_526);
x_528 = l_Lean_Name_toString(x_10, x_527, x_9);
x_529 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_529, 0, x_528);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_529);
lean_ctor_set(x_27, 0, x_525);
x_530 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_531 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_531, 0, x_530);
x_532 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_532, 0, x_27);
lean_ctor_set(x_532, 1, x_531);
x_533 = l_Lean_MessageData_ofFormat(x_532);
x_534 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_533, x_14, x_15, x_42);
lean_dec(x_15);
lean_dec(x_14);
return x_534;
}
default: 
{
lean_object* x_535; 
lean_dec(x_371);
lean_dec(x_43);
lean_free_object(x_39);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_535 = lean_apply_6(x_1, x_10, x_30, x_37, x_14, x_15, x_42);
if (lean_obj_tag(x_535) == 0)
{
lean_object* x_536; lean_object* x_537; 
x_536 = lean_ctor_get(x_535, 0);
lean_inc(x_536);
x_537 = lean_ctor_get(x_536, 0);
lean_inc(x_537);
if (lean_obj_tag(x_537) == 0)
{
lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; 
x_538 = lean_ctor_get(x_535, 1);
lean_inc(x_538);
lean_dec(x_535);
x_539 = lean_ctor_get(x_536, 1);
lean_inc(x_539);
if (lean_is_exclusive(x_536)) {
 lean_ctor_release(x_536, 0);
 lean_ctor_release(x_536, 1);
 x_540 = x_536;
} else {
 lean_dec_ref(x_536);
 x_540 = lean_box(0);
}
if (lean_is_scalar(x_540)) {
 x_541 = lean_alloc_ctor(6, 2, 0);
} else {
 x_541 = x_540;
 lean_ctor_set_tag(x_541, 6);
}
lean_ctor_set(x_541, 0, x_10);
lean_ctor_set(x_541, 1, x_30);
x_542 = lean_apply_5(x_3, x_541, x_539, x_14, x_15, x_538);
return x_542;
}
else
{
lean_object* x_543; lean_object* x_544; lean_object* x_545; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_543 = lean_ctor_get(x_535, 1);
lean_inc(x_543);
lean_dec(x_535);
x_544 = lean_ctor_get(x_536, 1);
lean_inc(x_544);
lean_dec(x_536);
x_545 = lean_ctor_get(x_537, 0);
lean_inc(x_545);
lean_dec(x_537);
x_17 = x_545;
x_18 = x_544;
x_19 = x_543;
goto block_22;
}
}
else
{
lean_object* x_546; lean_object* x_547; lean_object* x_548; lean_object* x_549; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_546 = lean_ctor_get(x_535, 0);
lean_inc(x_546);
x_547 = lean_ctor_get(x_535, 1);
lean_inc(x_547);
if (lean_is_exclusive(x_535)) {
 lean_ctor_release(x_535, 0);
 lean_ctor_release(x_535, 1);
 x_548 = x_535;
} else {
 lean_dec_ref(x_535);
 x_548 = lean_box(0);
}
if (lean_is_scalar(x_548)) {
 x_549 = lean_alloc_ctor(1, 2, 0);
} else {
 x_549 = x_548;
}
lean_ctor_set(x_549, 0, x_546);
lean_ctor_set(x_549, 1, x_547);
return x_549;
}
}
}
}
}
}
else
{
lean_object* x_550; lean_object* x_551; lean_object* x_552; lean_object* x_553; uint8_t x_554; lean_object* x_555; 
x_550 = lean_ctor_get(x_39, 0);
x_551 = lean_ctor_get(x_39, 1);
lean_inc(x_551);
lean_inc(x_550);
lean_dec(x_39);
x_552 = lean_ctor_get(x_550, 0);
lean_inc(x_552);
lean_dec(x_550);
x_553 = lean_box(0);
x_554 = lean_unbox(x_553);
lean_inc(x_10);
lean_inc(x_552);
x_555 = l_Lean_Environment_find_x3f(x_552, x_10, x_554);
if (lean_obj_tag(x_555) == 0)
{
lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; 
lean_dec(x_552);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_556 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_557 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_558 = lean_unsigned_to_nat(338u);
x_559 = lean_unsigned_to_nat(16u);
x_560 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
x_561 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_556, x_557, x_558, x_559, x_560);
lean_dec(x_560);
lean_dec(x_557);
lean_dec(x_556);
x_562 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_561, x_37, x_14, x_15, x_551);
return x_562;
}
else
{
lean_object* x_563; lean_object* x_564; 
x_563 = lean_ctor_get(x_555, 0);
lean_inc(x_563);
if (lean_is_exclusive(x_555)) {
 lean_ctor_release(x_555, 0);
 x_564 = x_555;
} else {
 lean_dec_ref(x_555);
 x_564 = lean_box(0);
}
switch (lean_obj_tag(x_563)) {
case 0:
{
lean_object* x_565; lean_object* x_566; lean_object* x_567; lean_object* x_568; uint8_t x_569; 
lean_dec(x_552);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_565 = x_563;
} else {
 lean_dec_ref(x_563);
 x_565 = lean_box(0);
}
x_566 = lean_mk_string_unchecked("Quot", 4, 4);
x_567 = lean_mk_string_unchecked("lcInv", 5, 5);
x_568 = l_Lean_Name_mkStr2(x_566, x_567);
x_569 = lean_name_eq(x_10, x_568);
lean_dec(x_568);
if (x_569 == 0)
{
lean_object* x_570; lean_object* x_571; uint8_t x_572; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_570 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
x_571 = l_Lean_Name_mkStr1(x_570);
x_572 = lean_name_eq(x_10, x_571);
lean_dec(x_571);
if (x_572 == 0)
{
lean_object* x_573; lean_object* x_574; lean_object* x_575; 
lean_free_object(x_33);
lean_inc(x_10);
x_573 = l_Lean_IR_ToIR_findDecl___redArg(x_10, x_37, x_15, x_551);
x_574 = lean_ctor_get(x_573, 0);
lean_inc(x_574);
x_575 = lean_ctor_get(x_574, 0);
lean_inc(x_575);
if (lean_obj_tag(x_575) == 0)
{
lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; lean_object* x_583; uint8_t x_584; lean_object* x_585; lean_object* x_586; lean_object* x_587; lean_object* x_588; lean_object* x_589; lean_object* x_590; lean_object* x_591; lean_object* x_592; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_576 = x_574;
} else {
 lean_dec_ref(x_574);
 x_576 = lean_box(0);
}
x_577 = lean_ctor_get(x_573, 1);
lean_inc(x_577);
if (lean_is_exclusive(x_573)) {
 lean_ctor_release(x_573, 0);
 lean_ctor_release(x_573, 1);
 x_578 = x_573;
} else {
 lean_dec_ref(x_573);
 x_578 = lean_box(0);
}
x_579 = lean_box(x_572);
x_580 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_580, 0, x_579);
x_581 = lean_mk_string_unchecked("axiom '", 7, 7);
if (lean_is_scalar(x_565)) {
 x_582 = lean_alloc_ctor(3, 1, 0);
} else {
 x_582 = x_565;
 lean_ctor_set_tag(x_582, 3);
}
lean_ctor_set(x_582, 0, x_581);
x_583 = lean_box(1);
x_584 = lean_unbox(x_583);
x_585 = l_Lean_Name_toString(x_10, x_584, x_580);
if (lean_is_scalar(x_564)) {
 x_586 = lean_alloc_ctor(3, 1, 0);
} else {
 x_586 = x_564;
 lean_ctor_set_tag(x_586, 3);
}
lean_ctor_set(x_586, 0, x_585);
if (lean_is_scalar(x_576)) {
 x_587 = lean_alloc_ctor(5, 2, 0);
} else {
 x_587 = x_576;
 lean_ctor_set_tag(x_587, 5);
}
lean_ctor_set(x_587, 0, x_582);
lean_ctor_set(x_587, 1, x_586);
x_588 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_589 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_589, 0, x_588);
if (lean_is_scalar(x_578)) {
 x_590 = lean_alloc_ctor(5, 2, 0);
} else {
 x_590 = x_578;
 lean_ctor_set_tag(x_590, 5);
}
lean_ctor_set(x_590, 0, x_587);
lean_ctor_set(x_590, 1, x_589);
x_591 = l_Lean_MessageData_ofFormat(x_590);
x_592 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_591, x_14, x_15, x_577);
lean_dec(x_15);
lean_dec(x_14);
return x_592;
}
else
{
lean_object* x_593; lean_object* x_594; lean_object* x_595; lean_object* x_596; lean_object* x_597; lean_object* x_598; lean_object* x_611; 
lean_dec(x_565);
lean_dec(x_564);
x_593 = lean_ctor_get(x_573, 1);
lean_inc(x_593);
lean_dec(x_573);
x_594 = lean_ctor_get(x_574, 1);
lean_inc(x_594);
if (lean_is_exclusive(x_574)) {
 lean_ctor_release(x_574, 0);
 lean_ctor_release(x_574, 1);
 x_595 = x_574;
} else {
 lean_dec_ref(x_574);
 x_595 = lean_box(0);
}
x_596 = lean_ctor_get(x_575, 0);
lean_inc(x_596);
lean_dec(x_575);
x_597 = lean_array_get_size(x_30);
x_611 = lean_ctor_get(x_596, 1);
lean_inc(x_611);
lean_dec(x_596);
x_598 = x_611;
goto block_610;
block_610:
{
lean_object* x_599; uint8_t x_600; 
x_599 = lean_array_get_size(x_598);
lean_dec(x_598);
x_600 = lean_nat_dec_lt(x_597, x_599);
if (x_600 == 0)
{
uint8_t x_601; 
x_601 = lean_nat_dec_eq(x_597, x_599);
if (x_601 == 0)
{
lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
lean_dec(x_3);
lean_inc(x_599);
x_602 = l_Array_extract(lean_box(0), x_30, x_24, x_599);
x_603 = l_Array_extract(lean_box(0), x_30, x_599, x_597);
lean_dec(x_30);
if (lean_is_scalar(x_595)) {
 x_604 = lean_alloc_ctor(6, 2, 0);
} else {
 x_604 = x_595;
 lean_ctor_set_tag(x_604, 6);
}
lean_ctor_set(x_604, 0, x_10);
lean_ctor_set(x_604, 1, x_602);
x_605 = lean_apply_6(x_2, x_604, x_603, x_594, x_14, x_15, x_593);
return x_605;
}
else
{
lean_object* x_606; lean_object* x_607; 
lean_dec(x_599);
lean_dec(x_597);
lean_dec(x_2);
if (lean_is_scalar(x_595)) {
 x_606 = lean_alloc_ctor(6, 2, 0);
} else {
 x_606 = x_595;
 lean_ctor_set_tag(x_606, 6);
}
lean_ctor_set(x_606, 0, x_10);
lean_ctor_set(x_606, 1, x_30);
x_607 = lean_apply_5(x_3, x_606, x_594, x_14, x_15, x_593);
return x_607;
}
}
else
{
lean_object* x_608; lean_object* x_609; 
lean_dec(x_599);
lean_dec(x_597);
lean_dec(x_2);
if (lean_is_scalar(x_595)) {
 x_608 = lean_alloc_ctor(7, 2, 0);
} else {
 x_608 = x_595;
 lean_ctor_set_tag(x_608, 7);
}
lean_ctor_set(x_608, 0, x_10);
lean_ctor_set(x_608, 1, x_30);
x_609 = lean_apply_5(x_3, x_608, x_594, x_14, x_15, x_593);
return x_609;
}
}
}
}
else
{
lean_object* x_612; lean_object* x_613; 
lean_dec(x_565);
lean_dec(x_564);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_612 = lean_box(13);
lean_ctor_set(x_33, 0, x_612);
x_613 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_613, 0, x_33);
lean_ctor_set(x_613, 1, x_551);
return x_613;
}
}
else
{
lean_object* x_614; lean_object* x_615; 
lean_dec(x_565);
lean_dec(x_564);
lean_free_object(x_33);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_614 = lean_unsigned_to_nat(2u);
x_615 = lean_array_get(x_4, x_30, x_614);
lean_dec(x_30);
if (lean_obj_tag(x_615) == 0)
{
lean_object* x_616; lean_object* x_617; 
lean_dec(x_6);
x_616 = lean_ctor_get(x_615, 0);
lean_inc(x_616);
lean_dec(x_615);
x_617 = lean_apply_5(x_5, x_616, x_37, x_14, x_15, x_551);
return x_617;
}
else
{
lean_object* x_618; lean_object* x_619; 
lean_dec(x_5);
x_618 = lean_box(0);
x_619 = lean_apply_5(x_6, x_618, x_37, x_14, x_15, x_551);
return x_619;
}
}
}
case 2:
{
lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; lean_object* x_624; lean_object* x_625; lean_object* x_626; 
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_552);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_620 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_621 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_622 = lean_unsigned_to_nat(337u);
x_623 = lean_unsigned_to_nat(30u);
x_624 = lean_mk_string_unchecked("thm unsupported by code generator", 33, 33);
x_625 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_620, x_621, x_622, x_623, x_624);
lean_dec(x_624);
lean_dec(x_621);
lean_dec(x_620);
x_626 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_625, x_37, x_14, x_15, x_551);
return x_626;
}
case 4:
{
lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; uint8_t x_631; 
lean_dec(x_552);
lean_free_object(x_33);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_627 = x_563;
} else {
 lean_dec_ref(x_563);
 x_627 = lean_box(0);
}
x_628 = lean_mk_string_unchecked("Quot", 4, 4);
x_629 = lean_mk_string_unchecked("mk", 2, 2);
x_630 = l_Lean_Name_mkStr2(x_628, x_629);
x_631 = lean_name_eq(x_10, x_630);
lean_dec(x_630);
if (x_631 == 0)
{
lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; uint8_t x_637; lean_object* x_638; lean_object* x_639; lean_object* x_640; lean_object* x_641; lean_object* x_642; lean_object* x_643; lean_object* x_644; 
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_632 = lean_box(x_631);
x_633 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_633, 0, x_632);
x_634 = lean_mk_string_unchecked("quot ", 5, 5);
if (lean_is_scalar(x_627)) {
 x_635 = lean_alloc_ctor(3, 1, 0);
} else {
 x_635 = x_627;
 lean_ctor_set_tag(x_635, 3);
}
lean_ctor_set(x_635, 0, x_634);
x_636 = lean_box(1);
x_637 = lean_unbox(x_636);
x_638 = l_Lean_Name_toString(x_10, x_637, x_633);
if (lean_is_scalar(x_564)) {
 x_639 = lean_alloc_ctor(3, 1, 0);
} else {
 x_639 = x_564;
 lean_ctor_set_tag(x_639, 3);
}
lean_ctor_set(x_639, 0, x_638);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_639);
lean_ctor_set(x_27, 0, x_635);
x_640 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
x_641 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_641, 0, x_640);
x_642 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_642, 0, x_27);
lean_ctor_set(x_642, 1, x_641);
x_643 = l_Lean_MessageData_ofFormat(x_642);
x_644 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_643, x_14, x_15, x_551);
lean_dec(x_15);
lean_dec(x_14);
return x_644;
}
else
{
lean_object* x_645; lean_object* x_646; 
lean_dec(x_627);
lean_dec(x_564);
lean_free_object(x_27);
lean_dec(x_10);
x_645 = lean_unsigned_to_nat(2u);
x_646 = lean_array_get(x_4, x_30, x_645);
lean_dec(x_30);
if (lean_obj_tag(x_646) == 0)
{
lean_object* x_647; lean_object* x_648; 
lean_dec(x_6);
x_647 = lean_ctor_get(x_646, 0);
lean_inc(x_647);
lean_dec(x_646);
x_648 = lean_apply_5(x_5, x_647, x_37, x_14, x_15, x_551);
return x_648;
}
else
{
lean_object* x_649; lean_object* x_650; 
lean_dec(x_5);
x_649 = lean_box(0);
x_650 = lean_apply_5(x_6, x_649, x_37, x_14, x_15, x_551);
return x_650;
}
}
}
case 5:
{
lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_552);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_651 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_652 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_653 = lean_unsigned_to_nat(336u);
x_654 = lean_unsigned_to_nat(33u);
x_655 = lean_mk_string_unchecked("induct unsupported by code generator", 36, 36);
x_656 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_651, x_652, x_653, x_654, x_655);
lean_dec(x_655);
lean_dec(x_652);
lean_dec(x_651);
x_657 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_656, x_37, x_14, x_15, x_551);
return x_657;
}
case 6:
{
lean_object* x_658; uint8_t x_659; 
lean_dec(x_564);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_658 = lean_ctor_get(x_563, 0);
lean_inc(x_658);
lean_dec(x_563);
lean_inc(x_10);
x_659 = l_Lean_isExtern(x_552, x_10);
if (x_659 == 0)
{
lean_object* x_660; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
x_660 = l_Lean_IR_ToIR_getCtorInfo(x_10, x_37, x_14, x_15, x_551);
if (lean_obj_tag(x_660) == 0)
{
lean_object* x_661; lean_object* x_662; lean_object* x_663; lean_object* x_664; lean_object* x_665; lean_object* x_666; lean_object* x_667; lean_object* x_668; lean_object* x_669; lean_object* x_670; lean_object* x_671; lean_object* x_672; lean_object* x_673; lean_object* x_674; lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; lean_object* x_682; lean_object* x_683; lean_object* x_684; lean_object* x_685; lean_object* x_686; 
x_661 = lean_ctor_get(x_660, 0);
lean_inc(x_661);
x_662 = lean_ctor_get(x_661, 0);
lean_inc(x_662);
x_663 = lean_ctor_get(x_660, 1);
lean_inc(x_663);
lean_dec(x_660);
x_664 = lean_ctor_get(x_661, 1);
lean_inc(x_664);
lean_dec(x_661);
x_665 = lean_ctor_get(x_662, 0);
lean_inc(x_665);
x_666 = lean_ctor_get(x_662, 1);
lean_inc(x_666);
lean_dec(x_662);
x_667 = lean_ctor_get(x_658, 3);
lean_inc(x_667);
lean_dec(x_658);
x_668 = lean_array_get_size(x_12);
x_669 = l_Array_extract(lean_box(0), x_12, x_667, x_668);
lean_dec(x_12);
x_670 = lean_mk_empty_array_with_capacity(x_24);
x_671 = lean_array_get_size(x_666);
x_672 = lean_unsigned_to_nat(1u);
x_673 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_673, 0, x_24);
lean_ctor_set(x_673, 1, x_671);
lean_ctor_set(x_673, 2, x_672);
x_674 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_669, x_666, x_659, x_673, x_670, x_24, x_664, x_663);
lean_dec(x_673);
x_675 = lean_ctor_get(x_674, 0);
lean_inc(x_675);
x_676 = lean_ctor_get(x_674, 1);
lean_inc(x_676);
lean_dec(x_674);
x_677 = lean_ctor_get(x_675, 0);
lean_inc(x_677);
x_678 = lean_ctor_get(x_675, 1);
lean_inc(x_678);
lean_dec(x_675);
x_679 = lean_ctor_get(x_7, 0);
lean_inc(x_679);
lean_dec(x_7);
x_680 = l_Lean_IR_ToIR_bindVar___redArg(x_679, x_678, x_676);
x_681 = lean_ctor_get(x_680, 0);
lean_inc(x_681);
x_682 = lean_ctor_get(x_680, 1);
lean_inc(x_682);
lean_dec(x_680);
x_683 = lean_ctor_get(x_681, 0);
lean_inc(x_683);
x_684 = lean_ctor_get(x_681, 1);
lean_inc(x_684);
if (lean_is_exclusive(x_681)) {
 lean_ctor_release(x_681, 0);
 lean_ctor_release(x_681, 1);
 x_685 = x_681;
} else {
 lean_dec_ref(x_681);
 x_685 = lean_box(0);
}
lean_inc(x_683);
x_686 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_8, x_665, x_666, x_669, x_683, x_684, x_14, x_15, x_682);
lean_dec(x_669);
lean_dec(x_666);
if (lean_obj_tag(x_686) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; 
x_687 = lean_ctor_get(x_686, 0);
lean_inc(x_687);
x_688 = lean_ctor_get(x_686, 1);
lean_inc(x_688);
if (lean_is_exclusive(x_686)) {
 lean_ctor_release(x_686, 0);
 lean_ctor_release(x_686, 1);
 x_689 = x_686;
} else {
 lean_dec_ref(x_686);
 x_689 = lean_box(0);
}
x_690 = lean_ctor_get(x_687, 0);
lean_inc(x_690);
x_691 = lean_ctor_get(x_687, 1);
lean_inc(x_691);
if (lean_is_exclusive(x_687)) {
 lean_ctor_release(x_687, 0);
 lean_ctor_release(x_687, 1);
 x_692 = x_687;
} else {
 lean_dec_ref(x_687);
 x_692 = lean_box(0);
}
x_693 = lean_box(7);
if (lean_is_scalar(x_685)) {
 x_694 = lean_alloc_ctor(0, 2, 0);
} else {
 x_694 = x_685;
}
lean_ctor_set(x_694, 0, x_665);
lean_ctor_set(x_694, 1, x_677);
x_695 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_695, 0, x_683);
lean_ctor_set(x_695, 1, x_693);
lean_ctor_set(x_695, 2, x_694);
lean_ctor_set(x_695, 3, x_690);
if (lean_is_scalar(x_692)) {
 x_696 = lean_alloc_ctor(0, 2, 0);
} else {
 x_696 = x_692;
}
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_691);
if (lean_is_scalar(x_689)) {
 x_697 = lean_alloc_ctor(0, 2, 0);
} else {
 x_697 = x_689;
}
lean_ctor_set(x_697, 0, x_696);
lean_ctor_set(x_697, 1, x_688);
return x_697;
}
else
{
lean_dec(x_685);
lean_dec(x_683);
lean_dec(x_677);
lean_dec(x_665);
return x_686;
}
}
else
{
lean_object* x_698; lean_object* x_699; lean_object* x_700; lean_object* x_701; 
lean_dec(x_658);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_698 = lean_ctor_get(x_660, 0);
lean_inc(x_698);
x_699 = lean_ctor_get(x_660, 1);
lean_inc(x_699);
if (lean_is_exclusive(x_660)) {
 lean_ctor_release(x_660, 0);
 lean_ctor_release(x_660, 1);
 x_700 = x_660;
} else {
 lean_dec_ref(x_660);
 x_700 = lean_box(0);
}
if (lean_is_scalar(x_700)) {
 x_701 = lean_alloc_ctor(1, 2, 0);
} else {
 x_701 = x_700;
}
lean_ctor_set(x_701, 0, x_698);
lean_ctor_set(x_701, 1, x_699);
return x_701;
}
}
else
{
lean_object* x_702; 
lean_dec(x_658);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_702 = lean_apply_6(x_1, x_10, x_30, x_37, x_14, x_15, x_551);
if (lean_obj_tag(x_702) == 0)
{
lean_object* x_703; lean_object* x_704; 
x_703 = lean_ctor_get(x_702, 0);
lean_inc(x_703);
x_704 = lean_ctor_get(x_703, 0);
lean_inc(x_704);
if (lean_obj_tag(x_704) == 0)
{
lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; 
x_705 = lean_ctor_get(x_702, 1);
lean_inc(x_705);
lean_dec(x_702);
x_706 = lean_ctor_get(x_703, 1);
lean_inc(x_706);
if (lean_is_exclusive(x_703)) {
 lean_ctor_release(x_703, 0);
 lean_ctor_release(x_703, 1);
 x_707 = x_703;
} else {
 lean_dec_ref(x_703);
 x_707 = lean_box(0);
}
if (lean_is_scalar(x_707)) {
 x_708 = lean_alloc_ctor(6, 2, 0);
} else {
 x_708 = x_707;
 lean_ctor_set_tag(x_708, 6);
}
lean_ctor_set(x_708, 0, x_10);
lean_ctor_set(x_708, 1, x_30);
x_709 = lean_apply_5(x_3, x_708, x_706, x_14, x_15, x_705);
return x_709;
}
else
{
lean_object* x_710; lean_object* x_711; lean_object* x_712; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_710 = lean_ctor_get(x_702, 1);
lean_inc(x_710);
lean_dec(x_702);
x_711 = lean_ctor_get(x_703, 1);
lean_inc(x_711);
lean_dec(x_703);
x_712 = lean_ctor_get(x_704, 0);
lean_inc(x_712);
lean_dec(x_704);
x_17 = x_712;
x_18 = x_711;
x_19 = x_710;
goto block_22;
}
}
else
{
lean_object* x_713; lean_object* x_714; lean_object* x_715; lean_object* x_716; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_713 = lean_ctor_get(x_702, 0);
lean_inc(x_713);
x_714 = lean_ctor_get(x_702, 1);
lean_inc(x_714);
if (lean_is_exclusive(x_702)) {
 lean_ctor_release(x_702, 0);
 lean_ctor_release(x_702, 1);
 x_715 = x_702;
} else {
 lean_dec_ref(x_702);
 x_715 = lean_box(0);
}
if (lean_is_scalar(x_715)) {
 x_716 = lean_alloc_ctor(1, 2, 0);
} else {
 x_716 = x_715;
}
lean_ctor_set(x_716, 0, x_713);
lean_ctor_set(x_716, 1, x_714);
return x_716;
}
}
}
case 7:
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; lean_object* x_720; uint8_t x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; 
lean_dec(x_552);
lean_free_object(x_33);
lean_dec(x_37);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_563)) {
 lean_ctor_release(x_563, 0);
 x_717 = x_563;
} else {
 lean_dec_ref(x_563);
 x_717 = lean_box(0);
}
x_718 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
if (lean_is_scalar(x_717)) {
 x_719 = lean_alloc_ctor(3, 1, 0);
} else {
 x_719 = x_717;
 lean_ctor_set_tag(x_719, 3);
}
lean_ctor_set(x_719, 0, x_718);
x_720 = lean_box(1);
x_721 = lean_unbox(x_720);
x_722 = l_Lean_Name_toString(x_10, x_721, x_9);
if (lean_is_scalar(x_564)) {
 x_723 = lean_alloc_ctor(3, 1, 0);
} else {
 x_723 = x_564;
 lean_ctor_set_tag(x_723, 3);
}
lean_ctor_set(x_723, 0, x_722);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_723);
lean_ctor_set(x_27, 0, x_719);
x_724 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_725 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_725, 0, x_724);
x_726 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_726, 0, x_27);
lean_ctor_set(x_726, 1, x_725);
x_727 = l_Lean_MessageData_ofFormat(x_726);
x_728 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_727, x_14, x_15, x_551);
lean_dec(x_15);
lean_dec(x_14);
return x_728;
}
default: 
{
lean_object* x_729; 
lean_dec(x_564);
lean_dec(x_563);
lean_dec(x_552);
lean_free_object(x_33);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_729 = lean_apply_6(x_1, x_10, x_30, x_37, x_14, x_15, x_551);
if (lean_obj_tag(x_729) == 0)
{
lean_object* x_730; lean_object* x_731; 
x_730 = lean_ctor_get(x_729, 0);
lean_inc(x_730);
x_731 = lean_ctor_get(x_730, 0);
lean_inc(x_731);
if (lean_obj_tag(x_731) == 0)
{
lean_object* x_732; lean_object* x_733; lean_object* x_734; lean_object* x_735; lean_object* x_736; 
x_732 = lean_ctor_get(x_729, 1);
lean_inc(x_732);
lean_dec(x_729);
x_733 = lean_ctor_get(x_730, 1);
lean_inc(x_733);
if (lean_is_exclusive(x_730)) {
 lean_ctor_release(x_730, 0);
 lean_ctor_release(x_730, 1);
 x_734 = x_730;
} else {
 lean_dec_ref(x_730);
 x_734 = lean_box(0);
}
if (lean_is_scalar(x_734)) {
 x_735 = lean_alloc_ctor(6, 2, 0);
} else {
 x_735 = x_734;
 lean_ctor_set_tag(x_735, 6);
}
lean_ctor_set(x_735, 0, x_10);
lean_ctor_set(x_735, 1, x_30);
x_736 = lean_apply_5(x_3, x_735, x_733, x_14, x_15, x_732);
return x_736;
}
else
{
lean_object* x_737; lean_object* x_738; lean_object* x_739; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_737 = lean_ctor_get(x_729, 1);
lean_inc(x_737);
lean_dec(x_729);
x_738 = lean_ctor_get(x_730, 1);
lean_inc(x_738);
lean_dec(x_730);
x_739 = lean_ctor_get(x_731, 0);
lean_inc(x_739);
lean_dec(x_731);
x_17 = x_739;
x_18 = x_738;
x_19 = x_737;
goto block_22;
}
}
else
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_740 = lean_ctor_get(x_729, 0);
lean_inc(x_740);
x_741 = lean_ctor_get(x_729, 1);
lean_inc(x_741);
if (lean_is_exclusive(x_729)) {
 lean_ctor_release(x_729, 0);
 lean_ctor_release(x_729, 1);
 x_742 = x_729;
} else {
 lean_dec_ref(x_729);
 x_742 = lean_box(0);
}
if (lean_is_scalar(x_742)) {
 x_743 = lean_alloc_ctor(1, 2, 0);
} else {
 x_743 = x_742;
}
lean_ctor_set(x_743, 0, x_740);
lean_ctor_set(x_743, 1, x_741);
return x_743;
}
}
}
}
}
}
else
{
lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; uint8_t x_751; lean_object* x_752; 
x_744 = lean_ctor_get(x_33, 1);
lean_inc(x_744);
lean_dec(x_33);
x_745 = lean_st_ref_get(x_15, x_35);
x_746 = lean_ctor_get(x_745, 0);
lean_inc(x_746);
x_747 = lean_ctor_get(x_745, 1);
lean_inc(x_747);
if (lean_is_exclusive(x_745)) {
 lean_ctor_release(x_745, 0);
 lean_ctor_release(x_745, 1);
 x_748 = x_745;
} else {
 lean_dec_ref(x_745);
 x_748 = lean_box(0);
}
x_749 = lean_ctor_get(x_746, 0);
lean_inc(x_749);
lean_dec(x_746);
x_750 = lean_box(0);
x_751 = lean_unbox(x_750);
lean_inc(x_10);
lean_inc(x_749);
x_752 = l_Lean_Environment_find_x3f(x_749, x_10, x_751);
if (lean_obj_tag(x_752) == 0)
{
lean_object* x_753; lean_object* x_754; lean_object* x_755; lean_object* x_756; lean_object* x_757; lean_object* x_758; lean_object* x_759; 
lean_dec(x_749);
lean_dec(x_748);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_753 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_754 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_755 = lean_unsigned_to_nat(338u);
x_756 = lean_unsigned_to_nat(16u);
x_757 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
x_758 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_753, x_754, x_755, x_756, x_757);
lean_dec(x_757);
lean_dec(x_754);
lean_dec(x_753);
x_759 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_758, x_744, x_14, x_15, x_747);
return x_759;
}
else
{
lean_object* x_760; lean_object* x_761; 
x_760 = lean_ctor_get(x_752, 0);
lean_inc(x_760);
if (lean_is_exclusive(x_752)) {
 lean_ctor_release(x_752, 0);
 x_761 = x_752;
} else {
 lean_dec_ref(x_752);
 x_761 = lean_box(0);
}
switch (lean_obj_tag(x_760)) {
case 0:
{
lean_object* x_762; lean_object* x_763; lean_object* x_764; lean_object* x_765; uint8_t x_766; 
lean_dec(x_749);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 x_762 = x_760;
} else {
 lean_dec_ref(x_760);
 x_762 = lean_box(0);
}
x_763 = lean_mk_string_unchecked("Quot", 4, 4);
x_764 = lean_mk_string_unchecked("lcInv", 5, 5);
x_765 = l_Lean_Name_mkStr2(x_763, x_764);
x_766 = lean_name_eq(x_10, x_765);
lean_dec(x_765);
if (x_766 == 0)
{
lean_object* x_767; lean_object* x_768; uint8_t x_769; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_767 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
x_768 = l_Lean_Name_mkStr1(x_767);
x_769 = lean_name_eq(x_10, x_768);
lean_dec(x_768);
if (x_769 == 0)
{
lean_object* x_770; lean_object* x_771; lean_object* x_772; 
lean_dec(x_748);
lean_inc(x_10);
x_770 = l_Lean_IR_ToIR_findDecl___redArg(x_10, x_744, x_15, x_747);
x_771 = lean_ctor_get(x_770, 0);
lean_inc(x_771);
x_772 = lean_ctor_get(x_771, 0);
lean_inc(x_772);
if (lean_obj_tag(x_772) == 0)
{
lean_object* x_773; lean_object* x_774; lean_object* x_775; lean_object* x_776; lean_object* x_777; lean_object* x_778; lean_object* x_779; lean_object* x_780; uint8_t x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_773 = x_771;
} else {
 lean_dec_ref(x_771);
 x_773 = lean_box(0);
}
x_774 = lean_ctor_get(x_770, 1);
lean_inc(x_774);
if (lean_is_exclusive(x_770)) {
 lean_ctor_release(x_770, 0);
 lean_ctor_release(x_770, 1);
 x_775 = x_770;
} else {
 lean_dec_ref(x_770);
 x_775 = lean_box(0);
}
x_776 = lean_box(x_769);
x_777 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_777, 0, x_776);
x_778 = lean_mk_string_unchecked("axiom '", 7, 7);
if (lean_is_scalar(x_762)) {
 x_779 = lean_alloc_ctor(3, 1, 0);
} else {
 x_779 = x_762;
 lean_ctor_set_tag(x_779, 3);
}
lean_ctor_set(x_779, 0, x_778);
x_780 = lean_box(1);
x_781 = lean_unbox(x_780);
x_782 = l_Lean_Name_toString(x_10, x_781, x_777);
if (lean_is_scalar(x_761)) {
 x_783 = lean_alloc_ctor(3, 1, 0);
} else {
 x_783 = x_761;
 lean_ctor_set_tag(x_783, 3);
}
lean_ctor_set(x_783, 0, x_782);
if (lean_is_scalar(x_773)) {
 x_784 = lean_alloc_ctor(5, 2, 0);
} else {
 x_784 = x_773;
 lean_ctor_set_tag(x_784, 5);
}
lean_ctor_set(x_784, 0, x_779);
lean_ctor_set(x_784, 1, x_783);
x_785 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_786 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_786, 0, x_785);
if (lean_is_scalar(x_775)) {
 x_787 = lean_alloc_ctor(5, 2, 0);
} else {
 x_787 = x_775;
 lean_ctor_set_tag(x_787, 5);
}
lean_ctor_set(x_787, 0, x_784);
lean_ctor_set(x_787, 1, x_786);
x_788 = l_Lean_MessageData_ofFormat(x_787);
x_789 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_788, x_14, x_15, x_774);
lean_dec(x_15);
lean_dec(x_14);
return x_789;
}
else
{
lean_object* x_790; lean_object* x_791; lean_object* x_792; lean_object* x_793; lean_object* x_794; lean_object* x_795; lean_object* x_808; 
lean_dec(x_762);
lean_dec(x_761);
x_790 = lean_ctor_get(x_770, 1);
lean_inc(x_790);
lean_dec(x_770);
x_791 = lean_ctor_get(x_771, 1);
lean_inc(x_791);
if (lean_is_exclusive(x_771)) {
 lean_ctor_release(x_771, 0);
 lean_ctor_release(x_771, 1);
 x_792 = x_771;
} else {
 lean_dec_ref(x_771);
 x_792 = lean_box(0);
}
x_793 = lean_ctor_get(x_772, 0);
lean_inc(x_793);
lean_dec(x_772);
x_794 = lean_array_get_size(x_30);
x_808 = lean_ctor_get(x_793, 1);
lean_inc(x_808);
lean_dec(x_793);
x_795 = x_808;
goto block_807;
block_807:
{
lean_object* x_796; uint8_t x_797; 
x_796 = lean_array_get_size(x_795);
lean_dec(x_795);
x_797 = lean_nat_dec_lt(x_794, x_796);
if (x_797 == 0)
{
uint8_t x_798; 
x_798 = lean_nat_dec_eq(x_794, x_796);
if (x_798 == 0)
{
lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; 
lean_dec(x_3);
lean_inc(x_796);
x_799 = l_Array_extract(lean_box(0), x_30, x_24, x_796);
x_800 = l_Array_extract(lean_box(0), x_30, x_796, x_794);
lean_dec(x_30);
if (lean_is_scalar(x_792)) {
 x_801 = lean_alloc_ctor(6, 2, 0);
} else {
 x_801 = x_792;
 lean_ctor_set_tag(x_801, 6);
}
lean_ctor_set(x_801, 0, x_10);
lean_ctor_set(x_801, 1, x_799);
x_802 = lean_apply_6(x_2, x_801, x_800, x_791, x_14, x_15, x_790);
return x_802;
}
else
{
lean_object* x_803; lean_object* x_804; 
lean_dec(x_796);
lean_dec(x_794);
lean_dec(x_2);
if (lean_is_scalar(x_792)) {
 x_803 = lean_alloc_ctor(6, 2, 0);
} else {
 x_803 = x_792;
 lean_ctor_set_tag(x_803, 6);
}
lean_ctor_set(x_803, 0, x_10);
lean_ctor_set(x_803, 1, x_30);
x_804 = lean_apply_5(x_3, x_803, x_791, x_14, x_15, x_790);
return x_804;
}
}
else
{
lean_object* x_805; lean_object* x_806; 
lean_dec(x_796);
lean_dec(x_794);
lean_dec(x_2);
if (lean_is_scalar(x_792)) {
 x_805 = lean_alloc_ctor(7, 2, 0);
} else {
 x_805 = x_792;
 lean_ctor_set_tag(x_805, 7);
}
lean_ctor_set(x_805, 0, x_10);
lean_ctor_set(x_805, 1, x_30);
x_806 = lean_apply_5(x_3, x_805, x_791, x_14, x_15, x_790);
return x_806;
}
}
}
}
else
{
lean_object* x_809; lean_object* x_810; lean_object* x_811; 
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_809 = lean_box(13);
x_810 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_810, 0, x_809);
lean_ctor_set(x_810, 1, x_744);
if (lean_is_scalar(x_748)) {
 x_811 = lean_alloc_ctor(0, 2, 0);
} else {
 x_811 = x_748;
}
lean_ctor_set(x_811, 0, x_810);
lean_ctor_set(x_811, 1, x_747);
return x_811;
}
}
else
{
lean_object* x_812; lean_object* x_813; 
lean_dec(x_762);
lean_dec(x_761);
lean_dec(x_748);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_812 = lean_unsigned_to_nat(2u);
x_813 = lean_array_get(x_4, x_30, x_812);
lean_dec(x_30);
if (lean_obj_tag(x_813) == 0)
{
lean_object* x_814; lean_object* x_815; 
lean_dec(x_6);
x_814 = lean_ctor_get(x_813, 0);
lean_inc(x_814);
lean_dec(x_813);
x_815 = lean_apply_5(x_5, x_814, x_744, x_14, x_15, x_747);
return x_815;
}
else
{
lean_object* x_816; lean_object* x_817; 
lean_dec(x_5);
x_816 = lean_box(0);
x_817 = lean_apply_5(x_6, x_816, x_744, x_14, x_15, x_747);
return x_817;
}
}
}
case 2:
{
lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; 
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_749);
lean_dec(x_748);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_818 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_819 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_820 = lean_unsigned_to_nat(337u);
x_821 = lean_unsigned_to_nat(30u);
x_822 = lean_mk_string_unchecked("thm unsupported by code generator", 33, 33);
x_823 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_818, x_819, x_820, x_821, x_822);
lean_dec(x_822);
lean_dec(x_819);
lean_dec(x_818);
x_824 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_823, x_744, x_14, x_15, x_747);
return x_824;
}
case 4:
{
lean_object* x_825; lean_object* x_826; lean_object* x_827; lean_object* x_828; uint8_t x_829; 
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 x_825 = x_760;
} else {
 lean_dec_ref(x_760);
 x_825 = lean_box(0);
}
x_826 = lean_mk_string_unchecked("Quot", 4, 4);
x_827 = lean_mk_string_unchecked("mk", 2, 2);
x_828 = l_Lean_Name_mkStr2(x_826, x_827);
x_829 = lean_name_eq(x_10, x_828);
lean_dec(x_828);
if (x_829 == 0)
{
lean_object* x_830; lean_object* x_831; lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_744);
lean_dec(x_30);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_830 = lean_box(x_829);
x_831 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_831, 0, x_830);
x_832 = lean_mk_string_unchecked("quot ", 5, 5);
if (lean_is_scalar(x_825)) {
 x_833 = lean_alloc_ctor(3, 1, 0);
} else {
 x_833 = x_825;
 lean_ctor_set_tag(x_833, 3);
}
lean_ctor_set(x_833, 0, x_832);
x_834 = lean_box(1);
x_835 = lean_unbox(x_834);
x_836 = l_Lean_Name_toString(x_10, x_835, x_831);
if (lean_is_scalar(x_761)) {
 x_837 = lean_alloc_ctor(3, 1, 0);
} else {
 x_837 = x_761;
 lean_ctor_set_tag(x_837, 3);
}
lean_ctor_set(x_837, 0, x_836);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_837);
lean_ctor_set(x_27, 0, x_833);
x_838 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
x_839 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_839, 0, x_838);
x_840 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_840, 0, x_27);
lean_ctor_set(x_840, 1, x_839);
x_841 = l_Lean_MessageData_ofFormat(x_840);
x_842 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_841, x_14, x_15, x_747);
lean_dec(x_15);
lean_dec(x_14);
return x_842;
}
else
{
lean_object* x_843; lean_object* x_844; 
lean_dec(x_825);
lean_dec(x_761);
lean_free_object(x_27);
lean_dec(x_10);
x_843 = lean_unsigned_to_nat(2u);
x_844 = lean_array_get(x_4, x_30, x_843);
lean_dec(x_30);
if (lean_obj_tag(x_844) == 0)
{
lean_object* x_845; lean_object* x_846; 
lean_dec(x_6);
x_845 = lean_ctor_get(x_844, 0);
lean_inc(x_845);
lean_dec(x_844);
x_846 = lean_apply_5(x_5, x_845, x_744, x_14, x_15, x_747);
return x_846;
}
else
{
lean_object* x_847; lean_object* x_848; 
lean_dec(x_5);
x_847 = lean_box(0);
x_848 = lean_apply_5(x_6, x_847, x_744, x_14, x_15, x_747);
return x_848;
}
}
}
case 5:
{
lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; 
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_749);
lean_dec(x_748);
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_12);
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
x_849 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_850 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_851 = lean_unsigned_to_nat(336u);
x_852 = lean_unsigned_to_nat(33u);
x_853 = lean_mk_string_unchecked("induct unsupported by code generator", 36, 36);
x_854 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_849, x_850, x_851, x_852, x_853);
lean_dec(x_853);
lean_dec(x_850);
lean_dec(x_849);
x_855 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_854, x_744, x_14, x_15, x_747);
return x_855;
}
case 6:
{
lean_object* x_856; uint8_t x_857; 
lean_dec(x_761);
lean_dec(x_748);
lean_free_object(x_27);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_856 = lean_ctor_get(x_760, 0);
lean_inc(x_856);
lean_dec(x_760);
lean_inc(x_10);
x_857 = l_Lean_isExtern(x_749, x_10);
if (x_857 == 0)
{
lean_object* x_858; 
lean_dec(x_30);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
x_858 = l_Lean_IR_ToIR_getCtorInfo(x_10, x_744, x_14, x_15, x_747);
if (lean_obj_tag(x_858) == 0)
{
lean_object* x_859; lean_object* x_860; lean_object* x_861; lean_object* x_862; lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; lean_object* x_877; lean_object* x_878; lean_object* x_879; lean_object* x_880; lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; 
x_859 = lean_ctor_get(x_858, 0);
lean_inc(x_859);
x_860 = lean_ctor_get(x_859, 0);
lean_inc(x_860);
x_861 = lean_ctor_get(x_858, 1);
lean_inc(x_861);
lean_dec(x_858);
x_862 = lean_ctor_get(x_859, 1);
lean_inc(x_862);
lean_dec(x_859);
x_863 = lean_ctor_get(x_860, 0);
lean_inc(x_863);
x_864 = lean_ctor_get(x_860, 1);
lean_inc(x_864);
lean_dec(x_860);
x_865 = lean_ctor_get(x_856, 3);
lean_inc(x_865);
lean_dec(x_856);
x_866 = lean_array_get_size(x_12);
x_867 = l_Array_extract(lean_box(0), x_12, x_865, x_866);
lean_dec(x_12);
x_868 = lean_mk_empty_array_with_capacity(x_24);
x_869 = lean_array_get_size(x_864);
x_870 = lean_unsigned_to_nat(1u);
x_871 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_871, 0, x_24);
lean_ctor_set(x_871, 1, x_869);
lean_ctor_set(x_871, 2, x_870);
x_872 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_867, x_864, x_857, x_871, x_868, x_24, x_862, x_861);
lean_dec(x_871);
x_873 = lean_ctor_get(x_872, 0);
lean_inc(x_873);
x_874 = lean_ctor_get(x_872, 1);
lean_inc(x_874);
lean_dec(x_872);
x_875 = lean_ctor_get(x_873, 0);
lean_inc(x_875);
x_876 = lean_ctor_get(x_873, 1);
lean_inc(x_876);
lean_dec(x_873);
x_877 = lean_ctor_get(x_7, 0);
lean_inc(x_877);
lean_dec(x_7);
x_878 = l_Lean_IR_ToIR_bindVar___redArg(x_877, x_876, x_874);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
x_880 = lean_ctor_get(x_878, 1);
lean_inc(x_880);
lean_dec(x_878);
x_881 = lean_ctor_get(x_879, 0);
lean_inc(x_881);
x_882 = lean_ctor_get(x_879, 1);
lean_inc(x_882);
if (lean_is_exclusive(x_879)) {
 lean_ctor_release(x_879, 0);
 lean_ctor_release(x_879, 1);
 x_883 = x_879;
} else {
 lean_dec_ref(x_879);
 x_883 = lean_box(0);
}
lean_inc(x_881);
x_884 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_8, x_863, x_864, x_867, x_881, x_882, x_14, x_15, x_880);
lean_dec(x_867);
lean_dec(x_864);
if (lean_obj_tag(x_884) == 0)
{
lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; lean_object* x_895; 
x_885 = lean_ctor_get(x_884, 0);
lean_inc(x_885);
x_886 = lean_ctor_get(x_884, 1);
lean_inc(x_886);
if (lean_is_exclusive(x_884)) {
 lean_ctor_release(x_884, 0);
 lean_ctor_release(x_884, 1);
 x_887 = x_884;
} else {
 lean_dec_ref(x_884);
 x_887 = lean_box(0);
}
x_888 = lean_ctor_get(x_885, 0);
lean_inc(x_888);
x_889 = lean_ctor_get(x_885, 1);
lean_inc(x_889);
if (lean_is_exclusive(x_885)) {
 lean_ctor_release(x_885, 0);
 lean_ctor_release(x_885, 1);
 x_890 = x_885;
} else {
 lean_dec_ref(x_885);
 x_890 = lean_box(0);
}
x_891 = lean_box(7);
if (lean_is_scalar(x_883)) {
 x_892 = lean_alloc_ctor(0, 2, 0);
} else {
 x_892 = x_883;
}
lean_ctor_set(x_892, 0, x_863);
lean_ctor_set(x_892, 1, x_875);
x_893 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_893, 0, x_881);
lean_ctor_set(x_893, 1, x_891);
lean_ctor_set(x_893, 2, x_892);
lean_ctor_set(x_893, 3, x_888);
if (lean_is_scalar(x_890)) {
 x_894 = lean_alloc_ctor(0, 2, 0);
} else {
 x_894 = x_890;
}
lean_ctor_set(x_894, 0, x_893);
lean_ctor_set(x_894, 1, x_889);
if (lean_is_scalar(x_887)) {
 x_895 = lean_alloc_ctor(0, 2, 0);
} else {
 x_895 = x_887;
}
lean_ctor_set(x_895, 0, x_894);
lean_ctor_set(x_895, 1, x_886);
return x_895;
}
else
{
lean_dec(x_883);
lean_dec(x_881);
lean_dec(x_875);
lean_dec(x_863);
return x_884;
}
}
else
{
lean_object* x_896; lean_object* x_897; lean_object* x_898; lean_object* x_899; 
lean_dec(x_856);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_896 = lean_ctor_get(x_858, 0);
lean_inc(x_896);
x_897 = lean_ctor_get(x_858, 1);
lean_inc(x_897);
if (lean_is_exclusive(x_858)) {
 lean_ctor_release(x_858, 0);
 lean_ctor_release(x_858, 1);
 x_898 = x_858;
} else {
 lean_dec_ref(x_858);
 x_898 = lean_box(0);
}
if (lean_is_scalar(x_898)) {
 x_899 = lean_alloc_ctor(1, 2, 0);
} else {
 x_899 = x_898;
}
lean_ctor_set(x_899, 0, x_896);
lean_ctor_set(x_899, 1, x_897);
return x_899;
}
}
else
{
lean_object* x_900; 
lean_dec(x_856);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_900 = lean_apply_6(x_1, x_10, x_30, x_744, x_14, x_15, x_747);
if (lean_obj_tag(x_900) == 0)
{
lean_object* x_901; lean_object* x_902; 
x_901 = lean_ctor_get(x_900, 0);
lean_inc(x_901);
x_902 = lean_ctor_get(x_901, 0);
lean_inc(x_902);
if (lean_obj_tag(x_902) == 0)
{
lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; 
x_903 = lean_ctor_get(x_900, 1);
lean_inc(x_903);
lean_dec(x_900);
x_904 = lean_ctor_get(x_901, 1);
lean_inc(x_904);
if (lean_is_exclusive(x_901)) {
 lean_ctor_release(x_901, 0);
 lean_ctor_release(x_901, 1);
 x_905 = x_901;
} else {
 lean_dec_ref(x_901);
 x_905 = lean_box(0);
}
if (lean_is_scalar(x_905)) {
 x_906 = lean_alloc_ctor(6, 2, 0);
} else {
 x_906 = x_905;
 lean_ctor_set_tag(x_906, 6);
}
lean_ctor_set(x_906, 0, x_10);
lean_ctor_set(x_906, 1, x_30);
x_907 = lean_apply_5(x_3, x_906, x_904, x_14, x_15, x_903);
return x_907;
}
else
{
lean_object* x_908; lean_object* x_909; lean_object* x_910; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_908 = lean_ctor_get(x_900, 1);
lean_inc(x_908);
lean_dec(x_900);
x_909 = lean_ctor_get(x_901, 1);
lean_inc(x_909);
lean_dec(x_901);
x_910 = lean_ctor_get(x_902, 0);
lean_inc(x_910);
lean_dec(x_902);
x_17 = x_910;
x_18 = x_909;
x_19 = x_908;
goto block_22;
}
}
else
{
lean_object* x_911; lean_object* x_912; lean_object* x_913; lean_object* x_914; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_911 = lean_ctor_get(x_900, 0);
lean_inc(x_911);
x_912 = lean_ctor_get(x_900, 1);
lean_inc(x_912);
if (lean_is_exclusive(x_900)) {
 lean_ctor_release(x_900, 0);
 lean_ctor_release(x_900, 1);
 x_913 = x_900;
} else {
 lean_dec_ref(x_900);
 x_913 = lean_box(0);
}
if (lean_is_scalar(x_913)) {
 x_914 = lean_alloc_ctor(1, 2, 0);
} else {
 x_914 = x_913;
}
lean_ctor_set(x_914, 0, x_911);
lean_ctor_set(x_914, 1, x_912);
return x_914;
}
}
}
case 7:
{
lean_object* x_915; lean_object* x_916; lean_object* x_917; lean_object* x_918; uint8_t x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; lean_object* x_923; lean_object* x_924; lean_object* x_925; lean_object* x_926; 
lean_dec(x_749);
lean_dec(x_748);
lean_dec(x_744);
lean_dec(x_30);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_760)) {
 lean_ctor_release(x_760, 0);
 x_915 = x_760;
} else {
 lean_dec_ref(x_760);
 x_915 = lean_box(0);
}
x_916 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
if (lean_is_scalar(x_915)) {
 x_917 = lean_alloc_ctor(3, 1, 0);
} else {
 x_917 = x_915;
 lean_ctor_set_tag(x_917, 3);
}
lean_ctor_set(x_917, 0, x_916);
x_918 = lean_box(1);
x_919 = lean_unbox(x_918);
x_920 = l_Lean_Name_toString(x_10, x_919, x_9);
if (lean_is_scalar(x_761)) {
 x_921 = lean_alloc_ctor(3, 1, 0);
} else {
 x_921 = x_761;
 lean_ctor_set_tag(x_921, 3);
}
lean_ctor_set(x_921, 0, x_920);
lean_ctor_set_tag(x_27, 5);
lean_ctor_set(x_27, 1, x_921);
lean_ctor_set(x_27, 0, x_917);
x_922 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_923 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_923, 0, x_922);
x_924 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_924, 0, x_27);
lean_ctor_set(x_924, 1, x_923);
x_925 = l_Lean_MessageData_ofFormat(x_924);
x_926 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_925, x_14, x_15, x_747);
lean_dec(x_15);
lean_dec(x_14);
return x_926;
}
default: 
{
lean_object* x_927; 
lean_dec(x_761);
lean_dec(x_760);
lean_dec(x_749);
lean_dec(x_748);
lean_free_object(x_27);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_30);
lean_inc(x_10);
x_927 = lean_apply_6(x_1, x_10, x_30, x_744, x_14, x_15, x_747);
if (lean_obj_tag(x_927) == 0)
{
lean_object* x_928; lean_object* x_929; 
x_928 = lean_ctor_get(x_927, 0);
lean_inc(x_928);
x_929 = lean_ctor_get(x_928, 0);
lean_inc(x_929);
if (lean_obj_tag(x_929) == 0)
{
lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
x_930 = lean_ctor_get(x_927, 1);
lean_inc(x_930);
lean_dec(x_927);
x_931 = lean_ctor_get(x_928, 1);
lean_inc(x_931);
if (lean_is_exclusive(x_928)) {
 lean_ctor_release(x_928, 0);
 lean_ctor_release(x_928, 1);
 x_932 = x_928;
} else {
 lean_dec_ref(x_928);
 x_932 = lean_box(0);
}
if (lean_is_scalar(x_932)) {
 x_933 = lean_alloc_ctor(6, 2, 0);
} else {
 x_933 = x_932;
 lean_ctor_set_tag(x_933, 6);
}
lean_ctor_set(x_933, 0, x_10);
lean_ctor_set(x_933, 1, x_30);
x_934 = lean_apply_5(x_3, x_933, x_931, x_14, x_15, x_930);
return x_934;
}
else
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_935 = lean_ctor_get(x_927, 1);
lean_inc(x_935);
lean_dec(x_927);
x_936 = lean_ctor_get(x_928, 1);
lean_inc(x_936);
lean_dec(x_928);
x_937 = lean_ctor_get(x_929, 0);
lean_inc(x_937);
lean_dec(x_929);
x_17 = x_937;
x_18 = x_936;
x_19 = x_935;
goto block_22;
}
}
else
{
lean_object* x_938; lean_object* x_939; lean_object* x_940; lean_object* x_941; 
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_938 = lean_ctor_get(x_927, 0);
lean_inc(x_938);
x_939 = lean_ctor_get(x_927, 1);
lean_inc(x_939);
if (lean_is_exclusive(x_927)) {
 lean_ctor_release(x_927, 0);
 lean_ctor_release(x_927, 1);
 x_940 = x_927;
} else {
 lean_dec_ref(x_927);
 x_940 = lean_box(0);
}
if (lean_is_scalar(x_940)) {
 x_941 = lean_alloc_ctor(1, 2, 0);
} else {
 x_941 = x_940;
}
lean_ctor_set(x_941, 0, x_938);
lean_ctor_set(x_941, 1, x_939);
return x_941;
}
}
}
}
}
}
else
{
lean_object* x_942; lean_object* x_943; lean_object* x_944; 
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
x_942 = lean_ctor_get(x_32, 1);
lean_inc(x_942);
lean_dec(x_32);
x_943 = lean_ctor_get(x_33, 1);
lean_inc(x_943);
lean_dec(x_33);
x_944 = lean_ctor_get(x_34, 0);
lean_inc(x_944);
lean_dec(x_34);
x_17 = x_944;
x_18 = x_943;
x_19 = x_942;
goto block_22;
}
}
else
{
uint8_t x_945; 
lean_free_object(x_27);
lean_dec(x_30);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
x_945 = !lean_is_exclusive(x_32);
if (x_945 == 0)
{
return x_32;
}
else
{
lean_object* x_946; lean_object* x_947; lean_object* x_948; 
x_946 = lean_ctor_get(x_32, 0);
x_947 = lean_ctor_get(x_32, 1);
lean_inc(x_947);
lean_inc(x_946);
lean_dec(x_32);
x_948 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_948, 0, x_946);
lean_ctor_set(x_948, 1, x_947);
return x_948;
}
}
}
else
{
lean_object* x_949; lean_object* x_950; lean_object* x_951; 
x_949 = lean_ctor_get(x_27, 0);
x_950 = lean_ctor_get(x_27, 1);
lean_inc(x_950);
lean_inc(x_949);
lean_dec(x_27);
lean_inc(x_1);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_949);
lean_inc(x_10);
x_951 = lean_apply_6(x_1, x_10, x_949, x_950, x_14, x_15, x_28);
if (lean_obj_tag(x_951) == 0)
{
lean_object* x_952; lean_object* x_953; 
x_952 = lean_ctor_get(x_951, 0);
lean_inc(x_952);
x_953 = lean_ctor_get(x_952, 0);
lean_inc(x_953);
if (lean_obj_tag(x_953) == 0)
{
lean_object* x_954; lean_object* x_955; lean_object* x_956; lean_object* x_957; lean_object* x_958; lean_object* x_959; lean_object* x_960; lean_object* x_961; lean_object* x_962; uint8_t x_963; lean_object* x_964; 
x_954 = lean_ctor_get(x_951, 1);
lean_inc(x_954);
lean_dec(x_951);
x_955 = lean_ctor_get(x_952, 1);
lean_inc(x_955);
if (lean_is_exclusive(x_952)) {
 lean_ctor_release(x_952, 0);
 lean_ctor_release(x_952, 1);
 x_956 = x_952;
} else {
 lean_dec_ref(x_952);
 x_956 = lean_box(0);
}
x_957 = lean_st_ref_get(x_15, x_954);
x_958 = lean_ctor_get(x_957, 0);
lean_inc(x_958);
x_959 = lean_ctor_get(x_957, 1);
lean_inc(x_959);
if (lean_is_exclusive(x_957)) {
 lean_ctor_release(x_957, 0);
 lean_ctor_release(x_957, 1);
 x_960 = x_957;
} else {
 lean_dec_ref(x_957);
 x_960 = lean_box(0);
}
x_961 = lean_ctor_get(x_958, 0);
lean_inc(x_961);
lean_dec(x_958);
x_962 = lean_box(0);
x_963 = lean_unbox(x_962);
lean_inc(x_10);
lean_inc(x_961);
x_964 = l_Lean_Environment_find_x3f(x_961, x_10, x_963);
if (lean_obj_tag(x_964) == 0)
{
lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; lean_object* x_969; lean_object* x_970; lean_object* x_971; 
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_949);
lean_dec(x_12);
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
x_965 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_966 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_967 = lean_unsigned_to_nat(338u);
x_968 = lean_unsigned_to_nat(16u);
x_969 = lean_mk_string_unchecked("reference to unbound name", 25, 25);
x_970 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_965, x_966, x_967, x_968, x_969);
lean_dec(x_969);
lean_dec(x_966);
lean_dec(x_965);
x_971 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_970, x_955, x_14, x_15, x_959);
return x_971;
}
else
{
lean_object* x_972; lean_object* x_973; 
x_972 = lean_ctor_get(x_964, 0);
lean_inc(x_972);
if (lean_is_exclusive(x_964)) {
 lean_ctor_release(x_964, 0);
 x_973 = x_964;
} else {
 lean_dec_ref(x_964);
 x_973 = lean_box(0);
}
switch (lean_obj_tag(x_972)) {
case 0:
{
lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; uint8_t x_978; 
lean_dec(x_961);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_1);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 x_974 = x_972;
} else {
 lean_dec_ref(x_972);
 x_974 = lean_box(0);
}
x_975 = lean_mk_string_unchecked("Quot", 4, 4);
x_976 = lean_mk_string_unchecked("lcInv", 5, 5);
x_977 = l_Lean_Name_mkStr2(x_975, x_976);
x_978 = lean_name_eq(x_10, x_977);
lean_dec(x_977);
if (x_978 == 0)
{
lean_object* x_979; lean_object* x_980; uint8_t x_981; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_979 = lean_mk_string_unchecked("lcUnreachable", 13, 13);
x_980 = l_Lean_Name_mkStr1(x_979);
x_981 = lean_name_eq(x_10, x_980);
lean_dec(x_980);
if (x_981 == 0)
{
lean_object* x_982; lean_object* x_983; lean_object* x_984; 
lean_dec(x_960);
lean_dec(x_956);
lean_inc(x_10);
x_982 = l_Lean_IR_ToIR_findDecl___redArg(x_10, x_955, x_15, x_959);
x_983 = lean_ctor_get(x_982, 0);
lean_inc(x_983);
x_984 = lean_ctor_get(x_983, 0);
lean_inc(x_984);
if (lean_obj_tag(x_984) == 0)
{
lean_object* x_985; lean_object* x_986; lean_object* x_987; lean_object* x_988; lean_object* x_989; lean_object* x_990; lean_object* x_991; lean_object* x_992; uint8_t x_993; lean_object* x_994; lean_object* x_995; lean_object* x_996; lean_object* x_997; lean_object* x_998; lean_object* x_999; lean_object* x_1000; lean_object* x_1001; 
lean_dec(x_949);
lean_dec(x_3);
lean_dec(x_2);
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 lean_ctor_release(x_983, 1);
 x_985 = x_983;
} else {
 lean_dec_ref(x_983);
 x_985 = lean_box(0);
}
x_986 = lean_ctor_get(x_982, 1);
lean_inc(x_986);
if (lean_is_exclusive(x_982)) {
 lean_ctor_release(x_982, 0);
 lean_ctor_release(x_982, 1);
 x_987 = x_982;
} else {
 lean_dec_ref(x_982);
 x_987 = lean_box(0);
}
x_988 = lean_box(x_981);
x_989 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_989, 0, x_988);
x_990 = lean_mk_string_unchecked("axiom '", 7, 7);
if (lean_is_scalar(x_974)) {
 x_991 = lean_alloc_ctor(3, 1, 0);
} else {
 x_991 = x_974;
 lean_ctor_set_tag(x_991, 3);
}
lean_ctor_set(x_991, 0, x_990);
x_992 = lean_box(1);
x_993 = lean_unbox(x_992);
x_994 = l_Lean_Name_toString(x_10, x_993, x_989);
if (lean_is_scalar(x_973)) {
 x_995 = lean_alloc_ctor(3, 1, 0);
} else {
 x_995 = x_973;
 lean_ctor_set_tag(x_995, 3);
}
lean_ctor_set(x_995, 0, x_994);
if (lean_is_scalar(x_985)) {
 x_996 = lean_alloc_ctor(5, 2, 0);
} else {
 x_996 = x_985;
 lean_ctor_set_tag(x_996, 5);
}
lean_ctor_set(x_996, 0, x_991);
lean_ctor_set(x_996, 1, x_995);
x_997 = lean_mk_string_unchecked("' not supported by code generator; consider marking definition as 'noncomputable'", 81, 81);
x_998 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_998, 0, x_997);
if (lean_is_scalar(x_987)) {
 x_999 = lean_alloc_ctor(5, 2, 0);
} else {
 x_999 = x_987;
 lean_ctor_set_tag(x_999, 5);
}
lean_ctor_set(x_999, 0, x_996);
lean_ctor_set(x_999, 1, x_998);
x_1000 = l_Lean_MessageData_ofFormat(x_999);
x_1001 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1000, x_14, x_15, x_986);
lean_dec(x_15);
lean_dec(x_14);
return x_1001;
}
else
{
lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; lean_object* x_1007; lean_object* x_1020; 
lean_dec(x_974);
lean_dec(x_973);
x_1002 = lean_ctor_get(x_982, 1);
lean_inc(x_1002);
lean_dec(x_982);
x_1003 = lean_ctor_get(x_983, 1);
lean_inc(x_1003);
if (lean_is_exclusive(x_983)) {
 lean_ctor_release(x_983, 0);
 lean_ctor_release(x_983, 1);
 x_1004 = x_983;
} else {
 lean_dec_ref(x_983);
 x_1004 = lean_box(0);
}
x_1005 = lean_ctor_get(x_984, 0);
lean_inc(x_1005);
lean_dec(x_984);
x_1006 = lean_array_get_size(x_949);
x_1020 = lean_ctor_get(x_1005, 1);
lean_inc(x_1020);
lean_dec(x_1005);
x_1007 = x_1020;
goto block_1019;
block_1019:
{
lean_object* x_1008; uint8_t x_1009; 
x_1008 = lean_array_get_size(x_1007);
lean_dec(x_1007);
x_1009 = lean_nat_dec_lt(x_1006, x_1008);
if (x_1009 == 0)
{
uint8_t x_1010; 
x_1010 = lean_nat_dec_eq(x_1006, x_1008);
if (x_1010 == 0)
{
lean_object* x_1011; lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; 
lean_dec(x_3);
lean_inc(x_1008);
x_1011 = l_Array_extract(lean_box(0), x_949, x_24, x_1008);
x_1012 = l_Array_extract(lean_box(0), x_949, x_1008, x_1006);
lean_dec(x_949);
if (lean_is_scalar(x_1004)) {
 x_1013 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1013 = x_1004;
 lean_ctor_set_tag(x_1013, 6);
}
lean_ctor_set(x_1013, 0, x_10);
lean_ctor_set(x_1013, 1, x_1011);
x_1014 = lean_apply_6(x_2, x_1013, x_1012, x_1003, x_14, x_15, x_1002);
return x_1014;
}
else
{
lean_object* x_1015; lean_object* x_1016; 
lean_dec(x_1008);
lean_dec(x_1006);
lean_dec(x_2);
if (lean_is_scalar(x_1004)) {
 x_1015 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1015 = x_1004;
 lean_ctor_set_tag(x_1015, 6);
}
lean_ctor_set(x_1015, 0, x_10);
lean_ctor_set(x_1015, 1, x_949);
x_1016 = lean_apply_5(x_3, x_1015, x_1003, x_14, x_15, x_1002);
return x_1016;
}
}
else
{
lean_object* x_1017; lean_object* x_1018; 
lean_dec(x_1008);
lean_dec(x_1006);
lean_dec(x_2);
if (lean_is_scalar(x_1004)) {
 x_1017 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1017 = x_1004;
 lean_ctor_set_tag(x_1017, 7);
}
lean_ctor_set(x_1017, 0, x_10);
lean_ctor_set(x_1017, 1, x_949);
x_1018 = lean_apply_5(x_3, x_1017, x_1003, x_14, x_15, x_1002);
return x_1018;
}
}
}
}
else
{
lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; 
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_949);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_1021 = lean_box(13);
if (lean_is_scalar(x_956)) {
 x_1022 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1022 = x_956;
}
lean_ctor_set(x_1022, 0, x_1021);
lean_ctor_set(x_1022, 1, x_955);
if (lean_is_scalar(x_960)) {
 x_1023 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1023 = x_960;
}
lean_ctor_set(x_1023, 0, x_1022);
lean_ctor_set(x_1023, 1, x_959);
return x_1023;
}
}
else
{
lean_object* x_1024; lean_object* x_1025; 
lean_dec(x_974);
lean_dec(x_973);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_10);
lean_dec(x_3);
lean_dec(x_2);
x_1024 = lean_unsigned_to_nat(2u);
x_1025 = lean_array_get(x_4, x_949, x_1024);
lean_dec(x_949);
if (lean_obj_tag(x_1025) == 0)
{
lean_object* x_1026; lean_object* x_1027; 
lean_dec(x_6);
x_1026 = lean_ctor_get(x_1025, 0);
lean_inc(x_1026);
lean_dec(x_1025);
x_1027 = lean_apply_5(x_5, x_1026, x_955, x_14, x_15, x_959);
return x_1027;
}
else
{
lean_object* x_1028; lean_object* x_1029; 
lean_dec(x_5);
x_1028 = lean_box(0);
x_1029 = lean_apply_5(x_6, x_1028, x_955, x_14, x_15, x_959);
return x_1029;
}
}
}
case 2:
{
lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; 
lean_dec(x_973);
lean_dec(x_972);
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_949);
lean_dec(x_12);
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
x_1030 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_1031 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_1032 = lean_unsigned_to_nat(337u);
x_1033 = lean_unsigned_to_nat(30u);
x_1034 = lean_mk_string_unchecked("thm unsupported by code generator", 33, 33);
x_1035 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1030, x_1031, x_1032, x_1033, x_1034);
lean_dec(x_1034);
lean_dec(x_1031);
lean_dec(x_1030);
x_1036 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_1035, x_955, x_14, x_15, x_959);
return x_1036;
}
case 4:
{
lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; uint8_t x_1041; 
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 x_1037 = x_972;
} else {
 lean_dec_ref(x_972);
 x_1037 = lean_box(0);
}
x_1038 = lean_mk_string_unchecked("Quot", 4, 4);
x_1039 = lean_mk_string_unchecked("mk", 2, 2);
x_1040 = l_Lean_Name_mkStr2(x_1038, x_1039);
x_1041 = lean_name_eq(x_10, x_1040);
lean_dec(x_1040);
if (x_1041 == 0)
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; lean_object* x_1045; lean_object* x_1046; uint8_t x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; 
lean_dec(x_955);
lean_dec(x_949);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
x_1042 = lean_box(x_1041);
x_1043 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__6___boxed), 2, 1);
lean_closure_set(x_1043, 0, x_1042);
x_1044 = lean_mk_string_unchecked("quot ", 5, 5);
if (lean_is_scalar(x_1037)) {
 x_1045 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1045 = x_1037;
 lean_ctor_set_tag(x_1045, 3);
}
lean_ctor_set(x_1045, 0, x_1044);
x_1046 = lean_box(1);
x_1047 = lean_unbox(x_1046);
x_1048 = l_Lean_Name_toString(x_10, x_1047, x_1043);
if (lean_is_scalar(x_973)) {
 x_1049 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1049 = x_973;
 lean_ctor_set_tag(x_1049, 3);
}
lean_ctor_set(x_1049, 0, x_1048);
x_1050 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1050, 0, x_1045);
lean_ctor_set(x_1050, 1, x_1049);
x_1051 = lean_mk_string_unchecked(" unsupported by code generator", 30, 30);
x_1052 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1052, 0, x_1051);
x_1053 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1053, 0, x_1050);
lean_ctor_set(x_1053, 1, x_1052);
x_1054 = l_Lean_MessageData_ofFormat(x_1053);
x_1055 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1054, x_14, x_15, x_959);
lean_dec(x_15);
lean_dec(x_14);
return x_1055;
}
else
{
lean_object* x_1056; lean_object* x_1057; 
lean_dec(x_1037);
lean_dec(x_973);
lean_dec(x_10);
x_1056 = lean_unsigned_to_nat(2u);
x_1057 = lean_array_get(x_4, x_949, x_1056);
lean_dec(x_949);
if (lean_obj_tag(x_1057) == 0)
{
lean_object* x_1058; lean_object* x_1059; 
lean_dec(x_6);
x_1058 = lean_ctor_get(x_1057, 0);
lean_inc(x_1058);
lean_dec(x_1057);
x_1059 = lean_apply_5(x_5, x_1058, x_955, x_14, x_15, x_959);
return x_1059;
}
else
{
lean_object* x_1060; lean_object* x_1061; 
lean_dec(x_5);
x_1060 = lean_box(0);
x_1061 = lean_apply_5(x_6, x_1060, x_955, x_14, x_15, x_959);
return x_1061;
}
}
}
case 5:
{
lean_object* x_1062; lean_object* x_1063; lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; lean_object* x_1067; lean_object* x_1068; 
lean_dec(x_973);
lean_dec(x_972);
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_949);
lean_dec(x_12);
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
x_1062 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_1063 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_1064 = lean_unsigned_to_nat(336u);
x_1065 = lean_unsigned_to_nat(33u);
x_1066 = lean_mk_string_unchecked("induct unsupported by code generator", 36, 36);
x_1067 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_1062, x_1063, x_1064, x_1065, x_1066);
lean_dec(x_1066);
lean_dec(x_1063);
lean_dec(x_1062);
x_1068 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_1067, x_955, x_14, x_15, x_959);
return x_1068;
}
case 6:
{
lean_object* x_1069; uint8_t x_1070; 
lean_dec(x_973);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
x_1069 = lean_ctor_get(x_972, 0);
lean_inc(x_1069);
lean_dec(x_972);
lean_inc(x_10);
x_1070 = l_Lean_isExtern(x_961, x_10);
if (x_1070 == 0)
{
lean_object* x_1071; 
lean_dec(x_949);
lean_dec(x_3);
lean_dec(x_1);
lean_inc(x_15);
lean_inc(x_14);
x_1071 = l_Lean_IR_ToIR_getCtorInfo(x_10, x_955, x_14, x_15, x_959);
if (lean_obj_tag(x_1071) == 0)
{
lean_object* x_1072; lean_object* x_1073; lean_object* x_1074; lean_object* x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; lean_object* x_1080; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; lean_object* x_1086; lean_object* x_1087; lean_object* x_1088; lean_object* x_1089; lean_object* x_1090; lean_object* x_1091; lean_object* x_1092; lean_object* x_1093; lean_object* x_1094; lean_object* x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1072 = lean_ctor_get(x_1071, 0);
lean_inc(x_1072);
x_1073 = lean_ctor_get(x_1072, 0);
lean_inc(x_1073);
x_1074 = lean_ctor_get(x_1071, 1);
lean_inc(x_1074);
lean_dec(x_1071);
x_1075 = lean_ctor_get(x_1072, 1);
lean_inc(x_1075);
lean_dec(x_1072);
x_1076 = lean_ctor_get(x_1073, 0);
lean_inc(x_1076);
x_1077 = lean_ctor_get(x_1073, 1);
lean_inc(x_1077);
lean_dec(x_1073);
x_1078 = lean_ctor_get(x_1069, 3);
lean_inc(x_1078);
lean_dec(x_1069);
x_1079 = lean_array_get_size(x_12);
x_1080 = l_Array_extract(lean_box(0), x_12, x_1078, x_1079);
lean_dec(x_12);
x_1081 = lean_mk_empty_array_with_capacity(x_24);
x_1082 = lean_array_get_size(x_1077);
x_1083 = lean_unsigned_to_nat(1u);
x_1084 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_1084, 0, x_24);
lean_ctor_set(x_1084, 1, x_1082);
lean_ctor_set(x_1084, 2, x_1083);
x_1085 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_1080, x_1077, x_1070, x_1084, x_1081, x_24, x_1075, x_1074);
lean_dec(x_1084);
x_1086 = lean_ctor_get(x_1085, 0);
lean_inc(x_1086);
x_1087 = lean_ctor_get(x_1085, 1);
lean_inc(x_1087);
lean_dec(x_1085);
x_1088 = lean_ctor_get(x_1086, 0);
lean_inc(x_1088);
x_1089 = lean_ctor_get(x_1086, 1);
lean_inc(x_1089);
lean_dec(x_1086);
x_1090 = lean_ctor_get(x_7, 0);
lean_inc(x_1090);
lean_dec(x_7);
x_1091 = l_Lean_IR_ToIR_bindVar___redArg(x_1090, x_1089, x_1087);
x_1092 = lean_ctor_get(x_1091, 0);
lean_inc(x_1092);
x_1093 = lean_ctor_get(x_1091, 1);
lean_inc(x_1093);
lean_dec(x_1091);
x_1094 = lean_ctor_get(x_1092, 0);
lean_inc(x_1094);
x_1095 = lean_ctor_get(x_1092, 1);
lean_inc(x_1095);
if (lean_is_exclusive(x_1092)) {
 lean_ctor_release(x_1092, 0);
 lean_ctor_release(x_1092, 1);
 x_1096 = x_1092;
} else {
 lean_dec_ref(x_1092);
 x_1096 = lean_box(0);
}
lean_inc(x_1094);
x_1097 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_8, x_1076, x_1077, x_1080, x_1094, x_1095, x_14, x_15, x_1093);
lean_dec(x_1080);
lean_dec(x_1077);
if (lean_obj_tag(x_1097) == 0)
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; lean_object* x_1104; lean_object* x_1105; lean_object* x_1106; lean_object* x_1107; lean_object* x_1108; 
x_1098 = lean_ctor_get(x_1097, 0);
lean_inc(x_1098);
x_1099 = lean_ctor_get(x_1097, 1);
lean_inc(x_1099);
if (lean_is_exclusive(x_1097)) {
 lean_ctor_release(x_1097, 0);
 lean_ctor_release(x_1097, 1);
 x_1100 = x_1097;
} else {
 lean_dec_ref(x_1097);
 x_1100 = lean_box(0);
}
x_1101 = lean_ctor_get(x_1098, 0);
lean_inc(x_1101);
x_1102 = lean_ctor_get(x_1098, 1);
lean_inc(x_1102);
if (lean_is_exclusive(x_1098)) {
 lean_ctor_release(x_1098, 0);
 lean_ctor_release(x_1098, 1);
 x_1103 = x_1098;
} else {
 lean_dec_ref(x_1098);
 x_1103 = lean_box(0);
}
x_1104 = lean_box(7);
if (lean_is_scalar(x_1096)) {
 x_1105 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1105 = x_1096;
}
lean_ctor_set(x_1105, 0, x_1076);
lean_ctor_set(x_1105, 1, x_1088);
x_1106 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_1106, 0, x_1094);
lean_ctor_set(x_1106, 1, x_1104);
lean_ctor_set(x_1106, 2, x_1105);
lean_ctor_set(x_1106, 3, x_1101);
if (lean_is_scalar(x_1103)) {
 x_1107 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1107 = x_1103;
}
lean_ctor_set(x_1107, 0, x_1106);
lean_ctor_set(x_1107, 1, x_1102);
if (lean_is_scalar(x_1100)) {
 x_1108 = lean_alloc_ctor(0, 2, 0);
} else {
 x_1108 = x_1100;
}
lean_ctor_set(x_1108, 0, x_1107);
lean_ctor_set(x_1108, 1, x_1099);
return x_1108;
}
else
{
lean_dec(x_1096);
lean_dec(x_1094);
lean_dec(x_1088);
lean_dec(x_1076);
return x_1097;
}
}
else
{
lean_object* x_1109; lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; 
lean_dec(x_1069);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
x_1109 = lean_ctor_get(x_1071, 0);
lean_inc(x_1109);
x_1110 = lean_ctor_get(x_1071, 1);
lean_inc(x_1110);
if (lean_is_exclusive(x_1071)) {
 lean_ctor_release(x_1071, 0);
 lean_ctor_release(x_1071, 1);
 x_1111 = x_1071;
} else {
 lean_dec_ref(x_1071);
 x_1111 = lean_box(0);
}
if (lean_is_scalar(x_1111)) {
 x_1112 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1112 = x_1111;
}
lean_ctor_set(x_1112, 0, x_1109);
lean_ctor_set(x_1112, 1, x_1110);
return x_1112;
}
}
else
{
lean_object* x_1113; 
lean_dec(x_1069);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_949);
lean_inc(x_10);
x_1113 = lean_apply_6(x_1, x_10, x_949, x_955, x_14, x_15, x_959);
if (lean_obj_tag(x_1113) == 0)
{
lean_object* x_1114; lean_object* x_1115; 
x_1114 = lean_ctor_get(x_1113, 0);
lean_inc(x_1114);
x_1115 = lean_ctor_get(x_1114, 0);
lean_inc(x_1115);
if (lean_obj_tag(x_1115) == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; 
x_1116 = lean_ctor_get(x_1113, 1);
lean_inc(x_1116);
lean_dec(x_1113);
x_1117 = lean_ctor_get(x_1114, 1);
lean_inc(x_1117);
if (lean_is_exclusive(x_1114)) {
 lean_ctor_release(x_1114, 0);
 lean_ctor_release(x_1114, 1);
 x_1118 = x_1114;
} else {
 lean_dec_ref(x_1114);
 x_1118 = lean_box(0);
}
if (lean_is_scalar(x_1118)) {
 x_1119 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1119 = x_1118;
 lean_ctor_set_tag(x_1119, 6);
}
lean_ctor_set(x_1119, 0, x_10);
lean_ctor_set(x_1119, 1, x_949);
x_1120 = lean_apply_5(x_3, x_1119, x_1117, x_14, x_15, x_1116);
return x_1120;
}
else
{
lean_object* x_1121; lean_object* x_1122; lean_object* x_1123; 
lean_dec(x_949);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_1121 = lean_ctor_get(x_1113, 1);
lean_inc(x_1121);
lean_dec(x_1113);
x_1122 = lean_ctor_get(x_1114, 1);
lean_inc(x_1122);
lean_dec(x_1114);
x_1123 = lean_ctor_get(x_1115, 0);
lean_inc(x_1123);
lean_dec(x_1115);
x_17 = x_1123;
x_18 = x_1122;
x_19 = x_1121;
goto block_22;
}
}
else
{
lean_object* x_1124; lean_object* x_1125; lean_object* x_1126; lean_object* x_1127; 
lean_dec(x_949);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_1124 = lean_ctor_get(x_1113, 0);
lean_inc(x_1124);
x_1125 = lean_ctor_get(x_1113, 1);
lean_inc(x_1125);
if (lean_is_exclusive(x_1113)) {
 lean_ctor_release(x_1113, 0);
 lean_ctor_release(x_1113, 1);
 x_1126 = x_1113;
} else {
 lean_dec_ref(x_1113);
 x_1126 = lean_box(0);
}
if (lean_is_scalar(x_1126)) {
 x_1127 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1127 = x_1126;
}
lean_ctor_set(x_1127, 0, x_1124);
lean_ctor_set(x_1127, 1, x_1125);
return x_1127;
}
}
}
case 7:
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; uint8_t x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_955);
lean_dec(x_949);
lean_dec(x_12);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
if (lean_is_exclusive(x_972)) {
 lean_ctor_release(x_972, 0);
 x_1128 = x_972;
} else {
 lean_dec_ref(x_972);
 x_1128 = lean_box(0);
}
x_1129 = lean_mk_string_unchecked("code generator does not support recursor '", 42, 42);
if (lean_is_scalar(x_1128)) {
 x_1130 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1130 = x_1128;
 lean_ctor_set_tag(x_1130, 3);
}
lean_ctor_set(x_1130, 0, x_1129);
x_1131 = lean_box(1);
x_1132 = lean_unbox(x_1131);
x_1133 = l_Lean_Name_toString(x_10, x_1132, x_9);
if (lean_is_scalar(x_973)) {
 x_1134 = lean_alloc_ctor(3, 1, 0);
} else {
 x_1134 = x_973;
 lean_ctor_set_tag(x_1134, 3);
}
lean_ctor_set(x_1134, 0, x_1133);
x_1135 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1135, 0, x_1130);
lean_ctor_set(x_1135, 1, x_1134);
x_1136 = lean_mk_string_unchecked("' yet, consider using 'match ... with' and/or structural recursion", 66, 66);
x_1137 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_1137, 0, x_1136);
x_1138 = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(x_1138, 0, x_1135);
lean_ctor_set(x_1138, 1, x_1137);
x_1139 = l_Lean_MessageData_ofFormat(x_1138);
x_1140 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1139, x_14, x_15, x_959);
lean_dec(x_15);
lean_dec(x_14);
return x_1140;
}
default: 
{
lean_object* x_1141; 
lean_dec(x_973);
lean_dec(x_972);
lean_dec(x_961);
lean_dec(x_960);
lean_dec(x_956);
lean_dec(x_12);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_inc(x_15);
lean_inc(x_14);
lean_inc(x_949);
lean_inc(x_10);
x_1141 = lean_apply_6(x_1, x_10, x_949, x_955, x_14, x_15, x_959);
if (lean_obj_tag(x_1141) == 0)
{
lean_object* x_1142; lean_object* x_1143; 
x_1142 = lean_ctor_get(x_1141, 0);
lean_inc(x_1142);
x_1143 = lean_ctor_get(x_1142, 0);
lean_inc(x_1143);
if (lean_obj_tag(x_1143) == 0)
{
lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; 
x_1144 = lean_ctor_get(x_1141, 1);
lean_inc(x_1144);
lean_dec(x_1141);
x_1145 = lean_ctor_get(x_1142, 1);
lean_inc(x_1145);
if (lean_is_exclusive(x_1142)) {
 lean_ctor_release(x_1142, 0);
 lean_ctor_release(x_1142, 1);
 x_1146 = x_1142;
} else {
 lean_dec_ref(x_1142);
 x_1146 = lean_box(0);
}
if (lean_is_scalar(x_1146)) {
 x_1147 = lean_alloc_ctor(6, 2, 0);
} else {
 x_1147 = x_1146;
 lean_ctor_set_tag(x_1147, 6);
}
lean_ctor_set(x_1147, 0, x_10);
lean_ctor_set(x_1147, 1, x_949);
x_1148 = lean_apply_5(x_3, x_1147, x_1145, x_14, x_15, x_1144);
return x_1148;
}
else
{
lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; 
lean_dec(x_949);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_1149 = lean_ctor_get(x_1141, 1);
lean_inc(x_1149);
lean_dec(x_1141);
x_1150 = lean_ctor_get(x_1142, 1);
lean_inc(x_1150);
lean_dec(x_1142);
x_1151 = lean_ctor_get(x_1143, 0);
lean_inc(x_1151);
lean_dec(x_1143);
x_17 = x_1151;
x_18 = x_1150;
x_19 = x_1149;
goto block_22;
}
}
else
{
lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; 
lean_dec(x_949);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_3);
x_1152 = lean_ctor_get(x_1141, 0);
lean_inc(x_1152);
x_1153 = lean_ctor_get(x_1141, 1);
lean_inc(x_1153);
if (lean_is_exclusive(x_1141)) {
 lean_ctor_release(x_1141, 0);
 lean_ctor_release(x_1141, 1);
 x_1154 = x_1141;
} else {
 lean_dec_ref(x_1141);
 x_1154 = lean_box(0);
}
if (lean_is_scalar(x_1154)) {
 x_1155 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1155 = x_1154;
}
lean_ctor_set(x_1155, 0, x_1152);
lean_ctor_set(x_1155, 1, x_1153);
return x_1155;
}
}
}
}
}
else
{
lean_object* x_1156; lean_object* x_1157; lean_object* x_1158; 
lean_dec(x_949);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
x_1156 = lean_ctor_get(x_951, 1);
lean_inc(x_1156);
lean_dec(x_951);
x_1157 = lean_ctor_get(x_952, 1);
lean_inc(x_1157);
lean_dec(x_952);
x_1158 = lean_ctor_get(x_953, 0);
lean_inc(x_1158);
lean_dec(x_953);
x_17 = x_1158;
x_18 = x_1157;
x_19 = x_1156;
goto block_22;
}
}
else
{
lean_object* x_1159; lean_object* x_1160; lean_object* x_1161; lean_object* x_1162; 
lean_dec(x_949);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
x_1159 = lean_ctor_get(x_951, 0);
lean_inc(x_1159);
x_1160 = lean_ctor_get(x_951, 1);
lean_inc(x_1160);
if (lean_is_exclusive(x_951)) {
 lean_ctor_release(x_951, 0);
 lean_ctor_release(x_951, 1);
 x_1161 = x_951;
} else {
 lean_dec_ref(x_951);
 x_1161 = lean_box(0);
}
if (lean_is_scalar(x_1161)) {
 x_1162 = lean_alloc_ctor(1, 2, 0);
} else {
 x_1162 = x_1161;
}
lean_ctor_set(x_1162, 0, x_1159);
lean_ctor_set(x_1162, 1, x_1160);
return x_1162;
}
}
}
else
{
uint8_t x_1163; 
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_12);
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
x_1163 = !lean_is_exclusive(x_26);
if (x_1163 == 0)
{
return x_26;
}
else
{
lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; 
x_1164 = lean_ctor_get(x_26, 0);
x_1165 = lean_ctor_get(x_26, 1);
lean_inc(x_1165);
lean_inc(x_1164);
lean_dec(x_26);
x_1166 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_1166, 0, x_1164);
lean_ctor_set(x_1166, 1, x_1165);
return x_1166;
}
}
block_22:
{
lean_object* x_20; lean_object* x_21; 
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_17);
lean_ctor_set(x_20, 1, x_18);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_19);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
lean_inc(x_2);
lean_inc(x_1);
x_7 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__0___boxed), 7, 2);
lean_closure_set(x_7, 0, x_1);
lean_closure_set(x_7, 1, x_2);
lean_inc(x_2);
lean_inc(x_1);
x_8 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__1), 7, 2);
lean_closure_set(x_8, 0, x_1);
lean_closure_set(x_8, 1, x_2);
x_9 = lean_ctor_get(x_1, 3);
lean_inc(x_9);
switch (lean_obj_tag(x_9)) {
case 0:
{
uint8_t x_10; 
lean_dec(x_8);
lean_dec(x_7);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = l_Lean_IR_ToIR_lowerLitValue(x_11);
lean_ctor_set_tag(x_9, 11);
lean_ctor_set(x_9, 0, x_12);
x_13 = l_Lean_IR_ToIR_lowerLet___lam__1(x_1, x_2, x_9, x_3, x_4, x_5, x_6);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_9, 0);
lean_inc(x_14);
lean_dec(x_9);
x_15 = l_Lean_IR_ToIR_lowerLitValue(x_14);
x_16 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_IR_ToIR_lowerLet___lam__1(x_1, x_2, x_16, x_3, x_4, x_5, x_6);
return x_17;
}
}
case 1:
{
lean_object* x_18; lean_object* x_19; 
lean_dec(x_8);
lean_dec(x_7);
x_18 = lean_box(0);
x_19 = l_Lean_IR_ToIR_lowerLet___lam__0(x_1, x_2, x_18, x_3, x_4, x_5, x_6);
return x_19;
}
case 2:
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint64_t x_26; lean_object* x_27; uint64_t x_28; uint64_t x_29; uint64_t x_30; lean_object* x_31; uint64_t x_32; uint64_t x_33; uint64_t x_34; size_t x_35; size_t x_36; lean_object* x_37; size_t x_38; size_t x_39; size_t x_40; lean_object* x_41; lean_object* x_42; 
lean_dec(x_8);
lean_dec(x_7);
x_20 = lean_ctor_get(x_3, 0);
lean_inc(x_20);
x_21 = lean_ctor_get(x_9, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_9, 1);
lean_inc(x_22);
x_23 = lean_ctor_get(x_9, 2);
lean_inc(x_23);
lean_dec(x_9);
x_24 = lean_ctor_get(x_20, 1);
lean_inc(x_24);
lean_dec(x_20);
x_25 = lean_array_get_size(x_24);
x_26 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_23);
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
x_42 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_23, x_41);
lean_dec(x_41);
lean_dec(x_23);
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; 
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_43 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_44 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_45 = lean_unsigned_to_nat(247u);
x_46 = lean_unsigned_to_nat(37u);
x_47 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_48 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_43, x_44, x_45, x_46, x_47);
lean_dec(x_47);
lean_dec(x_44);
lean_dec(x_43);
x_49 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_48, x_3, x_4, x_5, x_6);
return x_49;
}
else
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_42, 0);
lean_inc(x_50);
lean_dec(x_42);
switch (lean_obj_tag(x_50)) {
case 0:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_66; lean_object* x_67; uint8_t x_68; lean_object* x_69; 
x_51 = lean_ctor_get(x_50, 0);
lean_inc(x_51);
lean_dec(x_50);
x_52 = lean_st_ref_get(x_5, x_6);
x_53 = lean_ctor_get(x_52, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_52, 1);
lean_inc(x_54);
lean_dec(x_52);
x_66 = lean_ctor_get(x_53, 0);
lean_inc(x_66);
lean_dec(x_53);
x_67 = lean_box(0);
x_68 = lean_unbox(x_67);
x_69 = l_Lean_Environment_find_x3f(x_66, x_21, x_68);
if (lean_obj_tag(x_69) == 0)
{
lean_dec(x_51);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
goto block_65;
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec(x_69);
if (lean_obj_tag(x_70) == 5)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
lean_dec(x_70);
x_72 = lean_ctor_get(x_71, 4);
lean_inc(x_72);
lean_dec(x_71);
x_73 = lean_box(0);
x_74 = lean_unsigned_to_nat(0u);
x_75 = l___private_Init_GetElem_0__List_get_x21Internal___redArg(x_73, x_72, x_74);
lean_dec(x_72);
lean_inc(x_5);
lean_inc(x_4);
x_76 = l_Lean_IR_ToIR_getCtorInfo(x_75, x_3, x_4, x_5, x_54);
if (lean_obj_tag(x_76) == 0)
{
lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_77 = lean_ctor_get(x_76, 0);
lean_inc(x_77);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
x_79 = lean_ctor_get(x_76, 1);
lean_inc(x_79);
lean_dec(x_76);
x_80 = lean_ctor_get(x_77, 1);
lean_inc(x_80);
lean_dec(x_77);
x_81 = lean_ctor_get(x_78, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_78, 1);
lean_inc(x_82);
lean_dec(x_78);
x_83 = lean_box(0);
x_84 = lean_array_get(x_83, x_82, x_22);
lean_dec(x_22);
lean_dec(x_82);
x_85 = l_Lean_IR_ToIR_lowerProj(x_51, x_81, x_84);
lean_dec(x_81);
x_86 = lean_ctor_get(x_85, 0);
lean_inc(x_86);
if (lean_obj_tag(x_86) == 0)
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_87 = lean_ctor_get(x_85, 1);
lean_inc(x_87);
lean_dec(x_85);
x_88 = lean_ctor_get(x_86, 0);
lean_inc(x_88);
lean_dec(x_86);
x_89 = lean_ctor_get(x_1, 0);
lean_inc(x_89);
lean_dec(x_1);
x_90 = l_Lean_IR_ToIR_bindVar___redArg(x_89, x_80, x_79);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
lean_dec(x_90);
x_93 = lean_ctor_get(x_91, 0);
lean_inc(x_93);
x_94 = lean_ctor_get(x_91, 1);
lean_inc(x_94);
lean_dec(x_91);
x_95 = l_Lean_IR_ToIR_lowerCode(x_2, x_94, x_4, x_5, x_92);
if (lean_obj_tag(x_95) == 0)
{
uint8_t x_96; 
x_96 = !lean_is_exclusive(x_95);
if (x_96 == 0)
{
lean_object* x_97; uint8_t x_98; 
x_97 = lean_ctor_get(x_95, 0);
x_98 = !lean_is_exclusive(x_97);
if (x_98 == 0)
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_ctor_get(x_97, 0);
x_100 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_100, 0, x_93);
lean_ctor_set(x_100, 1, x_87);
lean_ctor_set(x_100, 2, x_88);
lean_ctor_set(x_100, 3, x_99);
lean_ctor_set(x_97, 0, x_100);
return x_95;
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = lean_ctor_get(x_97, 0);
x_102 = lean_ctor_get(x_97, 1);
lean_inc(x_102);
lean_inc(x_101);
lean_dec(x_97);
x_103 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_103, 0, x_93);
lean_ctor_set(x_103, 1, x_87);
lean_ctor_set(x_103, 2, x_88);
lean_ctor_set(x_103, 3, x_101);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_102);
lean_ctor_set(x_95, 0, x_104);
return x_95;
}
}
else
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; 
x_105 = lean_ctor_get(x_95, 0);
x_106 = lean_ctor_get(x_95, 1);
lean_inc(x_106);
lean_inc(x_105);
lean_dec(x_95);
x_107 = lean_ctor_get(x_105, 0);
lean_inc(x_107);
x_108 = lean_ctor_get(x_105, 1);
lean_inc(x_108);
if (lean_is_exclusive(x_105)) {
 lean_ctor_release(x_105, 0);
 lean_ctor_release(x_105, 1);
 x_109 = x_105;
} else {
 lean_dec_ref(x_105);
 x_109 = lean_box(0);
}
x_110 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_110, 0, x_93);
lean_ctor_set(x_110, 1, x_87);
lean_ctor_set(x_110, 2, x_88);
lean_ctor_set(x_110, 3, x_107);
if (lean_is_scalar(x_109)) {
 x_111 = lean_alloc_ctor(0, 2, 0);
} else {
 x_111 = x_109;
}
lean_ctor_set(x_111, 0, x_110);
lean_ctor_set(x_111, 1, x_108);
x_112 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_112, 0, x_111);
lean_ctor_set(x_112, 1, x_106);
return x_112;
}
}
else
{
lean_dec(x_93);
lean_dec(x_88);
lean_dec(x_87);
return x_95;
}
}
else
{
lean_object* x_113; lean_object* x_114; 
lean_dec(x_85);
x_113 = lean_box(0);
x_114 = l_Lean_IR_ToIR_lowerLet___lam__0(x_1, x_2, x_113, x_80, x_4, x_5, x_79);
return x_114;
}
}
else
{
uint8_t x_115; 
lean_dec(x_51);
lean_dec(x_22);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_115 = !lean_is_exclusive(x_76);
if (x_115 == 0)
{
return x_76;
}
else
{
lean_object* x_116; lean_object* x_117; lean_object* x_118; 
x_116 = lean_ctor_get(x_76, 0);
x_117 = lean_ctor_get(x_76, 1);
lean_inc(x_117);
lean_inc(x_116);
lean_dec(x_76);
x_118 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_118, 0, x_116);
lean_ctor_set(x_118, 1, x_117);
return x_118;
}
}
}
else
{
lean_dec(x_70);
lean_dec(x_51);
lean_dec(x_22);
lean_dec(x_2);
lean_dec(x_1);
x_55 = x_3;
x_56 = x_4;
x_57 = x_5;
goto block_65;
}
}
block_65:
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_58 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_59 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_60 = lean_unsigned_to_nat(233u);
x_61 = lean_unsigned_to_nat(10u);
x_62 = lean_mk_string_unchecked("projection of non-inductive type", 32, 32);
x_63 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_58, x_59, x_60, x_61, x_62);
lean_dec(x_62);
lean_dec(x_59);
lean_dec(x_58);
x_64 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_63, x_55, x_56, x_57, x_54);
return x_64;
}
}
case 1:
{
lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; 
lean_dec(x_50);
lean_dec(x_22);
lean_dec(x_21);
lean_dec(x_2);
lean_dec(x_1);
x_119 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_120 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_121 = lean_unsigned_to_nat(247u);
x_122 = lean_unsigned_to_nat(37u);
x_123 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_124 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_119, x_120, x_121, x_122, x_123);
lean_dec(x_123);
lean_dec(x_120);
lean_dec(x_119);
x_125 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_124, x_3, x_4, x_5, x_6);
return x_125;
}
default: 
{
lean_object* x_126; lean_object* x_127; 
lean_dec(x_22);
lean_dec(x_21);
x_126 = lean_box(0);
x_127 = l_Lean_IR_ToIR_lowerLet___lam__0(x_1, x_2, x_126, x_3, x_4, x_5, x_6);
return x_127;
}
}
}
}
case 3:
{
lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_128 = lean_ctor_get(x_9, 0);
lean_inc(x_128);
x_129 = lean_ctor_get(x_9, 1);
lean_inc(x_129);
x_130 = lean_ctor_get(x_9, 2);
lean_inc(x_130);
lean_dec(x_9);
x_131 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__2___boxed), 1, 0);
lean_inc(x_2);
lean_inc(x_1);
x_132 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__3), 8, 2);
lean_closure_set(x_132, 0, x_1);
lean_closure_set(x_132, 1, x_2);
lean_inc(x_8);
lean_inc(x_132);
x_133 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__4), 8, 2);
lean_closure_set(x_133, 0, x_132);
lean_closure_set(x_133, 1, x_8);
lean_inc(x_2);
lean_inc(x_1);
x_134 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerLet___lam__5), 7, 2);
lean_closure_set(x_134, 0, x_1);
lean_closure_set(x_134, 1, x_2);
x_135 = l_Lean_IR_instInhabitedArg;
if (lean_obj_tag(x_128) == 1)
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; 
x_136 = lean_ctor_get(x_128, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_128, 1);
lean_inc(x_137);
lean_dec(x_128);
x_138 = lean_box(0);
switch (lean_obj_tag(x_136)) {
case 0:
{
lean_object* x_139; lean_object* x_140; 
x_139 = l_Lean_Name_str___override(x_138, x_137);
x_140 = l_Lean_IR_ToIR_lowerLet___lam__8(x_133, x_132, x_8, x_135, x_134, x_7, x_1, x_2, x_131, x_139, x_129, x_130, x_3, x_4, x_5, x_6);
lean_dec(x_129);
return x_140;
}
case 1:
{
lean_object* x_141; 
x_141 = lean_ctor_get(x_136, 0);
lean_inc(x_141);
switch (lean_obj_tag(x_141)) {
case 0:
{
lean_object* x_142; lean_object* x_143; uint8_t x_144; 
x_142 = lean_ctor_get(x_136, 1);
lean_inc(x_142);
lean_dec(x_136);
x_143 = lean_mk_string_unchecked("Nat", 3, 3);
x_144 = lean_string_dec_eq(x_142, x_143);
if (x_144 == 0)
{
lean_object* x_145; lean_object* x_146; lean_object* x_147; 
lean_dec(x_143);
x_145 = l_Lean_Name_str___override(x_138, x_142);
x_146 = l_Lean_Name_str___override(x_145, x_137);
x_147 = l_Lean_IR_ToIR_lowerLet___lam__8(x_133, x_132, x_8, x_135, x_134, x_7, x_1, x_2, x_131, x_146, x_129, x_130, x_3, x_4, x_5, x_6);
lean_dec(x_129);
return x_147;
}
else
{
lean_object* x_148; uint8_t x_149; 
lean_dec(x_142);
x_148 = lean_mk_string_unchecked("succ", 4, 4);
x_149 = lean_string_dec_eq(x_137, x_148);
lean_dec(x_148);
if (x_149 == 0)
{
lean_object* x_150; lean_object* x_151; lean_object* x_152; 
x_150 = l_Lean_Name_str___override(x_138, x_143);
x_151 = l_Lean_Name_str___override(x_150, x_137);
x_152 = l_Lean_IR_ToIR_lowerLet___lam__8(x_133, x_132, x_8, x_135, x_134, x_7, x_1, x_2, x_131, x_151, x_129, x_130, x_3, x_4, x_5, x_6);
lean_dec(x_129);
return x_152;
}
else
{
size_t x_153; lean_object* x_154; size_t x_155; lean_object* x_156; 
lean_dec(x_137);
lean_dec(x_134);
lean_dec(x_133);
lean_dec(x_132);
lean_dec(x_131);
lean_dec(x_129);
lean_dec(x_8);
lean_dec(x_7);
x_153 = lean_array_size(x_130);
x_154 = lean_unsigned_to_nat(0u);
x_155 = lean_usize_of_nat(x_154);
lean_inc(x_5);
lean_inc(x_4);
x_156 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_153, x_155, x_130, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; uint8_t x_170; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
lean_dec(x_157);
x_161 = lean_ctor_get(x_1, 0);
lean_inc(x_161);
lean_dec(x_1);
x_162 = l_Lean_IR_ToIR_bindVar___redArg(x_161, x_160, x_158);
x_163 = lean_ctor_get(x_162, 0);
lean_inc(x_163);
x_164 = lean_ctor_get(x_162, 1);
lean_inc(x_164);
lean_dec(x_162);
x_165 = lean_ctor_get(x_163, 0);
lean_inc(x_165);
x_166 = lean_ctor_get(x_163, 1);
lean_inc(x_166);
lean_dec(x_163);
x_167 = l_Lean_IR_ToIR_newVar___redArg(x_166, x_164);
lean_dec(x_166);
x_168 = lean_ctor_get(x_167, 0);
lean_inc(x_168);
x_169 = lean_ctor_get(x_167, 1);
lean_inc(x_169);
lean_dec(x_167);
x_170 = !lean_is_exclusive(x_168);
if (x_170 == 0)
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_ctor_get(x_168, 0);
x_172 = lean_ctor_get(x_168, 1);
x_173 = l_Lean_IR_ToIR_lowerCode(x_2, x_172, x_4, x_5, x_169);
if (lean_obj_tag(x_173) == 0)
{
uint8_t x_174; 
x_174 = !lean_is_exclusive(x_173);
if (x_174 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = lean_ctor_get(x_173, 0);
x_176 = !lean_is_exclusive(x_175);
if (x_176 == 0)
{
lean_object* x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; 
x_177 = lean_ctor_get(x_175, 0);
x_178 = lean_box(7);
x_179 = lean_mk_string_unchecked("add", 3, 3);
x_180 = l_Lean_Name_mkStr2(x_143, x_179);
x_181 = lean_array_get(x_135, x_159, x_154);
lean_dec(x_159);
lean_inc(x_171);
x_182 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_182, 0, x_171);
x_183 = lean_unsigned_to_nat(2u);
x_184 = lean_mk_empty_array_with_capacity(x_183);
x_185 = lean_array_push(x_184, x_181);
x_186 = lean_array_push(x_185, x_182);
lean_ctor_set_tag(x_168, 6);
lean_ctor_set(x_168, 1, x_186);
lean_ctor_set(x_168, 0, x_180);
x_187 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_187, 0, x_165);
lean_ctor_set(x_187, 1, x_178);
lean_ctor_set(x_187, 2, x_168);
lean_ctor_set(x_187, 3, x_177);
x_188 = lean_unsigned_to_nat(1u);
x_189 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_189, 0, x_188);
x_190 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_190, 0, x_189);
x_191 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_191, 0, x_171);
lean_ctor_set(x_191, 1, x_178);
lean_ctor_set(x_191, 2, x_190);
lean_ctor_set(x_191, 3, x_187);
lean_ctor_set(x_175, 0, x_191);
return x_173;
}
else
{
lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; 
x_192 = lean_ctor_get(x_175, 0);
x_193 = lean_ctor_get(x_175, 1);
lean_inc(x_193);
lean_inc(x_192);
lean_dec(x_175);
x_194 = lean_box(7);
x_195 = lean_mk_string_unchecked("add", 3, 3);
x_196 = l_Lean_Name_mkStr2(x_143, x_195);
x_197 = lean_array_get(x_135, x_159, x_154);
lean_dec(x_159);
lean_inc(x_171);
x_198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_198, 0, x_171);
x_199 = lean_unsigned_to_nat(2u);
x_200 = lean_mk_empty_array_with_capacity(x_199);
x_201 = lean_array_push(x_200, x_197);
x_202 = lean_array_push(x_201, x_198);
lean_ctor_set_tag(x_168, 6);
lean_ctor_set(x_168, 1, x_202);
lean_ctor_set(x_168, 0, x_196);
x_203 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_203, 0, x_165);
lean_ctor_set(x_203, 1, x_194);
lean_ctor_set(x_203, 2, x_168);
lean_ctor_set(x_203, 3, x_192);
x_204 = lean_unsigned_to_nat(1u);
x_205 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_205, 0, x_204);
x_206 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_206, 0, x_205);
x_207 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_207, 0, x_171);
lean_ctor_set(x_207, 1, x_194);
lean_ctor_set(x_207, 2, x_206);
lean_ctor_set(x_207, 3, x_203);
x_208 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_208, 0, x_207);
lean_ctor_set(x_208, 1, x_193);
lean_ctor_set(x_173, 0, x_208);
return x_173;
}
}
else
{
lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; 
x_209 = lean_ctor_get(x_173, 0);
x_210 = lean_ctor_get(x_173, 1);
lean_inc(x_210);
lean_inc(x_209);
lean_dec(x_173);
x_211 = lean_ctor_get(x_209, 0);
lean_inc(x_211);
x_212 = lean_ctor_get(x_209, 1);
lean_inc(x_212);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_213 = x_209;
} else {
 lean_dec_ref(x_209);
 x_213 = lean_box(0);
}
x_214 = lean_box(7);
x_215 = lean_mk_string_unchecked("add", 3, 3);
x_216 = l_Lean_Name_mkStr2(x_143, x_215);
x_217 = lean_array_get(x_135, x_159, x_154);
lean_dec(x_159);
lean_inc(x_171);
x_218 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_218, 0, x_171);
x_219 = lean_unsigned_to_nat(2u);
x_220 = lean_mk_empty_array_with_capacity(x_219);
x_221 = lean_array_push(x_220, x_217);
x_222 = lean_array_push(x_221, x_218);
lean_ctor_set_tag(x_168, 6);
lean_ctor_set(x_168, 1, x_222);
lean_ctor_set(x_168, 0, x_216);
x_223 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_223, 0, x_165);
lean_ctor_set(x_223, 1, x_214);
lean_ctor_set(x_223, 2, x_168);
lean_ctor_set(x_223, 3, x_211);
x_224 = lean_unsigned_to_nat(1u);
x_225 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_225, 0, x_224);
x_226 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_226, 0, x_225);
x_227 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_227, 0, x_171);
lean_ctor_set(x_227, 1, x_214);
lean_ctor_set(x_227, 2, x_226);
lean_ctor_set(x_227, 3, x_223);
if (lean_is_scalar(x_213)) {
 x_228 = lean_alloc_ctor(0, 2, 0);
} else {
 x_228 = x_213;
}
lean_ctor_set(x_228, 0, x_227);
lean_ctor_set(x_228, 1, x_212);
x_229 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_229, 0, x_228);
lean_ctor_set(x_229, 1, x_210);
return x_229;
}
}
else
{
lean_free_object(x_168);
lean_dec(x_171);
lean_dec(x_165);
lean_dec(x_159);
lean_dec(x_143);
return x_173;
}
}
else
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; 
x_230 = lean_ctor_get(x_168, 0);
x_231 = lean_ctor_get(x_168, 1);
lean_inc(x_231);
lean_inc(x_230);
lean_dec(x_168);
x_232 = l_Lean_IR_ToIR_lowerCode(x_2, x_231, x_4, x_5, x_169);
if (lean_obj_tag(x_232) == 0)
{
lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; 
x_233 = lean_ctor_get(x_232, 0);
lean_inc(x_233);
x_234 = lean_ctor_get(x_232, 1);
lean_inc(x_234);
if (lean_is_exclusive(x_232)) {
 lean_ctor_release(x_232, 0);
 lean_ctor_release(x_232, 1);
 x_235 = x_232;
} else {
 lean_dec_ref(x_232);
 x_235 = lean_box(0);
}
x_236 = lean_ctor_get(x_233, 0);
lean_inc(x_236);
x_237 = lean_ctor_get(x_233, 1);
lean_inc(x_237);
if (lean_is_exclusive(x_233)) {
 lean_ctor_release(x_233, 0);
 lean_ctor_release(x_233, 1);
 x_238 = x_233;
} else {
 lean_dec_ref(x_233);
 x_238 = lean_box(0);
}
x_239 = lean_box(7);
x_240 = lean_mk_string_unchecked("add", 3, 3);
x_241 = l_Lean_Name_mkStr2(x_143, x_240);
x_242 = lean_array_get(x_135, x_159, x_154);
lean_dec(x_159);
lean_inc(x_230);
x_243 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_243, 0, x_230);
x_244 = lean_unsigned_to_nat(2u);
x_245 = lean_mk_empty_array_with_capacity(x_244);
x_246 = lean_array_push(x_245, x_242);
x_247 = lean_array_push(x_246, x_243);
x_248 = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(x_248, 0, x_241);
lean_ctor_set(x_248, 1, x_247);
x_249 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_249, 0, x_165);
lean_ctor_set(x_249, 1, x_239);
lean_ctor_set(x_249, 2, x_248);
lean_ctor_set(x_249, 3, x_236);
x_250 = lean_unsigned_to_nat(1u);
x_251 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_251, 0, x_250);
x_252 = lean_alloc_ctor(11, 1, 0);
lean_ctor_set(x_252, 0, x_251);
x_253 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_253, 0, x_230);
lean_ctor_set(x_253, 1, x_239);
lean_ctor_set(x_253, 2, x_252);
lean_ctor_set(x_253, 3, x_249);
if (lean_is_scalar(x_238)) {
 x_254 = lean_alloc_ctor(0, 2, 0);
} else {
 x_254 = x_238;
}
lean_ctor_set(x_254, 0, x_253);
lean_ctor_set(x_254, 1, x_237);
if (lean_is_scalar(x_235)) {
 x_255 = lean_alloc_ctor(0, 2, 0);
} else {
 x_255 = x_235;
}
lean_ctor_set(x_255, 0, x_254);
lean_ctor_set(x_255, 1, x_234);
return x_255;
}
else
{
lean_dec(x_230);
lean_dec(x_165);
lean_dec(x_159);
lean_dec(x_143);
return x_232;
}
}
}
else
{
uint8_t x_256; 
lean_dec(x_143);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_256 = !lean_is_exclusive(x_156);
if (x_256 == 0)
{
return x_156;
}
else
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; 
x_257 = lean_ctor_get(x_156, 0);
x_258 = lean_ctor_get(x_156, 1);
lean_inc(x_258);
lean_inc(x_257);
lean_dec(x_156);
x_259 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_259, 0, x_257);
lean_ctor_set(x_259, 1, x_258);
return x_259;
}
}
}
}
}
case 1:
{
lean_object* x_260; lean_object* x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; 
x_260 = lean_ctor_get(x_136, 1);
lean_inc(x_260);
lean_dec(x_136);
x_261 = lean_ctor_get(x_141, 0);
lean_inc(x_261);
x_262 = lean_ctor_get(x_141, 1);
lean_inc(x_262);
lean_dec(x_141);
x_263 = l_Lean_Name_str___override(x_261, x_262);
x_264 = l_Lean_Name_str___override(x_263, x_260);
x_265 = l_Lean_Name_str___override(x_264, x_137);
x_266 = l_Lean_IR_ToIR_lowerLet___lam__8(x_133, x_132, x_8, x_135, x_134, x_7, x_1, x_2, x_131, x_265, x_129, x_130, x_3, x_4, x_5, x_6);
lean_dec(x_129);
return x_266;
}
default: 
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; 
x_267 = lean_ctor_get(x_136, 1);
lean_inc(x_267);
lean_dec(x_136);
x_268 = lean_ctor_get(x_141, 0);
lean_inc(x_268);
x_269 = lean_ctor_get(x_141, 1);
lean_inc(x_269);
lean_dec(x_141);
x_270 = l_Lean_Name_num___override(x_268, x_269);
x_271 = l_Lean_Name_str___override(x_270, x_267);
x_272 = l_Lean_Name_str___override(x_271, x_137);
x_273 = l_Lean_IR_ToIR_lowerLet___lam__8(x_133, x_132, x_8, x_135, x_134, x_7, x_1, x_2, x_131, x_272, x_129, x_130, x_3, x_4, x_5, x_6);
lean_dec(x_129);
return x_273;
}
}
}
default: 
{
lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; 
x_274 = lean_ctor_get(x_136, 0);
lean_inc(x_274);
x_275 = lean_ctor_get(x_136, 1);
lean_inc(x_275);
lean_dec(x_136);
x_276 = l_Lean_Name_num___override(x_274, x_275);
x_277 = l_Lean_Name_str___override(x_276, x_137);
x_278 = l_Lean_IR_ToIR_lowerLet___lam__8(x_133, x_132, x_8, x_135, x_134, x_7, x_1, x_2, x_131, x_277, x_129, x_130, x_3, x_4, x_5, x_6);
lean_dec(x_129);
return x_278;
}
}
}
else
{
lean_object* x_279; 
x_279 = l_Lean_IR_ToIR_lowerLet___lam__8(x_133, x_132, x_8, x_135, x_134, x_7, x_1, x_2, x_131, x_128, x_129, x_130, x_3, x_4, x_5, x_6);
lean_dec(x_129);
return x_279;
}
}
default: 
{
lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; uint64_t x_285; lean_object* x_286; uint64_t x_287; uint64_t x_288; uint64_t x_289; lean_object* x_290; uint64_t x_291; uint64_t x_292; uint64_t x_293; size_t x_294; size_t x_295; lean_object* x_296; size_t x_297; size_t x_298; size_t x_299; lean_object* x_300; lean_object* x_301; 
lean_dec(x_8);
lean_dec(x_7);
x_280 = lean_ctor_get(x_3, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_9, 0);
lean_inc(x_281);
x_282 = lean_ctor_get(x_9, 1);
lean_inc(x_282);
lean_dec(x_9);
x_283 = lean_ctor_get(x_280, 1);
lean_inc(x_283);
lean_dec(x_280);
x_284 = lean_array_get_size(x_283);
x_285 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_281);
x_286 = lean_unsigned_to_nat(32u);
x_287 = lean_uint64_of_nat(x_286);
x_288 = lean_uint64_shift_right(x_285, x_287);
x_289 = lean_uint64_xor(x_285, x_288);
x_290 = lean_unsigned_to_nat(16u);
x_291 = lean_uint64_of_nat(x_290);
x_292 = lean_uint64_shift_right(x_289, x_291);
x_293 = lean_uint64_xor(x_289, x_292);
x_294 = lean_uint64_to_usize(x_293);
x_295 = lean_usize_of_nat(x_284);
lean_dec(x_284);
x_296 = lean_unsigned_to_nat(1u);
x_297 = lean_usize_of_nat(x_296);
x_298 = lean_usize_sub(x_295, x_297);
x_299 = lean_usize_land(x_294, x_298);
x_300 = lean_array_uget(x_283, x_299);
lean_dec(x_283);
x_301 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_281, x_300);
lean_dec(x_300);
lean_dec(x_281);
if (lean_obj_tag(x_301) == 0)
{
lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; 
lean_dec(x_282);
lean_dec(x_2);
lean_dec(x_1);
x_302 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_303 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_304 = lean_unsigned_to_nat(345u);
x_305 = lean_unsigned_to_nat(37u);
x_306 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_307 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_302, x_303, x_304, x_305, x_306);
lean_dec(x_306);
lean_dec(x_303);
lean_dec(x_302);
x_308 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_307, x_3, x_4, x_5, x_6);
return x_308;
}
else
{
lean_object* x_309; 
x_309 = lean_ctor_get(x_301, 0);
lean_inc(x_309);
lean_dec(x_301);
switch (lean_obj_tag(x_309)) {
case 0:
{
lean_object* x_310; size_t x_311; lean_object* x_312; size_t x_313; lean_object* x_314; 
x_310 = lean_ctor_get(x_309, 0);
lean_inc(x_310);
lean_dec(x_309);
x_311 = lean_array_size(x_282);
x_312 = lean_unsigned_to_nat(0u);
x_313 = lean_usize_of_nat(x_312);
lean_inc(x_5);
lean_inc(x_4);
x_314 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_311, x_313, x_282, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_314) == 0)
{
lean_object* x_315; lean_object* x_316; uint8_t x_317; 
x_315 = lean_ctor_get(x_314, 0);
lean_inc(x_315);
x_316 = lean_ctor_get(x_314, 1);
lean_inc(x_316);
lean_dec(x_314);
x_317 = !lean_is_exclusive(x_315);
if (x_317 == 0)
{
lean_object* x_318; lean_object* x_319; lean_object* x_320; 
x_318 = lean_ctor_get(x_315, 0);
x_319 = lean_ctor_get(x_315, 1);
lean_ctor_set_tag(x_315, 8);
lean_ctor_set(x_315, 1, x_318);
lean_ctor_set(x_315, 0, x_310);
x_320 = l_Lean_IR_ToIR_lowerLet___lam__1(x_1, x_2, x_315, x_319, x_4, x_5, x_316);
return x_320;
}
else
{
lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; 
x_321 = lean_ctor_get(x_315, 0);
x_322 = lean_ctor_get(x_315, 1);
lean_inc(x_322);
lean_inc(x_321);
lean_dec(x_315);
x_323 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_323, 0, x_310);
lean_ctor_set(x_323, 1, x_321);
x_324 = l_Lean_IR_ToIR_lowerLet___lam__1(x_1, x_2, x_323, x_322, x_4, x_5, x_316);
return x_324;
}
}
else
{
uint8_t x_325; 
lean_dec(x_310);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
x_325 = !lean_is_exclusive(x_314);
if (x_325 == 0)
{
return x_314;
}
else
{
lean_object* x_326; lean_object* x_327; lean_object* x_328; 
x_326 = lean_ctor_get(x_314, 0);
x_327 = lean_ctor_get(x_314, 1);
lean_inc(x_327);
lean_inc(x_326);
lean_dec(x_314);
x_328 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_328, 0, x_326);
lean_ctor_set(x_328, 1, x_327);
return x_328;
}
}
}
case 1:
{
lean_object* x_329; lean_object* x_330; lean_object* x_331; lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_309);
lean_dec(x_282);
lean_dec(x_2);
lean_dec(x_1);
x_329 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_330 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerLet", 21, 21);
x_331 = lean_unsigned_to_nat(345u);
x_332 = lean_unsigned_to_nat(37u);
x_333 = lean_mk_string_unchecked("unexpected value", 16, 16);
x_334 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_329, x_330, x_331, x_332, x_333);
lean_dec(x_333);
lean_dec(x_330);
lean_dec(x_329);
x_335 = l_panic___at___Lean_IR_ToIR_lowerAlt_loop_spec__0(x_334, x_3, x_4, x_5, x_6);
return x_335;
}
default: 
{
lean_object* x_336; lean_object* x_337; 
lean_dec(x_282);
x_336 = lean_box(0);
x_337 = l_Lean_IR_ToIR_lowerLet___lam__0(x_1, x_2, x_336, x_3, x_4, x_5, x_6);
return x_337;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_10, x_10, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_7, x_8, x_9, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_20; uint8_t x_21; 
x_20 = lean_array_get_size(x_4);
x_21 = lean_nat_dec_lt(x_7, x_20);
lean_dec(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_7);
lean_dec(x_5);
x_22 = l_Lean_IR_ToIR_lowerCode(x_1, x_8, x_9, x_10, x_11);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = lean_array_fget(x_4, x_7);
if (lean_obj_tag(x_23) == 1)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint64_t x_28; lean_object* x_29; uint64_t x_30; uint64_t x_31; uint64_t x_32; lean_object* x_33; uint64_t x_34; uint64_t x_35; uint64_t x_36; size_t x_37; size_t x_38; lean_object* x_39; size_t x_40; size_t x_41; size_t x_42; lean_object* x_43; lean_object* x_44; 
x_24 = lean_ctor_get(x_8, 0);
lean_inc(x_24);
x_25 = lean_ctor_get(x_23, 0);
lean_inc(x_25);
lean_dec(x_23);
x_26 = lean_ctor_get(x_24, 1);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_array_get_size(x_26);
x_28 = l___private_Lean_Expr_0__Lean_hashFVarId____x40_Lean_Expr___hyg_1730_(x_25);
x_29 = lean_unsigned_to_nat(32u);
x_30 = lean_uint64_of_nat(x_29);
x_31 = lean_uint64_shift_right(x_28, x_30);
x_32 = lean_uint64_xor(x_28, x_31);
x_33 = lean_unsigned_to_nat(16u);
x_34 = lean_uint64_of_nat(x_33);
x_35 = lean_uint64_shift_right(x_32, x_34);
x_36 = lean_uint64_xor(x_32, x_35);
x_37 = lean_uint64_to_usize(x_36);
x_38 = lean_usize_of_nat(x_27);
lean_dec(x_27);
x_39 = lean_unsigned_to_nat(1u);
x_40 = lean_usize_of_nat(x_39);
x_41 = lean_usize_sub(x_38, x_40);
x_42 = lean_usize_land(x_37, x_41);
x_43 = lean_array_uget(x_26, x_42);
lean_dec(x_26);
x_44 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___Lean_Compiler_LCNF_getType_spec__0___redArg(x_25, x_43);
lean_dec(x_43);
lean_dec(x_25);
if (lean_obj_tag(x_44) == 0)
{
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
x_15 = x_11;
goto block_19;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_44, 0);
lean_inc(x_45);
lean_dec(x_44);
if (lean_obj_tag(x_45) == 0)
{
lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_46 = lean_ctor_get(x_45, 0);
lean_inc(x_46);
lean_dec(x_45);
x_47 = lean_box(0);
x_48 = lean_array_get(x_47, x_3, x_7);
switch (lean_obj_tag(x_48)) {
case 2:
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
lean_dec(x_48);
x_49 = lean_nat_add(x_6, x_39);
x_50 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
lean_inc(x_5);
x_51 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_49, x_50, x_8, x_9, x_10, x_11);
lean_dec(x_49);
if (lean_obj_tag(x_51) == 0)
{
uint8_t x_52; 
x_52 = !lean_is_exclusive(x_51);
if (x_52 == 0)
{
lean_object* x_53; uint8_t x_54; 
x_53 = lean_ctor_get(x_51, 0);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; 
x_55 = lean_ctor_get(x_53, 0);
x_56 = lean_ctor_get(x_2, 2);
x_57 = lean_nat_add(x_56, x_6);
x_58 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_58, 0, x_5);
lean_ctor_set(x_58, 1, x_57);
lean_ctor_set(x_58, 2, x_46);
lean_ctor_set(x_58, 3, x_55);
lean_ctor_set(x_53, 0, x_58);
return x_51;
}
else
{
lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; 
x_59 = lean_ctor_get(x_53, 0);
x_60 = lean_ctor_get(x_53, 1);
lean_inc(x_60);
lean_inc(x_59);
lean_dec(x_53);
x_61 = lean_ctor_get(x_2, 2);
x_62 = lean_nat_add(x_61, x_6);
x_63 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_63, 0, x_5);
lean_ctor_set(x_63, 1, x_62);
lean_ctor_set(x_63, 2, x_46);
lean_ctor_set(x_63, 3, x_59);
x_64 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_64, 0, x_63);
lean_ctor_set(x_64, 1, x_60);
lean_ctor_set(x_51, 0, x_64);
return x_51;
}
}
else
{
lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; 
x_65 = lean_ctor_get(x_51, 0);
x_66 = lean_ctor_get(x_51, 1);
lean_inc(x_66);
lean_inc(x_65);
lean_dec(x_51);
x_67 = lean_ctor_get(x_65, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 x_69 = x_65;
} else {
 lean_dec_ref(x_65);
 x_69 = lean_box(0);
}
x_70 = lean_ctor_get(x_2, 2);
x_71 = lean_nat_add(x_70, x_6);
x_72 = lean_alloc_ctor(4, 4, 0);
lean_ctor_set(x_72, 0, x_5);
lean_ctor_set(x_72, 1, x_71);
lean_ctor_set(x_72, 2, x_46);
lean_ctor_set(x_72, 3, x_67);
if (lean_is_scalar(x_69)) {
 x_73 = lean_alloc_ctor(0, 2, 0);
} else {
 x_73 = x_69;
}
lean_ctor_set(x_73, 0, x_72);
lean_ctor_set(x_73, 1, x_68);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_73);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
}
else
{
lean_dec(x_46);
lean_dec(x_5);
return x_51;
}
}
case 3:
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; 
x_75 = lean_ctor_get(x_48, 1);
lean_inc(x_75);
x_76 = lean_ctor_get(x_48, 2);
lean_inc(x_76);
lean_dec(x_48);
x_77 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
lean_inc(x_5);
x_78 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_77, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_78) == 0)
{
uint8_t x_79; 
x_79 = !lean_is_exclusive(x_78);
if (x_79 == 0)
{
lean_object* x_80; uint8_t x_81; 
x_80 = lean_ctor_get(x_78, 0);
x_81 = !lean_is_exclusive(x_80);
if (x_81 == 0)
{
lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; 
x_82 = lean_ctor_get(x_80, 0);
x_83 = lean_ctor_get(x_2, 2);
x_84 = lean_ctor_get(x_2, 3);
x_85 = lean_nat_add(x_83, x_84);
x_86 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_86, 0, x_5);
lean_ctor_set(x_86, 1, x_85);
lean_ctor_set(x_86, 2, x_75);
lean_ctor_set(x_86, 3, x_46);
lean_ctor_set(x_86, 4, x_76);
lean_ctor_set(x_86, 5, x_82);
lean_ctor_set(x_80, 0, x_86);
return x_78;
}
else
{
lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_87 = lean_ctor_get(x_80, 0);
x_88 = lean_ctor_get(x_80, 1);
lean_inc(x_88);
lean_inc(x_87);
lean_dec(x_80);
x_89 = lean_ctor_get(x_2, 2);
x_90 = lean_ctor_get(x_2, 3);
x_91 = lean_nat_add(x_89, x_90);
x_92 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_92, 0, x_5);
lean_ctor_set(x_92, 1, x_91);
lean_ctor_set(x_92, 2, x_75);
lean_ctor_set(x_92, 3, x_46);
lean_ctor_set(x_92, 4, x_76);
lean_ctor_set(x_92, 5, x_87);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_88);
lean_ctor_set(x_78, 0, x_93);
return x_78;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_94 = lean_ctor_get(x_78, 0);
x_95 = lean_ctor_get(x_78, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_78);
x_96 = lean_ctor_get(x_94, 0);
lean_inc(x_96);
x_97 = lean_ctor_get(x_94, 1);
lean_inc(x_97);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_98 = x_94;
} else {
 lean_dec_ref(x_94);
 x_98 = lean_box(0);
}
x_99 = lean_ctor_get(x_2, 2);
x_100 = lean_ctor_get(x_2, 3);
x_101 = lean_nat_add(x_99, x_100);
x_102 = lean_alloc_ctor(5, 6, 0);
lean_ctor_set(x_102, 0, x_5);
lean_ctor_set(x_102, 1, x_101);
lean_ctor_set(x_102, 2, x_75);
lean_ctor_set(x_102, 3, x_46);
lean_ctor_set(x_102, 4, x_76);
lean_ctor_set(x_102, 5, x_96);
if (lean_is_scalar(x_98)) {
 x_103 = lean_alloc_ctor(0, 2, 0);
} else {
 x_103 = x_98;
}
lean_ctor_set(x_103, 0, x_102);
lean_ctor_set(x_103, 1, x_97);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_95);
return x_104;
}
}
else
{
lean_dec(x_76);
lean_dec(x_75);
lean_dec(x_46);
lean_dec(x_5);
return x_78;
}
}
default: 
{
lean_object* x_105; 
lean_dec(x_48);
lean_dec(x_46);
x_105 = lean_nat_add(x_7, x_39);
lean_dec(x_7);
x_7 = x_105;
goto _start;
}
}
}
else
{
lean_dec(x_45);
x_12 = x_8;
x_13 = x_9;
x_14 = x_10;
x_15 = x_11;
goto block_19;
}
}
}
else
{
lean_object* x_107; lean_object* x_108; 
lean_dec(x_23);
x_107 = lean_unsigned_to_nat(1u);
x_108 = lean_nat_add(x_7, x_107);
lean_dec(x_7);
x_7 = x_108;
goto _start;
}
}
block_19:
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_nat_add(x_7, x_16);
lean_dec(x_7);
x_7 = x_17;
x_8 = x_12;
x_9 = x_13;
x_10 = x_14;
x_11 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerAlt_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerAlt_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__1(x_8, x_9, x_3, x_4, x_5, x_6, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
size_t x_9; size_t x_10; lean_object* x_11; 
x_9 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_10 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_11 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__2(x_1, x_9, x_10, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_throwError___at___Lean_IR_ToIR_lowerLet_spec__0(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_9; lean_object* x_10; 
x_9 = lean_unbox(x_3);
lean_dec(x_3);
x_10 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___redArg(x_1, x_2, x_9, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; lean_object* x_14; 
x_13 = lean_unbox(x_3);
lean_dec(x_3);
x_14 = l_Std_Range_forIn_x27_loop___at___Lean_IR_ToIR_lowerLet_spec__1(x_1, x_2, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_11);
lean_dec(x_10);
lean_dec(x_4);
lean_dec(x_2);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_IR_ToIR_lowerLet___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__2___boxed(lean_object* x_1) {
_start:
{
uint8_t x_2; lean_object* x_3; 
x_2 = l_Lean_IR_ToIR_lowerLet___lam__2(x_1);
lean_dec(x_1);
x_3 = lean_box(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__6___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_3 = lean_unbox(x_1);
lean_dec(x_1);
x_4 = l_Lean_IR_ToIR_lowerLet___lam__6(x_3, x_2);
lean_dec(x_2);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet___lam__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13, lean_object* x_14, lean_object* x_15, lean_object* x_16) {
_start:
{
lean_object* x_17; 
x_17 = l_Lean_IR_ToIR_lowerLet___lam__8(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11, x_12, x_13, x_14, x_15, x_16);
lean_dec(x_11);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_IR_ToIR_lowerLet_lowerNonObjectFields_loop(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_2 = lean_mk_string_unchecked("Lean.Compiler.IR.ToIR", 21, 21);
x_3 = lean_mk_string_unchecked("Lean.IR.ToIR.lowerResultType.resultTypeForArity", 47, 47);
x_4 = lean_unsigned_to_nat(384u);
x_5 = lean_unsigned_to_nat(11u);
x_6 = lean_mk_string_unchecked("invalid arity", 13, 13);
x_7 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec(x_3);
lean_dec(x_2);
x_8 = l_panic___at___Lean_Expr_appFn_x21_spec__0(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; uint8_t x_4; 
x_3 = lean_unsigned_to_nat(0u);
x_4 = lean_nat_dec_eq(x_2, x_3);
if (x_4 == 0)
{
switch (lean_obj_tag(x_1)) {
case 4:
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; 
lean_dec(x_2);
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_ctor_get(x_1, 1);
lean_inc(x_6);
lean_dec(x_1);
x_7 = lean_box(0);
switch (lean_obj_tag(x_5)) {
case 0:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Expr_const___override(x_7, x_6);
x_9 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(x_8);
lean_dec(x_8);
return x_9;
}
case 1:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_26; uint8_t x_27; 
x_10 = lean_ctor_get(x_5, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_5, 1);
lean_inc(x_11);
lean_dec(x_5);
x_26 = lean_mk_string_unchecked("lcErased", 8, 8);
x_27 = lean_string_dec_eq(x_11, x_26);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec(x_26);
lean_inc(x_11);
x_28 = l_Lean_Name_str___override(x_7, x_11);
lean_inc(x_6);
x_29 = l_Lean_Expr_const___override(x_28, x_6);
x_30 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(x_29);
lean_dec(x_29);
x_12 = x_30;
goto block_25;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; 
x_31 = l_Lean_Name_mkStr1(x_26);
x_32 = lean_box(0);
x_33 = l_Lean_Expr_const___override(x_31, x_32);
x_12 = x_33;
goto block_25;
}
block_25:
{
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_dec(x_11);
lean_dec(x_6);
return x_12;
}
case 1:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; 
lean_dec(x_12);
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_10, 1);
lean_inc(x_14);
lean_dec(x_10);
x_15 = l_Lean_Name_str___override(x_13, x_14);
x_16 = l_Lean_Name_str___override(x_15, x_11);
x_17 = l_Lean_Expr_const___override(x_16, x_6);
x_18 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(x_17);
lean_dec(x_17);
return x_18;
}
default: 
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; 
lean_dec(x_12);
x_19 = lean_ctor_get(x_10, 0);
lean_inc(x_19);
x_20 = lean_ctor_get(x_10, 1);
lean_inc(x_20);
lean_dec(x_10);
x_21 = l_Lean_Name_num___override(x_19, x_20);
x_22 = l_Lean_Name_str___override(x_21, x_11);
x_23 = l_Lean_Expr_const___override(x_22, x_6);
x_24 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(x_23);
lean_dec(x_23);
return x_24;
}
}
}
}
default: 
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_34 = lean_ctor_get(x_5, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_5, 1);
lean_inc(x_35);
lean_dec(x_5);
x_36 = l_Lean_Name_num___override(x_34, x_35);
x_37 = l_Lean_Expr_const___override(x_36, x_6);
x_38 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(x_37);
lean_dec(x_37);
return x_38;
}
}
}
case 7:
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_39 = lean_ctor_get(x_1, 2);
lean_inc(x_39);
lean_dec(x_1);
x_40 = lean_unsigned_to_nat(1u);
x_41 = lean_nat_sub(x_2, x_40);
lean_dec(x_2);
x_1 = x_39;
x_2 = x_41;
goto _start;
}
default: 
{
lean_object* x_43; 
lean_dec(x_2);
x_43 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(x_1);
lean_dec(x_1);
return x_43;
}
}
}
else
{
lean_dec(x_2);
return x_1;
}
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity___lam__0(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerResultType(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_IR_ToIR_lowerResultType_resultTypeForArity(x_1, x_2);
x_8 = l_Lean_IR_ToIR_lowerType(x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_ToIR_lowerDecl(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; size_t x_7; lean_object* x_8; size_t x_9; lean_object* x_10; 
x_6 = lean_ctor_get(x_1, 3);
lean_inc(x_6);
x_7 = lean_array_size(x_6);
x_8 = lean_unsigned_to_nat(0u);
x_9 = lean_usize_of_nat(x_8);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_6);
x_10 = l_Array_mapMUnsafe_map___at___Lean_IR_ToIR_lowerCode_spec__0(x_7, x_9, x_6, x_2, x_3, x_4, x_5);
if (lean_obj_tag(x_10) == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
x_15 = lean_ctor_get(x_1, 2);
lean_inc(x_15);
x_16 = lean_array_get_size(x_6);
lean_dec(x_6);
lean_inc(x_4);
lean_inc(x_3);
x_17 = l_Lean_IR_ToIR_lowerResultType(x_15, x_16, x_14, x_3, x_4, x_12);
if (lean_obj_tag(x_17) == 0)
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_ctor_get(x_17, 0);
lean_inc(x_18);
x_19 = lean_ctor_get(x_1, 4);
lean_inc(x_19);
if (lean_obj_tag(x_19) == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_dec(x_17);
x_21 = lean_ctor_get(x_18, 0);
lean_inc(x_21);
x_22 = lean_ctor_get(x_18, 1);
lean_inc(x_22);
lean_dec(x_18);
x_23 = !lean_is_exclusive(x_19);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_19, 0);
x_25 = l_Lean_IR_ToIR_lowerCode(x_24, x_22, x_3, x_4, x_20);
if (lean_obj_tag(x_25) == 0)
{
uint8_t x_26; 
x_26 = !lean_is_exclusive(x_25);
if (x_26 == 0)
{
lean_object* x_27; uint8_t x_28; 
x_27 = lean_ctor_get(x_25, 0);
x_28 = !lean_is_exclusive(x_27);
if (x_28 == 0)
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_ctor_get(x_27, 0);
x_30 = lean_ctor_get(x_1, 0);
lean_inc(x_30);
lean_dec(x_1);
x_31 = lean_box(0);
x_32 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_32, 0, x_30);
lean_ctor_set(x_32, 1, x_13);
lean_ctor_set(x_32, 2, x_21);
lean_ctor_set(x_32, 3, x_29);
lean_ctor_set(x_32, 4, x_31);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_32);
lean_ctor_set(x_27, 0, x_19);
return x_25;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_33 = lean_ctor_get(x_27, 0);
x_34 = lean_ctor_get(x_27, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_27);
x_35 = lean_ctor_get(x_1, 0);
lean_inc(x_35);
lean_dec(x_1);
x_36 = lean_box(0);
x_37 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_37, 0, x_35);
lean_ctor_set(x_37, 1, x_13);
lean_ctor_set(x_37, 2, x_21);
lean_ctor_set(x_37, 3, x_33);
lean_ctor_set(x_37, 4, x_36);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_37);
x_38 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_38, 0, x_19);
lean_ctor_set(x_38, 1, x_34);
lean_ctor_set(x_25, 0, x_38);
return x_25;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_39 = lean_ctor_get(x_25, 0);
x_40 = lean_ctor_get(x_25, 1);
lean_inc(x_40);
lean_inc(x_39);
lean_dec(x_25);
x_41 = lean_ctor_get(x_39, 0);
lean_inc(x_41);
x_42 = lean_ctor_get(x_39, 1);
lean_inc(x_42);
if (lean_is_exclusive(x_39)) {
 lean_ctor_release(x_39, 0);
 lean_ctor_release(x_39, 1);
 x_43 = x_39;
} else {
 lean_dec_ref(x_39);
 x_43 = lean_box(0);
}
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
lean_dec(x_1);
x_45 = lean_box(0);
x_46 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_46, 0, x_44);
lean_ctor_set(x_46, 1, x_13);
lean_ctor_set(x_46, 2, x_21);
lean_ctor_set(x_46, 3, x_41);
lean_ctor_set(x_46, 4, x_45);
lean_ctor_set_tag(x_19, 1);
lean_ctor_set(x_19, 0, x_46);
if (lean_is_scalar(x_43)) {
 x_47 = lean_alloc_ctor(0, 2, 0);
} else {
 x_47 = x_43;
}
lean_ctor_set(x_47, 0, x_19);
lean_ctor_set(x_47, 1, x_42);
x_48 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_48, 0, x_47);
lean_ctor_set(x_48, 1, x_40);
return x_48;
}
}
else
{
uint8_t x_49; 
lean_free_object(x_19);
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_1);
x_49 = !lean_is_exclusive(x_25);
if (x_49 == 0)
{
return x_25;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
x_50 = lean_ctor_get(x_25, 0);
x_51 = lean_ctor_get(x_25, 1);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_25);
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
x_53 = lean_ctor_get(x_19, 0);
lean_inc(x_53);
lean_dec(x_19);
x_54 = l_Lean_IR_ToIR_lowerCode(x_53, x_22, x_3, x_4, x_20);
if (lean_obj_tag(x_54) == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; 
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
x_59 = lean_ctor_get(x_55, 1);
lean_inc(x_59);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 lean_ctor_release(x_55, 1);
 x_60 = x_55;
} else {
 lean_dec_ref(x_55);
 x_60 = lean_box(0);
}
x_61 = lean_ctor_get(x_1, 0);
lean_inc(x_61);
lean_dec(x_1);
x_62 = lean_box(0);
x_63 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_63, 0, x_61);
lean_ctor_set(x_63, 1, x_13);
lean_ctor_set(x_63, 2, x_21);
lean_ctor_set(x_63, 3, x_58);
lean_ctor_set(x_63, 4, x_62);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
if (lean_is_scalar(x_60)) {
 x_65 = lean_alloc_ctor(0, 2, 0);
} else {
 x_65 = x_60;
}
lean_ctor_set(x_65, 0, x_64);
lean_ctor_set(x_65, 1, x_59);
if (lean_is_scalar(x_57)) {
 x_66 = lean_alloc_ctor(0, 2, 0);
} else {
 x_66 = x_57;
}
lean_ctor_set(x_66, 0, x_65);
lean_ctor_set(x_66, 1, x_56);
return x_66;
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
lean_dec(x_21);
lean_dec(x_13);
lean_dec(x_1);
x_67 = lean_ctor_get(x_54, 0);
lean_inc(x_67);
x_68 = lean_ctor_get(x_54, 1);
lean_inc(x_68);
if (lean_is_exclusive(x_54)) {
 lean_ctor_release(x_54, 0);
 lean_ctor_release(x_54, 1);
 x_69 = x_54;
} else {
 lean_dec_ref(x_54);
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
}
else
{
uint8_t x_71; 
lean_dec(x_3);
x_71 = !lean_is_exclusive(x_17);
if (x_71 == 0)
{
lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_72 = lean_ctor_get(x_17, 1);
x_73 = lean_ctor_get(x_17, 0);
lean_dec(x_73);
x_74 = !lean_is_exclusive(x_18);
if (x_74 == 0)
{
uint8_t x_75; 
x_75 = !lean_is_exclusive(x_19);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; uint8_t x_80; 
x_76 = lean_ctor_get(x_18, 0);
x_77 = lean_ctor_get(x_18, 1);
x_78 = lean_ctor_get(x_19, 0);
x_79 = lean_ctor_get(x_78, 1);
lean_inc(x_79);
x_80 = l_List_isEmpty___redArg(x_79);
lean_dec(x_79);
if (x_80 == 0)
{
lean_object* x_81; lean_object* x_82; 
lean_dec(x_4);
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
lean_dec(x_1);
x_82 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_82, 0, x_81);
lean_ctor_set(x_82, 1, x_13);
lean_ctor_set(x_82, 2, x_76);
lean_ctor_set(x_82, 3, x_78);
lean_ctor_set(x_19, 0, x_82);
lean_ctor_set(x_18, 0, x_19);
return x_17;
}
else
{
lean_object* x_83; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
lean_free_object(x_19);
lean_dec(x_78);
lean_free_object(x_18);
lean_free_object(x_17);
x_83 = lean_ctor_get(x_1, 0);
lean_inc(x_83);
lean_dec(x_1);
x_84 = lean_ir_mk_dummy_extern_decl(x_83, x_13, x_76);
x_85 = l_Lean_IR_ToIR_addDecl___redArg(x_84, x_77, x_4, x_72);
lean_dec(x_4);
x_86 = !lean_is_exclusive(x_85);
if (x_86 == 0)
{
lean_object* x_87; uint8_t x_88; 
x_87 = lean_ctor_get(x_85, 0);
x_88 = !lean_is_exclusive(x_87);
if (x_88 == 0)
{
lean_object* x_89; lean_object* x_90; 
x_89 = lean_ctor_get(x_87, 0);
lean_dec(x_89);
x_90 = lean_box(0);
lean_ctor_set(x_87, 0, x_90);
return x_85;
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
x_91 = lean_ctor_get(x_87, 1);
lean_inc(x_91);
lean_dec(x_87);
x_92 = lean_box(0);
x_93 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_93, 0, x_92);
lean_ctor_set(x_93, 1, x_91);
lean_ctor_set(x_85, 0, x_93);
return x_85;
}
}
else
{
lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; 
x_94 = lean_ctor_get(x_85, 0);
x_95 = lean_ctor_get(x_85, 1);
lean_inc(x_95);
lean_inc(x_94);
lean_dec(x_85);
x_96 = lean_ctor_get(x_94, 1);
lean_inc(x_96);
if (lean_is_exclusive(x_94)) {
 lean_ctor_release(x_94, 0);
 lean_ctor_release(x_94, 1);
 x_97 = x_94;
} else {
 lean_dec_ref(x_94);
 x_97 = lean_box(0);
}
x_98 = lean_box(0);
if (lean_is_scalar(x_97)) {
 x_99 = lean_alloc_ctor(0, 2, 0);
} else {
 x_99 = x_97;
}
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_96);
x_100 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_95);
return x_100;
}
}
}
else
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; 
x_101 = lean_ctor_get(x_18, 0);
x_102 = lean_ctor_get(x_18, 1);
x_103 = lean_ctor_get(x_19, 0);
lean_inc(x_103);
lean_dec(x_19);
x_104 = lean_ctor_get(x_103, 1);
lean_inc(x_104);
x_105 = l_List_isEmpty___redArg(x_104);
lean_dec(x_104);
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
lean_dec(x_4);
x_106 = lean_ctor_get(x_1, 0);
lean_inc(x_106);
lean_dec(x_1);
x_107 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_107, 0, x_106);
lean_ctor_set(x_107, 1, x_13);
lean_ctor_set(x_107, 2, x_101);
lean_ctor_set(x_107, 3, x_103);
x_108 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_108, 0, x_107);
lean_ctor_set(x_18, 0, x_108);
return x_17;
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; 
lean_dec(x_103);
lean_free_object(x_18);
lean_free_object(x_17);
x_109 = lean_ctor_get(x_1, 0);
lean_inc(x_109);
lean_dec(x_1);
x_110 = lean_ir_mk_dummy_extern_decl(x_109, x_13, x_101);
x_111 = l_Lean_IR_ToIR_addDecl___redArg(x_110, x_102, x_4, x_72);
lean_dec(x_4);
x_112 = lean_ctor_get(x_111, 0);
lean_inc(x_112);
x_113 = lean_ctor_get(x_111, 1);
lean_inc(x_113);
if (lean_is_exclusive(x_111)) {
 lean_ctor_release(x_111, 0);
 lean_ctor_release(x_111, 1);
 x_114 = x_111;
} else {
 lean_dec_ref(x_111);
 x_114 = lean_box(0);
}
x_115 = lean_ctor_get(x_112, 1);
lean_inc(x_115);
if (lean_is_exclusive(x_112)) {
 lean_ctor_release(x_112, 0);
 lean_ctor_release(x_112, 1);
 x_116 = x_112;
} else {
 lean_dec_ref(x_112);
 x_116 = lean_box(0);
}
x_117 = lean_box(0);
if (lean_is_scalar(x_116)) {
 x_118 = lean_alloc_ctor(0, 2, 0);
} else {
 x_118 = x_116;
}
lean_ctor_set(x_118, 0, x_117);
lean_ctor_set(x_118, 1, x_115);
if (lean_is_scalar(x_114)) {
 x_119 = lean_alloc_ctor(0, 2, 0);
} else {
 x_119 = x_114;
}
lean_ctor_set(x_119, 0, x_118);
lean_ctor_set(x_119, 1, x_113);
return x_119;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; uint8_t x_125; 
x_120 = lean_ctor_get(x_18, 0);
x_121 = lean_ctor_get(x_18, 1);
lean_inc(x_121);
lean_inc(x_120);
lean_dec(x_18);
x_122 = lean_ctor_get(x_19, 0);
lean_inc(x_122);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_123 = x_19;
} else {
 lean_dec_ref(x_19);
 x_123 = lean_box(0);
}
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
x_125 = l_List_isEmpty___redArg(x_124);
lean_dec(x_124);
if (x_125 == 0)
{
lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; 
lean_dec(x_4);
x_126 = lean_ctor_get(x_1, 0);
lean_inc(x_126);
lean_dec(x_1);
x_127 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_127, 0, x_126);
lean_ctor_set(x_127, 1, x_13);
lean_ctor_set(x_127, 2, x_120);
lean_ctor_set(x_127, 3, x_122);
if (lean_is_scalar(x_123)) {
 x_128 = lean_alloc_ctor(1, 1, 0);
} else {
 x_128 = x_123;
}
lean_ctor_set(x_128, 0, x_127);
x_129 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_129, 0, x_128);
lean_ctor_set(x_129, 1, x_121);
lean_ctor_set(x_17, 0, x_129);
return x_17;
}
else
{
lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; lean_object* x_140; 
lean_dec(x_123);
lean_dec(x_122);
lean_free_object(x_17);
x_130 = lean_ctor_get(x_1, 0);
lean_inc(x_130);
lean_dec(x_1);
x_131 = lean_ir_mk_dummy_extern_decl(x_130, x_13, x_120);
x_132 = l_Lean_IR_ToIR_addDecl___redArg(x_131, x_121, x_4, x_72);
lean_dec(x_4);
x_133 = lean_ctor_get(x_132, 0);
lean_inc(x_133);
x_134 = lean_ctor_get(x_132, 1);
lean_inc(x_134);
if (lean_is_exclusive(x_132)) {
 lean_ctor_release(x_132, 0);
 lean_ctor_release(x_132, 1);
 x_135 = x_132;
} else {
 lean_dec_ref(x_132);
 x_135 = lean_box(0);
}
x_136 = lean_ctor_get(x_133, 1);
lean_inc(x_136);
if (lean_is_exclusive(x_133)) {
 lean_ctor_release(x_133, 0);
 lean_ctor_release(x_133, 1);
 x_137 = x_133;
} else {
 lean_dec_ref(x_133);
 x_137 = lean_box(0);
}
x_138 = lean_box(0);
if (lean_is_scalar(x_137)) {
 x_139 = lean_alloc_ctor(0, 2, 0);
} else {
 x_139 = x_137;
}
lean_ctor_set(x_139, 0, x_138);
lean_ctor_set(x_139, 1, x_136);
if (lean_is_scalar(x_135)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_135;
}
lean_ctor_set(x_140, 0, x_139);
lean_ctor_set(x_140, 1, x_134);
return x_140;
}
}
}
else
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; uint8_t x_148; 
x_141 = lean_ctor_get(x_17, 1);
lean_inc(x_141);
lean_dec(x_17);
x_142 = lean_ctor_get(x_18, 0);
lean_inc(x_142);
x_143 = lean_ctor_get(x_18, 1);
lean_inc(x_143);
if (lean_is_exclusive(x_18)) {
 lean_ctor_release(x_18, 0);
 lean_ctor_release(x_18, 1);
 x_144 = x_18;
} else {
 lean_dec_ref(x_18);
 x_144 = lean_box(0);
}
x_145 = lean_ctor_get(x_19, 0);
lean_inc(x_145);
if (lean_is_exclusive(x_19)) {
 lean_ctor_release(x_19, 0);
 x_146 = x_19;
} else {
 lean_dec_ref(x_19);
 x_146 = lean_box(0);
}
x_147 = lean_ctor_get(x_145, 1);
lean_inc(x_147);
x_148 = l_List_isEmpty___redArg(x_147);
lean_dec(x_147);
if (x_148 == 0)
{
lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; 
lean_dec(x_4);
x_149 = lean_ctor_get(x_1, 0);
lean_inc(x_149);
lean_dec(x_1);
x_150 = lean_alloc_ctor(1, 4, 0);
lean_ctor_set(x_150, 0, x_149);
lean_ctor_set(x_150, 1, x_13);
lean_ctor_set(x_150, 2, x_142);
lean_ctor_set(x_150, 3, x_145);
if (lean_is_scalar(x_146)) {
 x_151 = lean_alloc_ctor(1, 1, 0);
} else {
 x_151 = x_146;
}
lean_ctor_set(x_151, 0, x_150);
if (lean_is_scalar(x_144)) {
 x_152 = lean_alloc_ctor(0, 2, 0);
} else {
 x_152 = x_144;
}
lean_ctor_set(x_152, 0, x_151);
lean_ctor_set(x_152, 1, x_143);
x_153 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_153, 0, x_152);
lean_ctor_set(x_153, 1, x_141);
return x_153;
}
else
{
lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; 
lean_dec(x_146);
lean_dec(x_145);
lean_dec(x_144);
x_154 = lean_ctor_get(x_1, 0);
lean_inc(x_154);
lean_dec(x_1);
x_155 = lean_ir_mk_dummy_extern_decl(x_154, x_13, x_142);
x_156 = l_Lean_IR_ToIR_addDecl___redArg(x_155, x_143, x_4, x_141);
lean_dec(x_4);
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_159 = x_156;
} else {
 lean_dec_ref(x_156);
 x_159 = lean_box(0);
}
x_160 = lean_ctor_get(x_157, 1);
lean_inc(x_160);
if (lean_is_exclusive(x_157)) {
 lean_ctor_release(x_157, 0);
 lean_ctor_release(x_157, 1);
 x_161 = x_157;
} else {
 lean_dec_ref(x_157);
 x_161 = lean_box(0);
}
x_162 = lean_box(0);
if (lean_is_scalar(x_161)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_161;
}
lean_ctor_set(x_163, 0, x_162);
lean_ctor_set(x_163, 1, x_160);
if (lean_is_scalar(x_159)) {
 x_164 = lean_alloc_ctor(0, 2, 0);
} else {
 x_164 = x_159;
}
lean_ctor_set(x_164, 0, x_163);
lean_ctor_set(x_164, 1, x_158);
return x_164;
}
}
}
}
else
{
uint8_t x_165; 
lean_dec(x_13);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_165 = !lean_is_exclusive(x_17);
if (x_165 == 0)
{
return x_17;
}
else
{
lean_object* x_166; lean_object* x_167; lean_object* x_168; 
x_166 = lean_ctor_get(x_17, 0);
x_167 = lean_ctor_get(x_17, 1);
lean_inc(x_167);
lean_inc(x_166);
lean_dec(x_17);
x_168 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_168, 0, x_166);
lean_ctor_set(x_168, 1, x_167);
return x_168;
}
}
}
else
{
uint8_t x_169; 
lean_dec(x_6);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_1);
x_169 = !lean_is_exclusive(x_10);
if (x_169 == 0)
{
return x_10;
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; 
x_170 = lean_ctor_get(x_10, 0);
x_171 = lean_ctor_get(x_10, 1);
lean_inc(x_171);
lean_inc(x_170);
lean_dec(x_10);
x_172 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_172, 0, x_170);
lean_ctor_set(x_172, 1, x_171);
return x_172;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec(x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_array_uget(x_1, x_3);
x_11 = lean_alloc_closure((void*)(l_Lean_IR_ToIR_lowerDecl), 5, 1);
lean_closure_set(x_11, 0, x_10);
lean_inc(x_6);
lean_inc(x_5);
x_12 = l_Lean_IR_ToIR_M_run___redArg(x_11, x_5, x_6, x_7);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_ctor_get(x_12, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_12, 1);
lean_inc(x_14);
lean_dec(x_12);
if (lean_obj_tag(x_13) == 0)
{
x_15 = x_4;
goto block_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
x_21 = lean_ctor_get(x_13, 0);
lean_inc(x_21);
lean_dec(x_13);
x_22 = lean_array_push(x_4, x_21);
x_15 = x_22;
goto block_20;
}
block_20:
{
lean_object* x_16; size_t x_17; size_t x_18; 
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_15;
x_7 = x_14;
goto _start;
}
}
else
{
uint8_t x_23; 
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
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
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_5 = lean_unsigned_to_nat(0u);
x_6 = lean_mk_empty_array_with_capacity(x_5);
x_7 = lean_array_size(x_1);
x_8 = lean_usize_of_nat(x_5);
x_9 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_7, x_8, x_6, x_2, x_3, x_4);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_IR_toIR_spec__0(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_IR_toIR___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_IR_toIR(x_1, x_2, x_3, x_4);
lean_dec(x_1);
return x_5;
}
}
lean_object* initialize_Lean_Compiler_LCNF_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_Basic(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_IR_CtorLayout(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_CoreM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Environment(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_IR_ToIR(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_Basic(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_IR_CtorLayout(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_CoreM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Environment(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_IR_ToIR_instInhabitedTranslatedProj = _init_l_Lean_IR_ToIR_instInhabitedTranslatedProj();
lean_mark_persistent(l_Lean_IR_ToIR_instInhabitedTranslatedProj);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
