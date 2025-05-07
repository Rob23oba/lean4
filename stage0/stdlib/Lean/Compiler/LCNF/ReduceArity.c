// Lean compiler output
// Module: Lean.Compiler.LCNF.ReduceArity
// Imports: Lean.Compiler.LCNF.CompilerM Lean.Compiler.LCNF.PhaseExt Lean.Compiler.LCNF.InferType Lean.Compiler.LCNF.Internalize
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
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object*, uint8_t, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LetDecl_updateValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Code_inferType(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_LCtx_toLocalContext(lean_object*);
lean_object* l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7_spec__7(lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_mkForallParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object*, uint8_t, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Compiler_LCNF_Decl_saveMono___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity;
lean_object* l_Lean_Compiler_LCNF_eraseParams___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerTraceClass(lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Compiler_LCNF_Param_toArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
lean_object* lean_st_ref_get(lean_object*, lean_object*);
lean_object* lean_st_mk_ref(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l_Lean_checkTraceOption(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Init_Util_0__mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_FVarIdSet_insert(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2415_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_append(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_shiftl(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7_spec__7___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Nat_nextPowerOfTwo(lean_object*);
lean_object* l_Lean_RBMap_size___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
lean_object* l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* l_Lean_Expr_fvar___override(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_2, 1);
x_6 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_5, x_1);
if (lean_obj_tag(x_6) == 0)
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; 
lean_dec(x_6);
x_9 = lean_st_ref_take(x_3, x_4);
x_10 = lean_ctor_get(x_9, 0);
lean_inc(x_10);
x_11 = lean_ctor_get(x_9, 1);
lean_inc(x_11);
lean_dec(x_9);
x_12 = l_Lean_FVarIdSet_insert(x_10, x_1);
x_13 = lean_st_ref_set(x_3, x_12, x_11);
x_14 = !lean_is_exclusive(x_13);
if (x_14 == 0)
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_ctor_get(x_13, 0);
lean_dec(x_15);
x_16 = lean_box(0);
lean_ctor_set(x_13, 0, x_16);
return x_13;
}
else
{
lean_object* x_17; lean_object* x_18; lean_object* x_19; 
x_17 = lean_ctor_get(x_13, 1);
lean_inc(x_17);
lean_dec(x_13);
x_18 = lean_box(0);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_18);
lean_ctor_set(x_19, 1, x_17);
return x_19;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitFVar___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitFVar(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
if (lean_obj_tag(x_1) == 1)
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
lean_dec(x_1);
x_6 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_5, x_2, x_3, x_4);
return x_6;
}
else
{
lean_object* x_7; lean_object* x_8; 
lean_dec(x_1);
x_7 = lean_box(0);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_4);
return x_8;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_1, x_2, x_3, x_8);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_1, x_2, x_3, x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_eq(x_2, x_3);
if (x_8 == 0)
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; size_t x_14; size_t x_15; 
lean_dec(x_4);
x_9 = lean_array_uget(x_1, x_2);
x_10 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_9, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_10, 1);
lean_inc(x_12);
lean_dec(x_10);
x_13 = lean_unsigned_to_nat(1u);
x_14 = lean_usize_of_nat(x_13);
x_15 = lean_usize_add(x_2, x_14);
x_2 = x_15;
x_4 = x_11;
x_7 = x_12;
goto _start;
}
else
{
lean_object* x_17; 
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_4);
lean_ctor_set(x_17, 1, x_7);
return x_17;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_15; 
x_15 = lean_usize_dec_lt(x_3, x_2);
if (x_15 == 0)
{
lean_object* x_16; 
x_16 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_16, 0, x_4);
lean_ctor_set(x_16, 1, x_7);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_4, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_4, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_4);
lean_ctor_set(x_20, 1, x_7);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_21 = lean_ctor_get(x_4, 0);
lean_inc(x_21);
lean_dec(x_4);
x_22 = lean_array_fget(x_21, x_17);
x_23 = lean_unsigned_to_nat(1u);
x_24 = lean_nat_add(x_17, x_23);
lean_dec(x_17);
x_25 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_25, 0, x_21);
lean_ctor_set(x_25, 1, x_24);
lean_ctor_set(x_25, 2, x_18);
if (lean_obj_tag(x_22) == 1)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
x_26 = lean_ctor_get(x_22, 0);
lean_inc(x_26);
lean_dec(x_22);
x_27 = lean_array_uget(x_1, x_3);
x_28 = lean_ctor_get(x_27, 0);
lean_inc(x_28);
lean_dec(x_27);
x_29 = l___private_Lean_Expr_0__Lean_beqFVarId____x40_Lean_Expr___hyg_1672_(x_26, x_28);
lean_dec(x_28);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; 
x_30 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_26, x_5, x_6, x_7);
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
lean_dec(x_30);
x_8 = x_25;
x_9 = x_31;
goto block_14;
}
else
{
lean_dec(x_26);
x_8 = x_25;
x_9 = x_7;
goto block_14;
}
}
else
{
lean_dec(x_22);
x_8 = x_25;
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
x_12 = lean_usize_add(x_3, x_11);
x_3 = x_12;
x_4 = x_8;
x_7 = x_9;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; size_t x_16; size_t x_17; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_array_uget(x_10, x_3);
x_12 = l_Lean_Compiler_LCNF_FindUsed_visitArg___redArg(x_11, x_5, x_6, x_7);
x_13 = lean_ctor_get(x_12, 1);
lean_inc(x_13);
lean_dec(x_12);
x_14 = lean_box(0);
x_15 = lean_unsigned_to_nat(1u);
x_16 = lean_usize_of_nat(x_15);
x_17 = lean_usize_add(x_3, x_16);
x_3 = x_17;
x_4 = x_14;
x_7 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
uint8_t x_8; 
x_8 = lean_usize_dec_lt(x_3, x_2);
if (x_8 == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_4);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_dec(x_4);
x_10 = lean_ctor_get(x_1, 0);
x_11 = lean_array_uget(x_10, x_3);
x_12 = lean_ctor_get(x_11, 0);
lean_inc(x_12);
lean_dec(x_11);
x_13 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_12, x_5, x_6, x_7);
x_14 = lean_ctor_get(x_13, 1);
lean_inc(x_14);
lean_dec(x_13);
x_15 = lean_box(0);
x_16 = lean_unsigned_to_nat(1u);
x_17 = lean_usize_of_nat(x_16);
x_18 = lean_usize_add(x_3, x_17);
x_3 = x_18;
x_4 = x_15;
x_7 = x_14;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_11);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
switch (lean_obj_tag(x_1)) {
case 2:
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_1, 2);
lean_inc(x_9);
lean_dec(x_1);
x_10 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_9, x_2, x_3, x_8);
lean_dec(x_2);
return x_10;
}
case 3:
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 2);
lean_inc(x_12);
lean_dec(x_1);
x_13 = lean_ctor_get(x_2, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = lean_name_eq(x_11, x_14);
lean_dec(x_14);
lean_dec(x_11);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
lean_dec(x_13);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_get_size(x_12);
x_18 = lean_box(0);
x_19 = lean_nat_dec_lt(x_16, x_17);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_2);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_8);
return x_20;
}
else
{
uint8_t x_21; 
x_21 = lean_nat_dec_le(x_17, x_17);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_17);
lean_dec(x_12);
lean_dec(x_2);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_18);
lean_ctor_set(x_22, 1, x_8);
return x_22;
}
else
{
size_t x_23; size_t x_24; lean_object* x_25; 
x_23 = lean_usize_of_nat(x_16);
x_24 = lean_usize_of_nat(x_17);
lean_dec(x_17);
x_25 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_12, x_23, x_24, x_18, x_2, x_3, x_8);
lean_dec(x_2);
lean_dec(x_12);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; size_t x_38; lean_object* x_39; size_t x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; size_t x_45; lean_object* x_46; size_t x_47; lean_object* x_48; uint8_t x_49; 
x_26 = lean_unsigned_to_nat(0u);
x_27 = lean_array_get_size(x_12);
lean_inc(x_27);
lean_inc(x_12);
x_28 = l_Array_toSubarray___redArg(x_12, x_26, x_27);
x_29 = lean_ctor_get(x_13, 3);
lean_inc(x_29);
lean_dec(x_13);
x_30 = lean_array_size(x_29);
x_31 = lean_usize_of_nat(x_26);
x_32 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_29, x_30, x_31, x_28, x_2, x_3, x_8);
x_33 = lean_ctor_get(x_32, 1);
lean_inc(x_33);
lean_dec(x_32);
x_34 = lean_array_get_size(x_29);
lean_inc(x_27);
lean_inc(x_34);
x_35 = l_Array_toSubarray___redArg(x_12, x_34, x_27);
x_36 = lean_box(0);
x_37 = lean_ctor_get(x_35, 2);
lean_inc(x_37);
x_38 = lean_usize_of_nat(x_37);
lean_dec(x_37);
x_39 = lean_ctor_get(x_35, 1);
lean_inc(x_39);
x_40 = lean_usize_of_nat(x_39);
lean_dec(x_39);
x_41 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_35, x_38, x_40, x_36, x_2, x_3, x_33);
lean_dec(x_35);
x_42 = lean_ctor_get(x_41, 1);
lean_inc(x_42);
lean_dec(x_41);
x_43 = l_Array_toSubarray___redArg(x_29, x_27, x_34);
x_44 = lean_ctor_get(x_43, 2);
lean_inc(x_44);
x_45 = lean_usize_of_nat(x_44);
lean_dec(x_44);
x_46 = lean_ctor_get(x_43, 1);
lean_inc(x_46);
x_47 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_48 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_43, x_45, x_47, x_36, x_2, x_3, x_42);
lean_dec(x_2);
lean_dec(x_43);
x_49 = !lean_is_exclusive(x_48);
if (x_49 == 0)
{
lean_object* x_50; 
x_50 = lean_ctor_get(x_48, 0);
lean_dec(x_50);
lean_ctor_set(x_48, 0, x_36);
return x_48;
}
else
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_ctor_get(x_48, 1);
lean_inc(x_51);
lean_dec(x_48);
x_52 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_52, 0, x_36);
lean_ctor_set(x_52, 1, x_51);
return x_52;
}
}
}
case 4:
{
lean_object* x_53; lean_object* x_54; lean_object* x_55; uint8_t x_56; 
x_53 = lean_ctor_get(x_1, 0);
lean_inc(x_53);
x_54 = lean_ctor_get(x_1, 1);
lean_inc(x_54);
lean_dec(x_1);
x_55 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_53, x_2, x_3, x_8);
x_56 = !lean_is_exclusive(x_55);
if (x_56 == 0)
{
lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; uint8_t x_62; 
x_57 = lean_ctor_get(x_55, 1);
x_58 = lean_ctor_get(x_55, 0);
lean_dec(x_58);
x_59 = lean_unsigned_to_nat(0u);
x_60 = lean_array_get_size(x_54);
x_61 = lean_box(0);
x_62 = lean_nat_dec_lt(x_59, x_60);
if (x_62 == 0)
{
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_2);
lean_ctor_set(x_55, 0, x_61);
return x_55;
}
else
{
uint8_t x_63; 
x_63 = lean_nat_dec_le(x_60, x_60);
if (x_63 == 0)
{
lean_dec(x_60);
lean_dec(x_54);
lean_dec(x_2);
lean_ctor_set(x_55, 0, x_61);
return x_55;
}
else
{
size_t x_64; size_t x_65; lean_object* x_66; 
lean_free_object(x_55);
x_64 = lean_usize_of_nat(x_59);
x_65 = lean_usize_of_nat(x_60);
lean_dec(x_60);
x_66 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_54, x_64, x_65, x_61, x_2, x_3, x_57);
lean_dec(x_2);
lean_dec(x_54);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_67 = lean_ctor_get(x_55, 1);
lean_inc(x_67);
lean_dec(x_55);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get_size(x_54);
x_70 = lean_box(0);
x_71 = lean_nat_dec_lt(x_68, x_69);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_54);
lean_dec(x_2);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_67);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_69, x_69);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_69);
lean_dec(x_54);
lean_dec(x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_67);
return x_74;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = lean_usize_of_nat(x_68);
x_76 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_77 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_54, x_75, x_76, x_70, x_2, x_3, x_67);
lean_dec(x_2);
lean_dec(x_54);
return x_77;
}
}
}
}
default: 
{
lean_object* x_78; lean_object* x_79; 
lean_dec(x_2);
lean_dec(x_1);
x_78 = lean_box(0);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_8);
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__1(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__2(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
size_t x_8; size_t x_9; lean_object* x_10; 
x_8 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_9 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_10 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___redArg(x_1, x_8, x_9, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Subarray_forInUnsafe_loop___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__3(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visitLetValue___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; uint8_t x_21; 
x_21 = lean_usize_dec_eq(x_2, x_3);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec(x_4);
x_22 = lean_array_uget(x_1, x_2);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; 
x_23 = lean_ctor_get(x_22, 2);
lean_inc(x_23);
lean_dec(x_22);
x_12 = x_23;
goto block_20;
}
else
{
lean_object* x_24; 
x_24 = lean_ctor_get(x_22, 0);
lean_inc(x_24);
lean_dec(x_22);
x_12 = x_24;
goto block_20;
}
}
else
{
lean_object* x_25; 
lean_dec(x_5);
x_25 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_25, 0, x_4);
lean_ctor_set(x_25, 1, x_11);
return x_25;
}
block_20:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; 
lean_inc(x_5);
x_13 = l_Lean_Compiler_LCNF_FindUsed_visit(x_12, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
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
x_11 = x_15;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_23 = lean_ctor_get(x_1, 0);
lean_inc(x_23);
x_24 = lean_ctor_get(x_1, 1);
lean_inc(x_24);
lean_dec(x_1);
x_25 = lean_ctor_get(x_23, 3);
lean_inc(x_25);
lean_dec(x_23);
lean_inc(x_2);
x_26 = l_Lean_Compiler_LCNF_FindUsed_visitLetValue(x_25, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
x_27 = lean_ctor_get(x_26, 1);
lean_inc(x_27);
lean_dec(x_26);
x_1 = x_24;
x_8 = x_27;
goto _start;
}
case 3:
{
uint8_t x_29; 
x_29 = !lean_is_exclusive(x_1);
if (x_29 == 0)
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_30 = lean_ctor_get(x_1, 1);
x_31 = lean_ctor_get(x_1, 0);
lean_dec(x_31);
x_32 = lean_unsigned_to_nat(0u);
x_33 = lean_array_get_size(x_30);
x_34 = lean_box(0);
x_35 = lean_nat_dec_lt(x_32, x_33);
if (x_35 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
else
{
uint8_t x_36; 
x_36 = lean_nat_dec_le(x_33, x_33);
if (x_36 == 0)
{
lean_dec(x_33);
lean_dec(x_30);
lean_dec(x_2);
lean_ctor_set_tag(x_1, 0);
lean_ctor_set(x_1, 1, x_8);
lean_ctor_set(x_1, 0, x_34);
return x_1;
}
else
{
size_t x_37; size_t x_38; lean_object* x_39; 
lean_free_object(x_1);
x_37 = lean_usize_of_nat(x_32);
x_38 = lean_usize_of_nat(x_33);
lean_dec(x_33);
x_39 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_30, x_37, x_38, x_34, x_2, x_3, x_8);
lean_dec(x_2);
lean_dec(x_30);
return x_39;
}
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; uint8_t x_44; 
x_40 = lean_ctor_get(x_1, 1);
lean_inc(x_40);
lean_dec(x_1);
x_41 = lean_unsigned_to_nat(0u);
x_42 = lean_array_get_size(x_40);
x_43 = lean_box(0);
x_44 = lean_nat_dec_lt(x_41, x_42);
if (x_44 == 0)
{
lean_object* x_45; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_2);
x_45 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_8);
return x_45;
}
else
{
uint8_t x_46; 
x_46 = lean_nat_dec_le(x_42, x_42);
if (x_46 == 0)
{
lean_object* x_47; 
lean_dec(x_42);
lean_dec(x_40);
lean_dec(x_2);
x_47 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_47, 0, x_43);
lean_ctor_set(x_47, 1, x_8);
return x_47;
}
else
{
size_t x_48; size_t x_49; lean_object* x_50; 
x_48 = lean_usize_of_nat(x_41);
x_49 = lean_usize_of_nat(x_42);
lean_dec(x_42);
x_50 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visitLetValue_spec__0___redArg(x_40, x_48, x_49, x_43, x_2, x_3, x_8);
lean_dec(x_2);
lean_dec(x_40);
return x_50;
}
}
}
}
case 4:
{
lean_object* x_51; lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_51 = lean_ctor_get(x_1, 0);
lean_inc(x_51);
lean_dec(x_1);
x_52 = lean_ctor_get(x_51, 2);
lean_inc(x_52);
x_53 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_52, x_2, x_3, x_8);
x_54 = !lean_is_exclusive(x_53);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; uint8_t x_61; 
x_55 = lean_ctor_get(x_53, 1);
x_56 = lean_ctor_get(x_53, 0);
lean_dec(x_56);
x_57 = lean_ctor_get(x_51, 3);
lean_inc(x_57);
lean_dec(x_51);
x_58 = lean_unsigned_to_nat(0u);
x_59 = lean_array_get_size(x_57);
x_60 = lean_box(0);
x_61 = lean_nat_dec_lt(x_58, x_59);
if (x_61 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_2);
lean_ctor_set(x_53, 0, x_60);
return x_53;
}
else
{
uint8_t x_62; 
x_62 = lean_nat_dec_le(x_59, x_59);
if (x_62 == 0)
{
lean_dec(x_59);
lean_dec(x_57);
lean_dec(x_2);
lean_ctor_set(x_53, 0, x_60);
return x_53;
}
else
{
size_t x_63; size_t x_64; lean_object* x_65; 
lean_free_object(x_53);
x_63 = lean_usize_of_nat(x_58);
x_64 = lean_usize_of_nat(x_59);
lean_dec(x_59);
x_65 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_57, x_63, x_64, x_60, x_2, x_3, x_4, x_5, x_6, x_7, x_55);
lean_dec(x_57);
return x_65;
}
}
}
else
{
lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; uint8_t x_71; 
x_66 = lean_ctor_get(x_53, 1);
lean_inc(x_66);
lean_dec(x_53);
x_67 = lean_ctor_get(x_51, 3);
lean_inc(x_67);
lean_dec(x_51);
x_68 = lean_unsigned_to_nat(0u);
x_69 = lean_array_get_size(x_67);
x_70 = lean_box(0);
x_71 = lean_nat_dec_lt(x_68, x_69);
if (x_71 == 0)
{
lean_object* x_72; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_2);
x_72 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_72, 0, x_70);
lean_ctor_set(x_72, 1, x_66);
return x_72;
}
else
{
uint8_t x_73; 
x_73 = lean_nat_dec_le(x_69, x_69);
if (x_73 == 0)
{
lean_object* x_74; 
lean_dec(x_69);
lean_dec(x_67);
lean_dec(x_2);
x_74 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_74, 0, x_70);
lean_ctor_set(x_74, 1, x_66);
return x_74;
}
else
{
size_t x_75; size_t x_76; lean_object* x_77; 
x_75 = lean_usize_of_nat(x_68);
x_76 = lean_usize_of_nat(x_69);
lean_dec(x_69);
x_77 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_67, x_75, x_76, x_70, x_2, x_3, x_4, x_5, x_6, x_7, x_66);
lean_dec(x_67);
return x_77;
}
}
}
}
case 5:
{
lean_object* x_78; lean_object* x_79; 
x_78 = lean_ctor_get(x_1, 0);
lean_inc(x_78);
lean_dec(x_1);
x_79 = l_Lean_Compiler_LCNF_FindUsed_visitFVar___redArg(x_78, x_2, x_3, x_8);
lean_dec(x_2);
return x_79;
}
case 6:
{
lean_object* x_80; lean_object* x_81; 
lean_dec(x_2);
lean_dec(x_1);
x_80 = lean_box(0);
x_81 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_81, 0, x_80);
lean_ctor_set(x_81, 1, x_8);
return x_81;
}
default: 
{
lean_object* x_82; lean_object* x_83; 
x_82 = lean_ctor_get(x_1, 0);
lean_inc(x_82);
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
lean_dec(x_1);
x_9 = x_82;
x_10 = x_83;
x_11 = x_2;
x_12 = x_3;
x_13 = x_4;
x_14 = x_5;
x_15 = x_6;
x_16 = x_7;
x_17 = x_8;
goto block_22;
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_9, 4);
lean_inc(x_18);
lean_dec(x_9);
lean_inc(x_11);
x_19 = l_Lean_Compiler_LCNF_FindUsed_visit(x_18, x_11, x_12, x_13, x_14, x_15, x_16, x_17);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
x_1 = x_10;
x_2 = x_11;
x_3 = x_12;
x_4 = x_13;
x_5 = x_14;
x_6 = x_15;
x_7 = x_16;
x_8 = x_20;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_visit_spec__0(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_visit___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Compiler_LCNF_FindUsed_visit(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
lean_dec(x_2);
x_11 = lean_apply_8(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
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
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; uint8_t x_47; 
x_43 = lean_box(0);
x_44 = lean_ctor_get(x_1, 3);
lean_inc(x_44);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_array_get_size(x_44);
x_47 = lean_nat_dec_lt(x_45, x_46);
if (x_47 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_7 = x_43;
goto block_42;
}
else
{
uint8_t x_48; 
x_48 = lean_nat_dec_le(x_46, x_46);
if (x_48 == 0)
{
lean_dec(x_46);
lean_dec(x_44);
x_7 = x_43;
goto block_42;
}
else
{
size_t x_49; size_t x_50; lean_object* x_51; 
x_49 = lean_usize_of_nat(x_45);
x_50 = lean_usize_of_nat(x_46);
lean_dec(x_46);
x_51 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(x_44, x_49, x_50, x_43);
lean_dec(x_44);
x_7 = x_51;
goto block_42;
}
}
block_42:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_box(0);
x_9 = lean_st_mk_ref(x_8, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_ctor_get(x_9, 1);
x_13 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FindUsed_visit___boxed), 8, 0);
x_14 = lean_ctor_get(x_1, 4);
lean_inc(x_14);
lean_ctor_set(x_9, 1, x_7);
lean_ctor_set(x_9, 0, x_1);
lean_inc(x_11);
x_15 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(x_13, x_14, x_9, x_11, x_2, x_3, x_4, x_5, x_12);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; uint8_t x_18; 
x_16 = lean_ctor_get(x_15, 1);
lean_inc(x_16);
lean_dec(x_15);
x_17 = lean_st_ref_get(x_11, x_16);
lean_dec(x_11);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
return x_17;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_ctor_get(x_17, 1);
lean_inc(x_20);
lean_inc(x_19);
lean_dec(x_17);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_19);
lean_ctor_set(x_21, 1, x_20);
return x_21;
}
}
else
{
uint8_t x_22; 
lean_dec(x_11);
x_22 = !lean_is_exclusive(x_15);
if (x_22 == 0)
{
return x_15;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; 
x_23 = lean_ctor_get(x_15, 0);
x_24 = lean_ctor_get(x_15, 1);
lean_inc(x_24);
lean_inc(x_23);
lean_dec(x_15);
x_25 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_25, 0, x_23);
lean_ctor_set(x_25, 1, x_24);
return x_25;
}
}
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_26 = lean_ctor_get(x_9, 0);
x_27 = lean_ctor_get(x_9, 1);
lean_inc(x_27);
lean_inc(x_26);
lean_dec(x_9);
x_28 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_FindUsed_visit___boxed), 8, 0);
x_29 = lean_ctor_get(x_1, 4);
lean_inc(x_29);
x_30 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_30, 0, x_1);
lean_ctor_set(x_30, 1, x_7);
lean_inc(x_26);
x_31 = l_Lean_Compiler_LCNF_DeclValue_forCodeM___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__0(x_28, x_29, x_30, x_26, x_2, x_3, x_4, x_5, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_32 = lean_ctor_get(x_31, 1);
lean_inc(x_32);
lean_dec(x_31);
x_33 = lean_st_ref_get(x_26, x_32);
lean_dec(x_26);
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
if (lean_is_scalar(x_36)) {
 x_37 = lean_alloc_ctor(0, 2, 0);
} else {
 x_37 = x_36;
}
lean_ctor_set(x_37, 0, x_34);
lean_ctor_set(x_37, 1, x_35);
return x_37;
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_dec(x_26);
x_38 = lean_ctor_get(x_31, 0);
lean_inc(x_38);
x_39 = lean_ctor_get(x_31, 1);
lean_inc(x_39);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_40 = x_31;
} else {
 lean_dec_ref(x_31);
 x_40 = lean_box(0);
}
if (lean_is_scalar(x_40)) {
 x_41 = lean_alloc_ctor(1, 2, 0);
} else {
 x_41 = x_40;
}
lean_ctor_set(x_41, 0, x_38);
lean_ctor_set(x_41, 1, x_39);
return x_41;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_FindUsed_collectUsedParams_spec__1(x_1, x_5, x_6, x_4);
lean_dec(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget(x_1, x_3);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_17, x_25);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_18);
if (x_23 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_6 = x_28;
x_7 = x_5;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_array_fget(x_24, x_17);
lean_dec(x_17);
lean_dec(x_24);
x_30 = lean_array_push(x_16, x_29);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_27);
lean_ctor_set(x_31, 1, x_30);
x_6 = x_31;
x_7 = x_5;
goto block_12;
}
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; uint8_t x_10; 
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
lean_dec(x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_2);
lean_ctor_set(x_11, 1, x_8);
return x_11;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_array_fget(x_2, x_1);
if (lean_obj_tag(x_12) == 0)
{
lean_object* x_29; 
x_29 = lean_ctor_get(x_12, 2);
lean_inc(x_29);
x_13 = x_29;
goto block_28;
}
else
{
lean_object* x_30; 
x_30 = lean_ctor_get(x_12, 0);
lean_inc(x_30);
x_13 = x_30;
goto block_28;
}
block_28:
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; uint8_t x_20; 
x_14 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_13, x_3, x_4, x_5, x_6, x_7, x_8);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_14, 1);
lean_inc(x_16);
lean_dec(x_14);
lean_inc(x_12);
x_17 = l___private_Lean_Compiler_LCNF_Basic_0__Lean_Compiler_LCNF_updateAltCodeImp(x_12, x_15);
x_18 = lean_ptr_addr(x_12);
lean_dec(x_12);
x_19 = lean_ptr_addr(x_17);
x_20 = lean_usize_dec_eq(x_18, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_unsigned_to_nat(1u);
x_22 = lean_nat_add(x_1, x_21);
x_23 = lean_array_fset(x_2, x_1, x_17);
lean_dec(x_1);
x_1 = x_22;
x_2 = x_23;
x_8 = x_16;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec(x_17);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_1, x_25);
lean_dec(x_1);
x_1 = x_26;
x_8 = x_16;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
switch (lean_obj_tag(x_1)) {
case 0:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_ctor_get(x_1, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_81, 3);
lean_inc(x_82);
if (lean_obj_tag(x_82) == 3)
{
lean_object* x_83; uint8_t x_84; 
x_83 = lean_ctor_get(x_1, 1);
lean_inc(x_83);
x_84 = !lean_is_exclusive(x_82);
if (x_84 == 0)
{
lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; uint8_t x_89; 
x_85 = lean_ctor_get(x_82, 0);
x_86 = lean_ctor_get(x_82, 2);
x_87 = lean_ctor_get(x_82, 1);
lean_dec(x_87);
x_88 = lean_ctor_get(x_2, 0);
x_89 = lean_name_eq(x_85, x_88);
lean_dec(x_85);
if (x_89 == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; uint8_t x_94; size_t x_103; size_t x_104; uint8_t x_105; 
lean_free_object(x_82);
lean_dec(x_86);
lean_inc(x_83);
x_90 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_83, x_2, x_3, x_4, x_5, x_6, x_7);
x_91 = lean_ctor_get(x_90, 0);
lean_inc(x_91);
x_92 = lean_ctor_get(x_90, 1);
lean_inc(x_92);
if (lean_is_exclusive(x_90)) {
 lean_ctor_release(x_90, 0);
 lean_ctor_release(x_90, 1);
 x_93 = x_90;
} else {
 lean_dec_ref(x_90);
 x_93 = lean_box(0);
}
x_103 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_104 = lean_ptr_addr(x_91);
x_105 = lean_usize_dec_eq(x_103, x_104);
if (x_105 == 0)
{
x_94 = x_89;
goto block_102;
}
else
{
size_t x_106; uint8_t x_107; 
x_106 = lean_ptr_addr(x_81);
x_107 = lean_usize_dec_eq(x_106, x_106);
x_94 = x_107;
goto block_102;
}
block_102:
{
if (x_94 == 0)
{
uint8_t x_95; 
x_95 = !lean_is_exclusive(x_1);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; 
x_96 = lean_ctor_get(x_1, 1);
lean_dec(x_96);
x_97 = lean_ctor_get(x_1, 0);
lean_dec(x_97);
lean_ctor_set(x_1, 1, x_91);
if (lean_is_scalar(x_93)) {
 x_98 = lean_alloc_ctor(0, 2, 0);
} else {
 x_98 = x_93;
}
lean_ctor_set(x_98, 0, x_1);
lean_ctor_set(x_98, 1, x_92);
return x_98;
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec(x_1);
x_99 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_99, 0, x_81);
lean_ctor_set(x_99, 1, x_91);
if (lean_is_scalar(x_93)) {
 x_100 = lean_alloc_ctor(0, 2, 0);
} else {
 x_100 = x_93;
}
lean_ctor_set(x_100, 0, x_99);
lean_ctor_set(x_100, 1, x_92);
return x_100;
}
}
else
{
lean_object* x_101; 
lean_dec(x_91);
lean_dec(x_81);
if (lean_is_scalar(x_93)) {
 x_101 = lean_alloc_ctor(0, 2, 0);
} else {
 x_101 = x_93;
}
lean_ctor_set(x_101, 0, x_1);
lean_ctor_set(x_101, 1, x_92);
return x_101;
}
}
}
else
{
lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; size_t x_114; size_t x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; uint8_t x_129; size_t x_145; size_t x_146; uint8_t x_147; 
x_108 = lean_unsigned_to_nat(0u);
x_109 = lean_mk_empty_array_with_capacity(x_108);
x_110 = lean_array_get_size(x_86);
x_111 = l_Array_toSubarray___redArg(x_86, x_108, x_110);
x_112 = lean_ctor_get(x_2, 2);
x_113 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_113, 0, x_111);
lean_ctor_set(x_113, 1, x_109);
x_114 = lean_array_size(x_112);
x_115 = lean_usize_of_nat(x_108);
x_116 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_112, x_114, x_115, x_113, x_7);
x_117 = lean_ctor_get(x_116, 0);
lean_inc(x_117);
x_118 = lean_ctor_get(x_116, 1);
lean_inc(x_118);
lean_dec(x_116);
x_119 = lean_ctor_get(x_117, 1);
lean_inc(x_119);
lean_dec(x_117);
x_120 = lean_ctor_get(x_2, 1);
x_121 = lean_box(0);
lean_inc(x_120);
lean_ctor_set(x_82, 2, x_119);
lean_ctor_set(x_82, 1, x_121);
lean_ctor_set(x_82, 0, x_120);
lean_inc(x_81);
x_122 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_81, x_82, x_3, x_4, x_5, x_6, x_118);
x_123 = lean_ctor_get(x_122, 0);
lean_inc(x_123);
x_124 = lean_ctor_get(x_122, 1);
lean_inc(x_124);
lean_dec(x_122);
lean_inc(x_83);
x_125 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_83, x_2, x_3, x_4, x_5, x_6, x_124);
x_126 = lean_ctor_get(x_125, 0);
lean_inc(x_126);
x_127 = lean_ctor_get(x_125, 1);
lean_inc(x_127);
if (lean_is_exclusive(x_125)) {
 lean_ctor_release(x_125, 0);
 lean_ctor_release(x_125, 1);
 x_128 = x_125;
} else {
 lean_dec_ref(x_125);
 x_128 = lean_box(0);
}
x_145 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_146 = lean_ptr_addr(x_126);
x_147 = lean_usize_dec_eq(x_145, x_146);
if (x_147 == 0)
{
lean_dec(x_81);
x_129 = x_147;
goto block_144;
}
else
{
size_t x_148; size_t x_149; uint8_t x_150; 
x_148 = lean_ptr_addr(x_81);
lean_dec(x_81);
x_149 = lean_ptr_addr(x_123);
x_150 = lean_usize_dec_eq(x_148, x_149);
x_129 = x_150;
goto block_144;
}
block_144:
{
if (x_129 == 0)
{
if (x_89 == 0)
{
lean_object* x_130; 
lean_dec(x_126);
lean_dec(x_123);
if (lean_is_scalar(x_128)) {
 x_130 = lean_alloc_ctor(0, 2, 0);
} else {
 x_130 = x_128;
}
lean_ctor_set(x_130, 0, x_1);
lean_ctor_set(x_130, 1, x_127);
return x_130;
}
else
{
uint8_t x_131; 
x_131 = !lean_is_exclusive(x_1);
if (x_131 == 0)
{
lean_object* x_132; lean_object* x_133; lean_object* x_134; 
x_132 = lean_ctor_get(x_1, 1);
lean_dec(x_132);
x_133 = lean_ctor_get(x_1, 0);
lean_dec(x_133);
lean_ctor_set(x_1, 1, x_126);
lean_ctor_set(x_1, 0, x_123);
if (lean_is_scalar(x_128)) {
 x_134 = lean_alloc_ctor(0, 2, 0);
} else {
 x_134 = x_128;
}
lean_ctor_set(x_134, 0, x_1);
lean_ctor_set(x_134, 1, x_127);
return x_134;
}
else
{
lean_object* x_135; lean_object* x_136; 
lean_dec(x_1);
x_135 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_135, 0, x_123);
lean_ctor_set(x_135, 1, x_126);
if (lean_is_scalar(x_128)) {
 x_136 = lean_alloc_ctor(0, 2, 0);
} else {
 x_136 = x_128;
}
lean_ctor_set(x_136, 0, x_135);
lean_ctor_set(x_136, 1, x_127);
return x_136;
}
}
}
else
{
if (x_89 == 0)
{
uint8_t x_137; 
x_137 = !lean_is_exclusive(x_1);
if (x_137 == 0)
{
lean_object* x_138; lean_object* x_139; lean_object* x_140; 
x_138 = lean_ctor_get(x_1, 1);
lean_dec(x_138);
x_139 = lean_ctor_get(x_1, 0);
lean_dec(x_139);
lean_ctor_set(x_1, 1, x_126);
lean_ctor_set(x_1, 0, x_123);
if (lean_is_scalar(x_128)) {
 x_140 = lean_alloc_ctor(0, 2, 0);
} else {
 x_140 = x_128;
}
lean_ctor_set(x_140, 0, x_1);
lean_ctor_set(x_140, 1, x_127);
return x_140;
}
else
{
lean_object* x_141; lean_object* x_142; 
lean_dec(x_1);
x_141 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_141, 0, x_123);
lean_ctor_set(x_141, 1, x_126);
if (lean_is_scalar(x_128)) {
 x_142 = lean_alloc_ctor(0, 2, 0);
} else {
 x_142 = x_128;
}
lean_ctor_set(x_142, 0, x_141);
lean_ctor_set(x_142, 1, x_127);
return x_142;
}
}
else
{
lean_object* x_143; 
lean_dec(x_126);
lean_dec(x_123);
if (lean_is_scalar(x_128)) {
 x_143 = lean_alloc_ctor(0, 2, 0);
} else {
 x_143 = x_128;
}
lean_ctor_set(x_143, 0, x_1);
lean_ctor_set(x_143, 1, x_127);
return x_143;
}
}
}
}
}
else
{
lean_object* x_151; lean_object* x_152; lean_object* x_153; uint8_t x_154; 
x_151 = lean_ctor_get(x_82, 0);
x_152 = lean_ctor_get(x_82, 2);
lean_inc(x_152);
lean_inc(x_151);
lean_dec(x_82);
x_153 = lean_ctor_get(x_2, 0);
x_154 = lean_name_eq(x_151, x_153);
lean_dec(x_151);
if (x_154 == 0)
{
lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; uint8_t x_159; size_t x_165; size_t x_166; uint8_t x_167; 
lean_dec(x_152);
lean_inc(x_83);
x_155 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_83, x_2, x_3, x_4, x_5, x_6, x_7);
x_156 = lean_ctor_get(x_155, 0);
lean_inc(x_156);
x_157 = lean_ctor_get(x_155, 1);
lean_inc(x_157);
if (lean_is_exclusive(x_155)) {
 lean_ctor_release(x_155, 0);
 lean_ctor_release(x_155, 1);
 x_158 = x_155;
} else {
 lean_dec_ref(x_155);
 x_158 = lean_box(0);
}
x_165 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_166 = lean_ptr_addr(x_156);
x_167 = lean_usize_dec_eq(x_165, x_166);
if (x_167 == 0)
{
x_159 = x_154;
goto block_164;
}
else
{
size_t x_168; uint8_t x_169; 
x_168 = lean_ptr_addr(x_81);
x_169 = lean_usize_dec_eq(x_168, x_168);
x_159 = x_169;
goto block_164;
}
block_164:
{
if (x_159 == 0)
{
lean_object* x_160; lean_object* x_161; lean_object* x_162; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_160 = x_1;
} else {
 lean_dec_ref(x_1);
 x_160 = lean_box(0);
}
if (lean_is_scalar(x_160)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_160;
}
lean_ctor_set(x_161, 0, x_81);
lean_ctor_set(x_161, 1, x_156);
if (lean_is_scalar(x_158)) {
 x_162 = lean_alloc_ctor(0, 2, 0);
} else {
 x_162 = x_158;
}
lean_ctor_set(x_162, 0, x_161);
lean_ctor_set(x_162, 1, x_157);
return x_162;
}
else
{
lean_object* x_163; 
lean_dec(x_156);
lean_dec(x_81);
if (lean_is_scalar(x_158)) {
 x_163 = lean_alloc_ctor(0, 2, 0);
} else {
 x_163 = x_158;
}
lean_ctor_set(x_163, 0, x_1);
lean_ctor_set(x_163, 1, x_157);
return x_163;
}
}
}
else
{
lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; size_t x_176; size_t x_177; lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; uint8_t x_192; size_t x_202; size_t x_203; uint8_t x_204; 
x_170 = lean_unsigned_to_nat(0u);
x_171 = lean_mk_empty_array_with_capacity(x_170);
x_172 = lean_array_get_size(x_152);
x_173 = l_Array_toSubarray___redArg(x_152, x_170, x_172);
x_174 = lean_ctor_get(x_2, 2);
x_175 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_175, 0, x_173);
lean_ctor_set(x_175, 1, x_171);
x_176 = lean_array_size(x_174);
x_177 = lean_usize_of_nat(x_170);
x_178 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_174, x_176, x_177, x_175, x_7);
x_179 = lean_ctor_get(x_178, 0);
lean_inc(x_179);
x_180 = lean_ctor_get(x_178, 1);
lean_inc(x_180);
lean_dec(x_178);
x_181 = lean_ctor_get(x_179, 1);
lean_inc(x_181);
lean_dec(x_179);
x_182 = lean_ctor_get(x_2, 1);
x_183 = lean_box(0);
lean_inc(x_182);
x_184 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_184, 0, x_182);
lean_ctor_set(x_184, 1, x_183);
lean_ctor_set(x_184, 2, x_181);
lean_inc(x_81);
x_185 = l_Lean_Compiler_LCNF_LetDecl_updateValue(x_81, x_184, x_3, x_4, x_5, x_6, x_180);
x_186 = lean_ctor_get(x_185, 0);
lean_inc(x_186);
x_187 = lean_ctor_get(x_185, 1);
lean_inc(x_187);
lean_dec(x_185);
lean_inc(x_83);
x_188 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_83, x_2, x_3, x_4, x_5, x_6, x_187);
x_189 = lean_ctor_get(x_188, 0);
lean_inc(x_189);
x_190 = lean_ctor_get(x_188, 1);
lean_inc(x_190);
if (lean_is_exclusive(x_188)) {
 lean_ctor_release(x_188, 0);
 lean_ctor_release(x_188, 1);
 x_191 = x_188;
} else {
 lean_dec_ref(x_188);
 x_191 = lean_box(0);
}
x_202 = lean_ptr_addr(x_83);
lean_dec(x_83);
x_203 = lean_ptr_addr(x_189);
x_204 = lean_usize_dec_eq(x_202, x_203);
if (x_204 == 0)
{
lean_dec(x_81);
x_192 = x_204;
goto block_201;
}
else
{
size_t x_205; size_t x_206; uint8_t x_207; 
x_205 = lean_ptr_addr(x_81);
lean_dec(x_81);
x_206 = lean_ptr_addr(x_186);
x_207 = lean_usize_dec_eq(x_205, x_206);
x_192 = x_207;
goto block_201;
}
block_201:
{
if (x_192 == 0)
{
if (x_154 == 0)
{
lean_object* x_193; 
lean_dec(x_189);
lean_dec(x_186);
if (lean_is_scalar(x_191)) {
 x_193 = lean_alloc_ctor(0, 2, 0);
} else {
 x_193 = x_191;
}
lean_ctor_set(x_193, 0, x_1);
lean_ctor_set(x_193, 1, x_190);
return x_193;
}
else
{
lean_object* x_194; lean_object* x_195; lean_object* x_196; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_194 = x_1;
} else {
 lean_dec_ref(x_1);
 x_194 = lean_box(0);
}
if (lean_is_scalar(x_194)) {
 x_195 = lean_alloc_ctor(0, 2, 0);
} else {
 x_195 = x_194;
}
lean_ctor_set(x_195, 0, x_186);
lean_ctor_set(x_195, 1, x_189);
if (lean_is_scalar(x_191)) {
 x_196 = lean_alloc_ctor(0, 2, 0);
} else {
 x_196 = x_191;
}
lean_ctor_set(x_196, 0, x_195);
lean_ctor_set(x_196, 1, x_190);
return x_196;
}
}
else
{
if (x_154 == 0)
{
lean_object* x_197; lean_object* x_198; lean_object* x_199; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 lean_ctor_release(x_1, 1);
 x_197 = x_1;
} else {
 lean_dec_ref(x_1);
 x_197 = lean_box(0);
}
if (lean_is_scalar(x_197)) {
 x_198 = lean_alloc_ctor(0, 2, 0);
} else {
 x_198 = x_197;
}
lean_ctor_set(x_198, 0, x_186);
lean_ctor_set(x_198, 1, x_189);
if (lean_is_scalar(x_191)) {
 x_199 = lean_alloc_ctor(0, 2, 0);
} else {
 x_199 = x_191;
}
lean_ctor_set(x_199, 0, x_198);
lean_ctor_set(x_199, 1, x_190);
return x_199;
}
else
{
lean_object* x_200; 
lean_dec(x_189);
lean_dec(x_186);
if (lean_is_scalar(x_191)) {
 x_200 = lean_alloc_ctor(0, 2, 0);
} else {
 x_200 = x_191;
}
lean_ctor_set(x_200, 0, x_1);
lean_ctor_set(x_200, 1, x_190);
return x_200;
}
}
}
}
}
}
else
{
lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; uint8_t x_213; size_t x_222; size_t x_223; uint8_t x_224; 
lean_dec(x_82);
x_208 = lean_ctor_get(x_1, 1);
lean_inc(x_208);
lean_inc(x_208);
x_209 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_208, x_2, x_3, x_4, x_5, x_6, x_7);
x_210 = lean_ctor_get(x_209, 0);
lean_inc(x_210);
x_211 = lean_ctor_get(x_209, 1);
lean_inc(x_211);
if (lean_is_exclusive(x_209)) {
 lean_ctor_release(x_209, 0);
 lean_ctor_release(x_209, 1);
 x_212 = x_209;
} else {
 lean_dec_ref(x_209);
 x_212 = lean_box(0);
}
x_222 = lean_ptr_addr(x_208);
lean_dec(x_208);
x_223 = lean_ptr_addr(x_210);
x_224 = lean_usize_dec_eq(x_222, x_223);
if (x_224 == 0)
{
x_213 = x_224;
goto block_221;
}
else
{
size_t x_225; uint8_t x_226; 
x_225 = lean_ptr_addr(x_81);
x_226 = lean_usize_dec_eq(x_225, x_225);
x_213 = x_226;
goto block_221;
}
block_221:
{
if (x_213 == 0)
{
uint8_t x_214; 
x_214 = !lean_is_exclusive(x_1);
if (x_214 == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; 
x_215 = lean_ctor_get(x_1, 1);
lean_dec(x_215);
x_216 = lean_ctor_get(x_1, 0);
lean_dec(x_216);
lean_ctor_set(x_1, 1, x_210);
if (lean_is_scalar(x_212)) {
 x_217 = lean_alloc_ctor(0, 2, 0);
} else {
 x_217 = x_212;
}
lean_ctor_set(x_217, 0, x_1);
lean_ctor_set(x_217, 1, x_211);
return x_217;
}
else
{
lean_object* x_218; lean_object* x_219; 
lean_dec(x_1);
x_218 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_218, 0, x_81);
lean_ctor_set(x_218, 1, x_210);
if (lean_is_scalar(x_212)) {
 x_219 = lean_alloc_ctor(0, 2, 0);
} else {
 x_219 = x_212;
}
lean_ctor_set(x_219, 0, x_218);
lean_ctor_set(x_219, 1, x_211);
return x_219;
}
}
else
{
lean_object* x_220; 
lean_dec(x_210);
lean_dec(x_81);
if (lean_is_scalar(x_212)) {
 x_220 = lean_alloc_ctor(0, 2, 0);
} else {
 x_220 = x_212;
}
lean_ctor_set(x_220, 0, x_1);
lean_ctor_set(x_220, 1, x_211);
return x_220;
}
}
}
}
case 1:
{
lean_object* x_227; lean_object* x_228; 
x_227 = lean_ctor_get(x_1, 0);
lean_inc(x_227);
x_228 = lean_ctor_get(x_1, 1);
lean_inc(x_228);
x_24 = x_227;
x_25 = x_228;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
goto block_80;
}
case 2:
{
lean_object* x_229; lean_object* x_230; 
x_229 = lean_ctor_get(x_1, 0);
lean_inc(x_229);
x_230 = lean_ctor_get(x_1, 1);
lean_inc(x_230);
x_24 = x_229;
x_25 = x_230;
x_26 = x_2;
x_27 = x_3;
x_28 = x_4;
x_29 = x_5;
x_30 = x_6;
x_31 = x_7;
goto block_80;
}
case 4:
{
lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; uint8_t x_235; 
x_231 = lean_ctor_get(x_1, 0);
lean_inc(x_231);
x_232 = lean_ctor_get(x_231, 3);
lean_inc(x_232);
x_233 = lean_unsigned_to_nat(0u);
lean_inc(x_232);
x_234 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(x_233, x_232, x_2, x_3, x_4, x_5, x_6, x_7);
x_235 = !lean_is_exclusive(x_234);
if (x_235 == 0)
{
lean_object* x_236; size_t x_237; size_t x_238; uint8_t x_239; 
x_236 = lean_ctor_get(x_234, 0);
x_237 = lean_ptr_addr(x_232);
lean_dec(x_232);
x_238 = lean_ptr_addr(x_236);
x_239 = lean_usize_dec_eq(x_237, x_238);
if (x_239 == 0)
{
uint8_t x_240; 
x_240 = !lean_is_exclusive(x_1);
if (x_240 == 0)
{
lean_object* x_241; lean_object* x_242; lean_object* x_243; lean_object* x_244; lean_object* x_245; 
x_241 = lean_ctor_get(x_1, 0);
lean_dec(x_241);
x_242 = lean_ctor_get(x_231, 0);
lean_inc(x_242);
x_243 = lean_ctor_get(x_231, 1);
lean_inc(x_243);
x_244 = lean_ctor_get(x_231, 2);
lean_inc(x_244);
lean_dec(x_231);
x_245 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_245, 0, x_242);
lean_ctor_set(x_245, 1, x_243);
lean_ctor_set(x_245, 2, x_244);
lean_ctor_set(x_245, 3, x_236);
lean_ctor_set(x_1, 0, x_245);
lean_ctor_set(x_234, 0, x_1);
return x_234;
}
else
{
lean_object* x_246; lean_object* x_247; lean_object* x_248; lean_object* x_249; lean_object* x_250; 
lean_dec(x_1);
x_246 = lean_ctor_get(x_231, 0);
lean_inc(x_246);
x_247 = lean_ctor_get(x_231, 1);
lean_inc(x_247);
x_248 = lean_ctor_get(x_231, 2);
lean_inc(x_248);
lean_dec(x_231);
x_249 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_249, 0, x_246);
lean_ctor_set(x_249, 1, x_247);
lean_ctor_set(x_249, 2, x_248);
lean_ctor_set(x_249, 3, x_236);
x_250 = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(x_250, 0, x_249);
lean_ctor_set(x_234, 0, x_250);
return x_234;
}
}
else
{
lean_dec(x_236);
lean_dec(x_231);
lean_ctor_set(x_234, 0, x_1);
return x_234;
}
}
else
{
lean_object* x_251; lean_object* x_252; size_t x_253; size_t x_254; uint8_t x_255; 
x_251 = lean_ctor_get(x_234, 0);
x_252 = lean_ctor_get(x_234, 1);
lean_inc(x_252);
lean_inc(x_251);
lean_dec(x_234);
x_253 = lean_ptr_addr(x_232);
lean_dec(x_232);
x_254 = lean_ptr_addr(x_251);
x_255 = lean_usize_dec_eq(x_253, x_254);
if (x_255 == 0)
{
lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; lean_object* x_262; 
if (lean_is_exclusive(x_1)) {
 lean_ctor_release(x_1, 0);
 x_256 = x_1;
} else {
 lean_dec_ref(x_1);
 x_256 = lean_box(0);
}
x_257 = lean_ctor_get(x_231, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_231, 1);
lean_inc(x_258);
x_259 = lean_ctor_get(x_231, 2);
lean_inc(x_259);
lean_dec(x_231);
x_260 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_260, 0, x_257);
lean_ctor_set(x_260, 1, x_258);
lean_ctor_set(x_260, 2, x_259);
lean_ctor_set(x_260, 3, x_251);
if (lean_is_scalar(x_256)) {
 x_261 = lean_alloc_ctor(4, 1, 0);
} else {
 x_261 = x_256;
}
lean_ctor_set(x_261, 0, x_260);
x_262 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_262, 0, x_261);
lean_ctor_set(x_262, 1, x_252);
return x_262;
}
else
{
lean_object* x_263; 
lean_dec(x_251);
lean_dec(x_231);
x_263 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_263, 0, x_1);
lean_ctor_set(x_263, 1, x_252);
return x_263;
}
}
}
default: 
{
lean_object* x_264; 
x_264 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_264, 0, x_1);
lean_ctor_set(x_264, 1, x_7);
return x_264;
}
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
lean_dec(x_1);
x_12 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_12, 0, x_10);
lean_ctor_set(x_12, 1, x_8);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_9);
return x_13;
}
else
{
lean_object* x_14; 
lean_dec(x_10);
lean_dec(x_8);
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_1);
lean_ctor_set(x_14, 1, x_9);
return x_14;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_1);
x_20 = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_17);
return x_21;
}
else
{
lean_object* x_22; 
lean_dec(x_18);
lean_dec(x_16);
x_22 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_22, 0, x_1);
lean_ctor_set(x_22, 1, x_17);
return x_22;
}
}
block_80:
{
lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_32 = lean_ctor_get(x_24, 4);
lean_inc(x_32);
x_33 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_32, x_26, x_27, x_28, x_29, x_30, x_31);
x_34 = lean_ctor_get(x_33, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_33, 1);
lean_inc(x_35);
lean_dec(x_33);
x_36 = lean_ctor_get(x_24, 3);
lean_inc(x_36);
x_37 = lean_ctor_get(x_24, 2);
lean_inc(x_37);
x_38 = l___private_Lean_Compiler_LCNF_CompilerM_0__Lean_Compiler_LCNF_updateFunDeclImp___redArg(x_24, x_36, x_37, x_34, x_28, x_35);
x_39 = lean_ctor_get(x_38, 0);
lean_inc(x_39);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_25, x_26, x_27, x_28, x_29, x_30, x_40);
switch (lean_obj_tag(x_1)) {
case 1:
{
lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; size_t x_46; size_t x_47; uint8_t x_48; 
x_42 = lean_ctor_get(x_41, 0);
lean_inc(x_42);
x_43 = lean_ctor_get(x_41, 1);
lean_inc(x_43);
lean_dec(x_41);
x_44 = lean_ctor_get(x_1, 0);
lean_inc(x_44);
x_45 = lean_ctor_get(x_1, 1);
lean_inc(x_45);
x_46 = lean_ptr_addr(x_45);
lean_dec(x_45);
x_47 = lean_ptr_addr(x_42);
x_48 = lean_usize_dec_eq(x_46, x_47);
if (x_48 == 0)
{
lean_dec(x_44);
x_8 = x_42;
x_9 = x_43;
x_10 = x_39;
x_11 = x_48;
goto block_15;
}
else
{
size_t x_49; size_t x_50; uint8_t x_51; 
x_49 = lean_ptr_addr(x_44);
lean_dec(x_44);
x_50 = lean_ptr_addr(x_39);
x_51 = lean_usize_dec_eq(x_49, x_50);
x_8 = x_42;
x_9 = x_43;
x_10 = x_39;
x_11 = x_51;
goto block_15;
}
}
case 2:
{
lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; size_t x_56; size_t x_57; uint8_t x_58; 
x_52 = lean_ctor_get(x_41, 0);
lean_inc(x_52);
x_53 = lean_ctor_get(x_41, 1);
lean_inc(x_53);
lean_dec(x_41);
x_54 = lean_ctor_get(x_1, 0);
lean_inc(x_54);
x_55 = lean_ctor_get(x_1, 1);
lean_inc(x_55);
x_56 = lean_ptr_addr(x_55);
lean_dec(x_55);
x_57 = lean_ptr_addr(x_52);
x_58 = lean_usize_dec_eq(x_56, x_57);
if (x_58 == 0)
{
lean_dec(x_54);
x_16 = x_52;
x_17 = x_53;
x_18 = x_39;
x_19 = x_58;
goto block_23;
}
else
{
size_t x_59; size_t x_60; uint8_t x_61; 
x_59 = lean_ptr_addr(x_54);
lean_dec(x_54);
x_60 = lean_ptr_addr(x_39);
x_61 = lean_usize_dec_eq(x_59, x_60);
x_16 = x_52;
x_17 = x_53;
x_18 = x_39;
x_19 = x_61;
goto block_23;
}
}
default: 
{
uint8_t x_62; 
lean_dec(x_39);
lean_dec(x_1);
x_62 = !lean_is_exclusive(x_41);
if (x_62 == 0)
{
lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; 
x_63 = lean_ctor_get(x_41, 0);
lean_dec(x_63);
x_64 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_65 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_66 = lean_unsigned_to_nat(305u);
x_67 = lean_unsigned_to_nat(9u);
x_68 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_69 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_64, x_65, x_66, x_67, x_68);
lean_dec(x_68);
lean_dec(x_65);
lean_dec(x_64);
x_70 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_69);
lean_ctor_set(x_41, 0, x_70);
return x_41;
}
else
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; 
x_71 = lean_ctor_get(x_41, 1);
lean_inc(x_71);
lean_dec(x_41);
x_72 = lean_mk_string_unchecked("Lean.Compiler.LCNF.Basic", 24, 24);
x_73 = lean_mk_string_unchecked("_private.Lean.Compiler.LCNF.Basic.0.Lean.Compiler.LCNF.updateFunImp", 67, 67);
x_74 = lean_unsigned_to_nat(305u);
x_75 = lean_unsigned_to_nat(9u);
x_76 = lean_mk_string_unchecked("unreachable code has been reached", 33, 33);
x_77 = l___private_Init_Util_0__mkPanicMessageWithDecl(x_72, x_73, x_74, x_75, x_76);
lean_dec(x_76);
lean_dec(x_73);
lean_dec(x_72);
x_78 = l_panic___at___Lean_Compiler_LCNF_Code_instantiateValueLevelParams_instCode_spec__0(x_77);
x_79 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_79, 0, x_78);
lean_ctor_set(x_79, 1, x_71);
return x_79;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__0(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l___private_Init_Data_Array_BasicAux_0__mapMonoMImp_go___at___Lean_Compiler_LCNF_ReduceArity_reduce_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_ReduceArity_reduce(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(lean_object* x_1, uint8_t x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; 
x_6 = lean_usize_dec_lt(x_4, x_3);
if (x_6 == 0)
{
return x_5;
}
else
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_18; lean_object* x_19; 
x_7 = lean_array_uget(x_5, x_4);
x_8 = lean_box(0);
x_9 = lean_array_uset(x_5, x_4, x_8);
x_18 = lean_ctor_get(x_7, 0);
lean_inc(x_18);
lean_dec(x_7);
x_19 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_18);
lean_dec(x_18);
if (lean_obj_tag(x_19) == 0)
{
x_10 = x_2;
goto block_17;
}
else
{
lean_dec(x_19);
x_10 = x_6;
goto block_17;
}
block_17:
{
lean_object* x_11; size_t x_12; size_t x_13; lean_object* x_14; lean_object* x_15; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_usize_of_nat(x_11);
x_13 = lean_usize_add(x_4, x_12);
x_14 = lean_box(x_10);
x_15 = lean_array_uset(x_9, x_4, x_14);
x_4 = x_13;
x_5 = x_15;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
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
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_lt(x_3, x_2);
if (x_13 == 0)
{
lean_object* x_14; 
x_14 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_14, 0, x_4);
lean_ctor_set(x_14, 1, x_5);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_15 = lean_ctor_get(x_4, 0);
lean_inc(x_15);
x_16 = lean_ctor_get(x_4, 1);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_ctor_get(x_15, 1);
lean_inc(x_17);
x_18 = lean_ctor_get(x_15, 2);
lean_inc(x_18);
x_19 = lean_nat_dec_lt(x_17, x_18);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_dec(x_18);
lean_dec(x_17);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_15);
lean_ctor_set(x_20, 1, x_16);
x_21 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_21, 0, x_20);
lean_ctor_set(x_21, 1, x_5);
return x_21;
}
else
{
lean_object* x_22; uint8_t x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_22 = lean_array_uget(x_1, x_3);
x_23 = lean_unbox(x_22);
lean_dec(x_22);
x_24 = lean_ctor_get(x_15, 0);
lean_inc(x_24);
lean_dec(x_15);
x_25 = lean_unsigned_to_nat(1u);
x_26 = lean_nat_add(x_17, x_25);
lean_inc(x_24);
x_27 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_27, 0, x_24);
lean_ctor_set(x_27, 1, x_26);
lean_ctor_set(x_27, 2, x_18);
if (x_23 == 0)
{
lean_object* x_28; 
lean_dec(x_24);
lean_dec(x_17);
x_28 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_28, 0, x_27);
lean_ctor_set(x_28, 1, x_16);
x_6 = x_28;
x_7 = x_5;
goto block_12;
}
else
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_29 = lean_array_fget(x_24, x_17);
lean_dec(x_17);
lean_dec(x_24);
x_30 = l_Lean_Compiler_LCNF_Param_toArg(x_29);
lean_dec(x_29);
x_31 = lean_array_push(x_16, x_30);
x_32 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_32, 0, x_27);
lean_ctor_set(x_32, 1, x_31);
x_6 = x_32;
x_7 = x_5;
goto block_12;
}
}
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_3, x_9);
x_3 = x_10;
x_4 = x_6;
x_5 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_1, x_2, x_3, x_4, x_10);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(lean_object* x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_3, x_4);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_13 = lean_array_uget(x_2, x_3);
x_14 = lean_ctor_get(x_13, 0);
lean_inc(x_14);
x_15 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_14);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; 
x_16 = lean_array_push(x_5, x_13);
x_6 = x_16;
goto block_11;
}
else
{
lean_dec(x_15);
lean_dec(x_13);
x_6 = x_5;
goto block_11;
}
}
else
{
return x_5;
}
block_11:
{
lean_object* x_7; size_t x_8; size_t x_9; 
x_7 = lean_unsigned_to_nat(1u);
x_8 = lean_usize_of_nat(x_7);
x_9 = lean_usize_add(x_3, x_8);
x_3 = x_9;
x_5 = x_6;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
if (x_2 == 0)
{
lean_dec(x_14);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_6, x_14);
x_7 = x_17;
goto block_12;
}
}
else
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = lean_array_push(x_6, x_14);
x_7 = x_18;
goto block_12;
}
}
else
{
return x_6;
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_4 = x_10;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(lean_object* x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_13; 
x_13 = lean_usize_dec_eq(x_4, x_5);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = lean_array_uget(x_3, x_4);
x_15 = lean_ctor_get(x_14, 0);
lean_inc(x_15);
x_16 = l_Lean_RBNode_findCore___at_____private_Lean_Meta_FunInfo_0__Lean_Meta_getFunInfoAux_spec__0___redArg(x_1, x_15);
lean_dec(x_15);
if (lean_obj_tag(x_16) == 0)
{
if (x_2 == 0)
{
lean_dec(x_14);
x_7 = x_6;
goto block_12;
}
else
{
lean_object* x_17; 
x_17 = lean_array_push(x_6, x_14);
x_7 = x_17;
goto block_12;
}
}
else
{
lean_object* x_18; 
lean_dec(x_16);
x_18 = lean_array_push(x_6, x_14);
x_7 = x_18;
goto block_12;
}
}
else
{
return x_6;
}
block_12:
{
lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_usize_of_nat(x_8);
x_10 = lean_usize_add(x_4, x_9);
x_11 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4_spec__4(x_1, x_2, x_3, x_10, x_5, x_7);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
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
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___redArg(x_1, x_4, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7_spec__7(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_2, 3);
x_6 = l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7_spec__7(x_1, x_5);
lean_inc(x_4);
x_7 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_7, 0, x_4);
lean_ctor_set(x_7, 1, x_6);
x_1 = x_7;
x_2 = x_3;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_box(0);
x_3 = l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7_spec__7(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_Expr_fvar___override(x_5);
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
x_11 = l_Lean_Expr_fvar___override(x_9);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10(lean_object* x_1, lean_object* x_2) {
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
x_7 = l_Lean_MessageData_ofExpr(x_5);
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
x_11 = l_Lean_MessageData_ofExpr(x_9);
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
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
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg(x_1, x_2, x_4, x_5, x_6, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_Decl_reduceArity(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = lean_ctor_get(x_1, 4);
lean_inc(x_7);
if (lean_obj_tag(x_7) == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_7, 0);
lean_inc(x_8);
lean_inc(x_5);
lean_inc(x_4);
lean_inc(x_3);
lean_inc(x_2);
lean_inc(x_1);
x_9 = l_Lean_Compiler_LCNF_FindUsed_collectUsedParams(x_1, x_2, x_3, x_4, x_5, x_6);
if (lean_obj_tag(x_9) == 0)
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; uint8_t x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; size_t x_27; lean_object* x_28; size_t x_29; lean_object* x_30; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; uint8_t x_343; lean_object* x_344; size_t x_345; lean_object* x_346; lean_object* x_347; size_t x_348; lean_object* x_349; lean_object* x_350; uint8_t x_359; lean_object* x_360; lean_object* x_361; lean_object* x_362; lean_object* x_363; lean_object* x_364; uint8_t x_379; uint8_t x_431; 
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
x_13 = l_Lean_RBMap_size___redArg(x_10);
x_14 = lean_ctor_get(x_1, 3);
lean_inc(x_14);
x_337 = lean_array_get_size(x_14);
x_431 = lean_nat_dec_eq(x_13, x_337);
if (x_431 == 0)
{
lean_object* x_432; uint8_t x_433; 
x_432 = lean_unsigned_to_nat(0u);
x_433 = lean_nat_dec_eq(x_13, x_432);
lean_dec(x_13);
x_379 = x_433;
goto block_430;
}
else
{
lean_dec(x_13);
x_379 = x_431;
goto block_430;
}
block_336:
{
lean_object* x_31; uint8_t x_32; 
lean_inc(x_19);
lean_inc(x_15);
lean_inc(x_23);
lean_inc(x_28);
lean_inc(x_7);
x_31 = l_Lean_Compiler_LCNF_DeclValue_mapCodeM___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__1(x_25, x_7, x_22, x_28, x_23, x_15, x_19, x_26);
x_32 = !lean_is_exclusive(x_7);
if (x_32 == 0)
{
lean_object* x_33; 
x_33 = lean_ctor_get(x_7, 0);
lean_dec(x_33);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; 
x_34 = lean_ctor_get(x_31, 0);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 1);
lean_inc(x_35);
lean_dec(x_31);
x_36 = l_Lean_Compiler_LCNF_Code_inferType(x_8, x_28, x_23, x_15, x_19, x_35);
if (lean_obj_tag(x_36) == 0)
{
lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
x_38 = lean_ctor_get(x_36, 1);
lean_inc(x_38);
lean_dec(x_36);
lean_inc(x_20);
x_39 = l_Lean_Compiler_LCNF_mkForallParams(x_20, x_37, x_28, x_23, x_15, x_19, x_38);
lean_dec(x_37);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; uint8_t x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 1);
lean_inc(x_41);
lean_dec(x_39);
x_42 = lean_box(0);
x_43 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_44 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_45 = lean_ctor_get(x_1, 5);
lean_inc(x_45);
lean_inc(x_16);
x_46 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_46, 0, x_16);
lean_ctor_set(x_46, 1, x_42);
lean_ctor_set(x_46, 2, x_40);
lean_ctor_set(x_46, 3, x_20);
lean_ctor_set(x_46, 4, x_34);
lean_ctor_set(x_46, 5, x_45);
lean_ctor_set_uint8(x_46, sizeof(void*)*6, x_43);
lean_ctor_set_uint8(x_46, sizeof(void*)*6 + 1, x_44);
lean_inc(x_46);
x_47 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_46, x_19, x_41);
x_48 = !lean_is_exclusive(x_47);
if (x_48 == 0)
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; uint8_t x_63; 
x_49 = lean_ctor_get(x_47, 1);
x_50 = lean_ctor_get(x_47, 0);
lean_dec(x_50);
x_51 = lean_unsigned_to_nat(8u);
x_52 = lean_unsigned_to_nat(2u);
x_53 = lean_nat_shiftl(x_51, x_52);
x_54 = lean_unsigned_to_nat(3u);
x_55 = lean_nat_div(x_53, x_54);
lean_dec(x_53);
x_56 = l_Nat_nextPowerOfTwo(x_55);
lean_dec(x_55);
x_57 = lean_box(0);
x_58 = lean_mk_array(x_56, x_57);
lean_inc(x_17);
lean_ctor_set(x_47, 1, x_58);
lean_ctor_set(x_47, 0, x_17);
x_59 = lean_st_mk_ref(x_47, x_49);
x_60 = lean_ctor_get(x_59, 0);
lean_inc(x_60);
x_61 = lean_ctor_get(x_59, 1);
lean_inc(x_61);
lean_dec(x_59);
x_62 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_27, x_29, x_14, x_60, x_28, x_23, x_15, x_19, x_61);
x_63 = !lean_is_exclusive(x_62);
if (x_63 == 0)
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; size_t x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_64 = lean_ctor_get(x_62, 0);
x_65 = lean_ctor_get(x_62, 1);
x_66 = lean_mk_empty_array_with_capacity(x_17);
x_67 = lean_array_get_size(x_64);
lean_inc(x_64);
x_68 = l_Array_toSubarray___redArg(x_64, x_17, x_67);
lean_ctor_set(x_62, 1, x_66);
lean_ctor_set(x_62, 0, x_68);
x_69 = lean_array_size(x_18);
x_70 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_18, x_69, x_29, x_62, x_65);
lean_dec(x_18);
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc(x_72);
lean_dec(x_70);
x_73 = !lean_is_exclusive(x_71);
if (x_73 == 0)
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; 
x_74 = lean_ctor_get(x_71, 1);
x_75 = lean_ctor_get(x_71, 0);
lean_dec(x_75);
x_76 = lean_box(0);
x_77 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_77, 0, x_16);
lean_ctor_set(x_77, 1, x_76);
lean_ctor_set(x_77, 2, x_74);
x_78 = lean_mk_string_unchecked("_x", 2, 2);
x_79 = l_Lean_Name_mkStr1(x_78);
lean_inc(x_19);
lean_inc(x_23);
x_80 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_77, x_79, x_28, x_23, x_15, x_19, x_72);
if (lean_obj_tag(x_80) == 0)
{
lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; uint8_t x_95; 
x_81 = lean_ctor_get(x_80, 0);
lean_inc(x_81);
x_82 = lean_ctor_get(x_80, 1);
lean_inc(x_82);
lean_dec(x_80);
x_83 = lean_ctor_get(x_81, 0);
lean_inc(x_83);
x_84 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_84, 0, x_83);
lean_ctor_set(x_71, 1, x_84);
lean_ctor_set(x_71, 0, x_81);
lean_ctor_set(x_7, 0, x_71);
x_85 = lean_ctor_get(x_1, 1);
lean_inc(x_85);
x_86 = lean_ctor_get(x_1, 2);
lean_inc(x_86);
lean_dec(x_1);
x_87 = lean_box(0);
x_88 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_88, 0, x_87);
x_89 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_89, 0, x_24);
lean_ctor_set(x_89, 1, x_85);
lean_ctor_set(x_89, 2, x_86);
lean_ctor_set(x_89, 3, x_64);
lean_ctor_set(x_89, 4, x_7);
lean_ctor_set(x_89, 5, x_88);
lean_ctor_set_uint8(x_89, sizeof(void*)*6, x_21);
lean_ctor_set_uint8(x_89, sizeof(void*)*6 + 1, x_44);
lean_inc(x_89);
x_90 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_89, x_19, x_82);
lean_dec(x_19);
x_91 = lean_ctor_get(x_90, 1);
lean_inc(x_91);
lean_dec(x_90);
x_92 = lean_st_ref_get(x_60, x_91);
lean_dec(x_60);
x_93 = lean_ctor_get(x_92, 1);
lean_inc(x_93);
lean_dec(x_92);
x_94 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_23, x_93);
lean_dec(x_23);
lean_dec(x_30);
x_95 = !lean_is_exclusive(x_94);
if (x_95 == 0)
{
lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; 
x_96 = lean_ctor_get(x_94, 0);
lean_dec(x_96);
x_97 = lean_mk_empty_array_with_capacity(x_52);
x_98 = lean_array_push(x_97, x_46);
x_99 = lean_array_push(x_98, x_89);
lean_ctor_set(x_94, 0, x_99);
return x_94;
}
else
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_100 = lean_ctor_get(x_94, 1);
lean_inc(x_100);
lean_dec(x_94);
x_101 = lean_mk_empty_array_with_capacity(x_52);
x_102 = lean_array_push(x_101, x_46);
x_103 = lean_array_push(x_102, x_89);
x_104 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_104, 0, x_103);
lean_ctor_set(x_104, 1, x_100);
return x_104;
}
}
else
{
uint8_t x_105; 
lean_free_object(x_71);
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_46);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_1);
x_105 = !lean_is_exclusive(x_80);
if (x_105 == 0)
{
return x_80;
}
else
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = lean_ctor_get(x_80, 0);
x_107 = lean_ctor_get(x_80, 1);
lean_inc(x_107);
lean_inc(x_106);
lean_dec(x_80);
x_108 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_108, 0, x_106);
lean_ctor_set(x_108, 1, x_107);
return x_108;
}
}
}
else
{
lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; 
x_109 = lean_ctor_get(x_71, 1);
lean_inc(x_109);
lean_dec(x_71);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_111, 0, x_16);
lean_ctor_set(x_111, 1, x_110);
lean_ctor_set(x_111, 2, x_109);
x_112 = lean_mk_string_unchecked("_x", 2, 2);
x_113 = l_Lean_Name_mkStr1(x_112);
lean_inc(x_19);
lean_inc(x_23);
x_114 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_111, x_113, x_28, x_23, x_15, x_19, x_72);
if (lean_obj_tag(x_114) == 0)
{
lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_121; lean_object* x_122; lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; 
x_115 = lean_ctor_get(x_114, 0);
lean_inc(x_115);
x_116 = lean_ctor_get(x_114, 1);
lean_inc(x_116);
lean_dec(x_114);
x_117 = lean_ctor_get(x_115, 0);
lean_inc(x_117);
x_118 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_118, 0, x_117);
x_119 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_119, 0, x_115);
lean_ctor_set(x_119, 1, x_118);
lean_ctor_set(x_7, 0, x_119);
x_120 = lean_ctor_get(x_1, 1);
lean_inc(x_120);
x_121 = lean_ctor_get(x_1, 2);
lean_inc(x_121);
lean_dec(x_1);
x_122 = lean_box(0);
x_123 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_123, 0, x_122);
x_124 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_124, 0, x_24);
lean_ctor_set(x_124, 1, x_120);
lean_ctor_set(x_124, 2, x_121);
lean_ctor_set(x_124, 3, x_64);
lean_ctor_set(x_124, 4, x_7);
lean_ctor_set(x_124, 5, x_123);
lean_ctor_set_uint8(x_124, sizeof(void*)*6, x_21);
lean_ctor_set_uint8(x_124, sizeof(void*)*6 + 1, x_44);
lean_inc(x_124);
x_125 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_124, x_19, x_116);
lean_dec(x_19);
x_126 = lean_ctor_get(x_125, 1);
lean_inc(x_126);
lean_dec(x_125);
x_127 = lean_st_ref_get(x_60, x_126);
lean_dec(x_60);
x_128 = lean_ctor_get(x_127, 1);
lean_inc(x_128);
lean_dec(x_127);
x_129 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_23, x_128);
lean_dec(x_23);
lean_dec(x_30);
x_130 = lean_ctor_get(x_129, 1);
lean_inc(x_130);
if (lean_is_exclusive(x_129)) {
 lean_ctor_release(x_129, 0);
 lean_ctor_release(x_129, 1);
 x_131 = x_129;
} else {
 lean_dec_ref(x_129);
 x_131 = lean_box(0);
}
x_132 = lean_mk_empty_array_with_capacity(x_52);
x_133 = lean_array_push(x_132, x_46);
x_134 = lean_array_push(x_133, x_124);
if (lean_is_scalar(x_131)) {
 x_135 = lean_alloc_ctor(0, 2, 0);
} else {
 x_135 = x_131;
}
lean_ctor_set(x_135, 0, x_134);
lean_ctor_set(x_135, 1, x_130);
return x_135;
}
else
{
lean_object* x_136; lean_object* x_137; lean_object* x_138; lean_object* x_139; 
lean_dec(x_64);
lean_dec(x_60);
lean_dec(x_46);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_1);
x_136 = lean_ctor_get(x_114, 0);
lean_inc(x_136);
x_137 = lean_ctor_get(x_114, 1);
lean_inc(x_137);
if (lean_is_exclusive(x_114)) {
 lean_ctor_release(x_114, 0);
 lean_ctor_release(x_114, 1);
 x_138 = x_114;
} else {
 lean_dec_ref(x_114);
 x_138 = lean_box(0);
}
if (lean_is_scalar(x_138)) {
 x_139 = lean_alloc_ctor(1, 2, 0);
} else {
 x_139 = x_138;
}
lean_ctor_set(x_139, 0, x_136);
lean_ctor_set(x_139, 1, x_137);
return x_139;
}
}
}
else
{
lean_object* x_140; lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; size_t x_146; lean_object* x_147; lean_object* x_148; lean_object* x_149; lean_object* x_150; lean_object* x_151; lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; 
x_140 = lean_ctor_get(x_62, 0);
x_141 = lean_ctor_get(x_62, 1);
lean_inc(x_141);
lean_inc(x_140);
lean_dec(x_62);
x_142 = lean_mk_empty_array_with_capacity(x_17);
x_143 = lean_array_get_size(x_140);
lean_inc(x_140);
x_144 = l_Array_toSubarray___redArg(x_140, x_17, x_143);
x_145 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_145, 0, x_144);
lean_ctor_set(x_145, 1, x_142);
x_146 = lean_array_size(x_18);
x_147 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_18, x_146, x_29, x_145, x_141);
lean_dec(x_18);
x_148 = lean_ctor_get(x_147, 0);
lean_inc(x_148);
x_149 = lean_ctor_get(x_147, 1);
lean_inc(x_149);
lean_dec(x_147);
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
x_152 = lean_box(0);
x_153 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_153, 0, x_16);
lean_ctor_set(x_153, 1, x_152);
lean_ctor_set(x_153, 2, x_150);
x_154 = lean_mk_string_unchecked("_x", 2, 2);
x_155 = l_Lean_Name_mkStr1(x_154);
lean_inc(x_19);
lean_inc(x_23);
x_156 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_153, x_155, x_28, x_23, x_15, x_19, x_149);
if (lean_obj_tag(x_156) == 0)
{
lean_object* x_157; lean_object* x_158; lean_object* x_159; lean_object* x_160; lean_object* x_161; lean_object* x_162; lean_object* x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; lean_object* x_171; lean_object* x_172; lean_object* x_173; lean_object* x_174; lean_object* x_175; lean_object* x_176; lean_object* x_177; 
x_157 = lean_ctor_get(x_156, 0);
lean_inc(x_157);
x_158 = lean_ctor_get(x_156, 1);
lean_inc(x_158);
lean_dec(x_156);
x_159 = lean_ctor_get(x_157, 0);
lean_inc(x_159);
x_160 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_160, 0, x_159);
if (lean_is_scalar(x_151)) {
 x_161 = lean_alloc_ctor(0, 2, 0);
} else {
 x_161 = x_151;
}
lean_ctor_set(x_161, 0, x_157);
lean_ctor_set(x_161, 1, x_160);
lean_ctor_set(x_7, 0, x_161);
x_162 = lean_ctor_get(x_1, 1);
lean_inc(x_162);
x_163 = lean_ctor_get(x_1, 2);
lean_inc(x_163);
lean_dec(x_1);
x_164 = lean_box(0);
x_165 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_165, 0, x_164);
x_166 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_166, 0, x_24);
lean_ctor_set(x_166, 1, x_162);
lean_ctor_set(x_166, 2, x_163);
lean_ctor_set(x_166, 3, x_140);
lean_ctor_set(x_166, 4, x_7);
lean_ctor_set(x_166, 5, x_165);
lean_ctor_set_uint8(x_166, sizeof(void*)*6, x_21);
lean_ctor_set_uint8(x_166, sizeof(void*)*6 + 1, x_44);
lean_inc(x_166);
x_167 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_166, x_19, x_158);
lean_dec(x_19);
x_168 = lean_ctor_get(x_167, 1);
lean_inc(x_168);
lean_dec(x_167);
x_169 = lean_st_ref_get(x_60, x_168);
lean_dec(x_60);
x_170 = lean_ctor_get(x_169, 1);
lean_inc(x_170);
lean_dec(x_169);
x_171 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_23, x_170);
lean_dec(x_23);
lean_dec(x_30);
x_172 = lean_ctor_get(x_171, 1);
lean_inc(x_172);
if (lean_is_exclusive(x_171)) {
 lean_ctor_release(x_171, 0);
 lean_ctor_release(x_171, 1);
 x_173 = x_171;
} else {
 lean_dec_ref(x_171);
 x_173 = lean_box(0);
}
x_174 = lean_mk_empty_array_with_capacity(x_52);
x_175 = lean_array_push(x_174, x_46);
x_176 = lean_array_push(x_175, x_166);
if (lean_is_scalar(x_173)) {
 x_177 = lean_alloc_ctor(0, 2, 0);
} else {
 x_177 = x_173;
}
lean_ctor_set(x_177, 0, x_176);
lean_ctor_set(x_177, 1, x_172);
return x_177;
}
else
{
lean_object* x_178; lean_object* x_179; lean_object* x_180; lean_object* x_181; 
lean_dec(x_151);
lean_dec(x_140);
lean_dec(x_60);
lean_dec(x_46);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_1);
x_178 = lean_ctor_get(x_156, 0);
lean_inc(x_178);
x_179 = lean_ctor_get(x_156, 1);
lean_inc(x_179);
if (lean_is_exclusive(x_156)) {
 lean_ctor_release(x_156, 0);
 lean_ctor_release(x_156, 1);
 x_180 = x_156;
} else {
 lean_dec_ref(x_156);
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
lean_object* x_182; lean_object* x_183; lean_object* x_184; lean_object* x_185; lean_object* x_186; lean_object* x_187; lean_object* x_188; lean_object* x_189; lean_object* x_190; lean_object* x_191; lean_object* x_192; lean_object* x_193; lean_object* x_194; lean_object* x_195; lean_object* x_196; lean_object* x_197; lean_object* x_198; lean_object* x_199; lean_object* x_200; lean_object* x_201; lean_object* x_202; size_t x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; lean_object* x_210; lean_object* x_211; lean_object* x_212; lean_object* x_213; 
x_182 = lean_ctor_get(x_47, 1);
lean_inc(x_182);
lean_dec(x_47);
x_183 = lean_unsigned_to_nat(8u);
x_184 = lean_unsigned_to_nat(2u);
x_185 = lean_nat_shiftl(x_183, x_184);
x_186 = lean_unsigned_to_nat(3u);
x_187 = lean_nat_div(x_185, x_186);
lean_dec(x_185);
x_188 = l_Nat_nextPowerOfTwo(x_187);
lean_dec(x_187);
x_189 = lean_box(0);
x_190 = lean_mk_array(x_188, x_189);
lean_inc(x_17);
x_191 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_191, 0, x_17);
lean_ctor_set(x_191, 1, x_190);
x_192 = lean_st_mk_ref(x_191, x_182);
x_193 = lean_ctor_get(x_192, 0);
lean_inc(x_193);
x_194 = lean_ctor_get(x_192, 1);
lean_inc(x_194);
lean_dec(x_192);
x_195 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_27, x_29, x_14, x_193, x_28, x_23, x_15, x_19, x_194);
x_196 = lean_ctor_get(x_195, 0);
lean_inc(x_196);
x_197 = lean_ctor_get(x_195, 1);
lean_inc(x_197);
if (lean_is_exclusive(x_195)) {
 lean_ctor_release(x_195, 0);
 lean_ctor_release(x_195, 1);
 x_198 = x_195;
} else {
 lean_dec_ref(x_195);
 x_198 = lean_box(0);
}
x_199 = lean_mk_empty_array_with_capacity(x_17);
x_200 = lean_array_get_size(x_196);
lean_inc(x_196);
x_201 = l_Array_toSubarray___redArg(x_196, x_17, x_200);
if (lean_is_scalar(x_198)) {
 x_202 = lean_alloc_ctor(0, 2, 0);
} else {
 x_202 = x_198;
}
lean_ctor_set(x_202, 0, x_201);
lean_ctor_set(x_202, 1, x_199);
x_203 = lean_array_size(x_18);
x_204 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_18, x_203, x_29, x_202, x_197);
lean_dec(x_18);
x_205 = lean_ctor_get(x_204, 0);
lean_inc(x_205);
x_206 = lean_ctor_get(x_204, 1);
lean_inc(x_206);
lean_dec(x_204);
x_207 = lean_ctor_get(x_205, 1);
lean_inc(x_207);
if (lean_is_exclusive(x_205)) {
 lean_ctor_release(x_205, 0);
 lean_ctor_release(x_205, 1);
 x_208 = x_205;
} else {
 lean_dec_ref(x_205);
 x_208 = lean_box(0);
}
x_209 = lean_box(0);
x_210 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_210, 0, x_16);
lean_ctor_set(x_210, 1, x_209);
lean_ctor_set(x_210, 2, x_207);
x_211 = lean_mk_string_unchecked("_x", 2, 2);
x_212 = l_Lean_Name_mkStr1(x_211);
lean_inc(x_19);
lean_inc(x_23);
x_213 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_210, x_212, x_28, x_23, x_15, x_19, x_206);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_214; lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; lean_object* x_228; lean_object* x_229; lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; 
x_214 = lean_ctor_get(x_213, 0);
lean_inc(x_214);
x_215 = lean_ctor_get(x_213, 1);
lean_inc(x_215);
lean_dec(x_213);
x_216 = lean_ctor_get(x_214, 0);
lean_inc(x_216);
x_217 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_217, 0, x_216);
if (lean_is_scalar(x_208)) {
 x_218 = lean_alloc_ctor(0, 2, 0);
} else {
 x_218 = x_208;
}
lean_ctor_set(x_218, 0, x_214);
lean_ctor_set(x_218, 1, x_217);
lean_ctor_set(x_7, 0, x_218);
x_219 = lean_ctor_get(x_1, 1);
lean_inc(x_219);
x_220 = lean_ctor_get(x_1, 2);
lean_inc(x_220);
lean_dec(x_1);
x_221 = lean_box(0);
x_222 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_222, 0, x_221);
x_223 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_223, 0, x_24);
lean_ctor_set(x_223, 1, x_219);
lean_ctor_set(x_223, 2, x_220);
lean_ctor_set(x_223, 3, x_196);
lean_ctor_set(x_223, 4, x_7);
lean_ctor_set(x_223, 5, x_222);
lean_ctor_set_uint8(x_223, sizeof(void*)*6, x_21);
lean_ctor_set_uint8(x_223, sizeof(void*)*6 + 1, x_44);
lean_inc(x_223);
x_224 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_223, x_19, x_215);
lean_dec(x_19);
x_225 = lean_ctor_get(x_224, 1);
lean_inc(x_225);
lean_dec(x_224);
x_226 = lean_st_ref_get(x_193, x_225);
lean_dec(x_193);
x_227 = lean_ctor_get(x_226, 1);
lean_inc(x_227);
lean_dec(x_226);
x_228 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_23, x_227);
lean_dec(x_23);
lean_dec(x_30);
x_229 = lean_ctor_get(x_228, 1);
lean_inc(x_229);
if (lean_is_exclusive(x_228)) {
 lean_ctor_release(x_228, 0);
 lean_ctor_release(x_228, 1);
 x_230 = x_228;
} else {
 lean_dec_ref(x_228);
 x_230 = lean_box(0);
}
x_231 = lean_mk_empty_array_with_capacity(x_184);
x_232 = lean_array_push(x_231, x_46);
x_233 = lean_array_push(x_232, x_223);
if (lean_is_scalar(x_230)) {
 x_234 = lean_alloc_ctor(0, 2, 0);
} else {
 x_234 = x_230;
}
lean_ctor_set(x_234, 0, x_233);
lean_ctor_set(x_234, 1, x_229);
return x_234;
}
else
{
lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; 
lean_dec(x_208);
lean_dec(x_196);
lean_dec(x_193);
lean_dec(x_46);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_1);
x_235 = lean_ctor_get(x_213, 0);
lean_inc(x_235);
x_236 = lean_ctor_get(x_213, 1);
lean_inc(x_236);
if (lean_is_exclusive(x_213)) {
 lean_ctor_release(x_213, 0);
 lean_ctor_release(x_213, 1);
 x_237 = x_213;
} else {
 lean_dec_ref(x_213);
 x_237 = lean_box(0);
}
if (lean_is_scalar(x_237)) {
 x_238 = lean_alloc_ctor(1, 2, 0);
} else {
 x_238 = x_237;
}
lean_ctor_set(x_238, 0, x_235);
lean_ctor_set(x_238, 1, x_236);
return x_238;
}
}
}
else
{
uint8_t x_239; 
lean_dec(x_34);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_239 = !lean_is_exclusive(x_39);
if (x_239 == 0)
{
return x_39;
}
else
{
lean_object* x_240; lean_object* x_241; lean_object* x_242; 
x_240 = lean_ctor_get(x_39, 0);
x_241 = lean_ctor_get(x_39, 1);
lean_inc(x_241);
lean_inc(x_240);
lean_dec(x_39);
x_242 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
return x_242;
}
}
}
else
{
uint8_t x_243; 
lean_dec(x_34);
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_243 = !lean_is_exclusive(x_36);
if (x_243 == 0)
{
return x_36;
}
else
{
lean_object* x_244; lean_object* x_245; lean_object* x_246; 
x_244 = lean_ctor_get(x_36, 0);
x_245 = lean_ctor_get(x_36, 1);
lean_inc(x_245);
lean_inc(x_244);
lean_dec(x_36);
x_246 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_246, 0, x_244);
lean_ctor_set(x_246, 1, x_245);
return x_246;
}
}
}
else
{
uint8_t x_247; 
lean_free_object(x_7);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_1);
x_247 = !lean_is_exclusive(x_31);
if (x_247 == 0)
{
return x_31;
}
else
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; 
x_248 = lean_ctor_get(x_31, 0);
x_249 = lean_ctor_get(x_31, 1);
lean_inc(x_249);
lean_inc(x_248);
lean_dec(x_31);
x_250 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
return x_250;
}
}
}
else
{
lean_dec(x_7);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_251; lean_object* x_252; lean_object* x_253; 
x_251 = lean_ctor_get(x_31, 0);
lean_inc(x_251);
x_252 = lean_ctor_get(x_31, 1);
lean_inc(x_252);
lean_dec(x_31);
x_253 = l_Lean_Compiler_LCNF_Code_inferType(x_8, x_28, x_23, x_15, x_19, x_252);
if (lean_obj_tag(x_253) == 0)
{
lean_object* x_254; lean_object* x_255; lean_object* x_256; 
x_254 = lean_ctor_get(x_253, 0);
lean_inc(x_254);
x_255 = lean_ctor_get(x_253, 1);
lean_inc(x_255);
lean_dec(x_253);
lean_inc(x_20);
x_256 = l_Lean_Compiler_LCNF_mkForallParams(x_20, x_254, x_28, x_23, x_15, x_19, x_255);
lean_dec(x_254);
if (lean_obj_tag(x_256) == 0)
{
lean_object* x_257; lean_object* x_258; lean_object* x_259; uint8_t x_260; uint8_t x_261; lean_object* x_262; lean_object* x_263; lean_object* x_264; lean_object* x_265; lean_object* x_266; lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_271; lean_object* x_272; lean_object* x_273; lean_object* x_274; lean_object* x_275; lean_object* x_276; lean_object* x_277; lean_object* x_278; lean_object* x_279; lean_object* x_280; lean_object* x_281; lean_object* x_282; lean_object* x_283; lean_object* x_284; lean_object* x_285; lean_object* x_286; size_t x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_291; lean_object* x_292; lean_object* x_293; lean_object* x_294; lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_257 = lean_ctor_get(x_256, 0);
lean_inc(x_257);
x_258 = lean_ctor_get(x_256, 1);
lean_inc(x_258);
lean_dec(x_256);
x_259 = lean_box(0);
x_260 = lean_ctor_get_uint8(x_1, sizeof(void*)*6);
x_261 = lean_ctor_get_uint8(x_1, sizeof(void*)*6 + 1);
x_262 = lean_ctor_get(x_1, 5);
lean_inc(x_262);
lean_inc(x_16);
x_263 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_263, 0, x_16);
lean_ctor_set(x_263, 1, x_259);
lean_ctor_set(x_263, 2, x_257);
lean_ctor_set(x_263, 3, x_20);
lean_ctor_set(x_263, 4, x_251);
lean_ctor_set(x_263, 5, x_262);
lean_ctor_set_uint8(x_263, sizeof(void*)*6, x_260);
lean_ctor_set_uint8(x_263, sizeof(void*)*6 + 1, x_261);
lean_inc(x_263);
x_264 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_263, x_19, x_258);
x_265 = lean_ctor_get(x_264, 1);
lean_inc(x_265);
if (lean_is_exclusive(x_264)) {
 lean_ctor_release(x_264, 0);
 lean_ctor_release(x_264, 1);
 x_266 = x_264;
} else {
 lean_dec_ref(x_264);
 x_266 = lean_box(0);
}
x_267 = lean_unsigned_to_nat(8u);
x_268 = lean_unsigned_to_nat(2u);
x_269 = lean_nat_shiftl(x_267, x_268);
x_270 = lean_unsigned_to_nat(3u);
x_271 = lean_nat_div(x_269, x_270);
lean_dec(x_269);
x_272 = l_Nat_nextPowerOfTwo(x_271);
lean_dec(x_271);
x_273 = lean_box(0);
x_274 = lean_mk_array(x_272, x_273);
lean_inc(x_17);
if (lean_is_scalar(x_266)) {
 x_275 = lean_alloc_ctor(0, 2, 0);
} else {
 x_275 = x_266;
}
lean_ctor_set(x_275, 0, x_17);
lean_ctor_set(x_275, 1, x_274);
x_276 = lean_st_mk_ref(x_275, x_265);
x_277 = lean_ctor_get(x_276, 0);
lean_inc(x_277);
x_278 = lean_ctor_get(x_276, 1);
lean_inc(x_278);
lean_dec(x_276);
x_279 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Internalize_internalizeFunDecl_spec__0(x_27, x_29, x_14, x_277, x_28, x_23, x_15, x_19, x_278);
x_280 = lean_ctor_get(x_279, 0);
lean_inc(x_280);
x_281 = lean_ctor_get(x_279, 1);
lean_inc(x_281);
if (lean_is_exclusive(x_279)) {
 lean_ctor_release(x_279, 0);
 lean_ctor_release(x_279, 1);
 x_282 = x_279;
} else {
 lean_dec_ref(x_279);
 x_282 = lean_box(0);
}
x_283 = lean_mk_empty_array_with_capacity(x_17);
x_284 = lean_array_get_size(x_280);
lean_inc(x_280);
x_285 = l_Array_toSubarray___redArg(x_280, x_17, x_284);
if (lean_is_scalar(x_282)) {
 x_286 = lean_alloc_ctor(0, 2, 0);
} else {
 x_286 = x_282;
}
lean_ctor_set(x_286, 0, x_285);
lean_ctor_set(x_286, 1, x_283);
x_287 = lean_array_size(x_18);
x_288 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_18, x_287, x_29, x_286, x_281);
lean_dec(x_18);
x_289 = lean_ctor_get(x_288, 0);
lean_inc(x_289);
x_290 = lean_ctor_get(x_288, 1);
lean_inc(x_290);
lean_dec(x_288);
x_291 = lean_ctor_get(x_289, 1);
lean_inc(x_291);
if (lean_is_exclusive(x_289)) {
 lean_ctor_release(x_289, 0);
 lean_ctor_release(x_289, 1);
 x_292 = x_289;
} else {
 lean_dec_ref(x_289);
 x_292 = lean_box(0);
}
x_293 = lean_box(0);
x_294 = lean_alloc_ctor(3, 3, 0);
lean_ctor_set(x_294, 0, x_16);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set(x_294, 2, x_291);
x_295 = lean_mk_string_unchecked("_x", 2, 2);
x_296 = l_Lean_Name_mkStr1(x_295);
lean_inc(x_19);
lean_inc(x_23);
x_297 = l_Lean_Compiler_LCNF_mkAuxLetDecl(x_294, x_296, x_28, x_23, x_15, x_19, x_290);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; lean_object* x_299; lean_object* x_300; lean_object* x_301; lean_object* x_302; lean_object* x_303; lean_object* x_304; lean_object* x_305; lean_object* x_306; lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_316; lean_object* x_317; lean_object* x_318; lean_object* x_319; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
x_299 = lean_ctor_get(x_297, 1);
lean_inc(x_299);
lean_dec(x_297);
x_300 = lean_ctor_get(x_298, 0);
lean_inc(x_300);
x_301 = lean_alloc_ctor(5, 1, 0);
lean_ctor_set(x_301, 0, x_300);
if (lean_is_scalar(x_292)) {
 x_302 = lean_alloc_ctor(0, 2, 0);
} else {
 x_302 = x_292;
}
lean_ctor_set(x_302, 0, x_298);
lean_ctor_set(x_302, 1, x_301);
x_303 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_303, 0, x_302);
x_304 = lean_ctor_get(x_1, 1);
lean_inc(x_304);
x_305 = lean_ctor_get(x_1, 2);
lean_inc(x_305);
lean_dec(x_1);
x_306 = lean_box(0);
x_307 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_307, 0, x_306);
x_308 = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(x_308, 0, x_24);
lean_ctor_set(x_308, 1, x_304);
lean_ctor_set(x_308, 2, x_305);
lean_ctor_set(x_308, 3, x_280);
lean_ctor_set(x_308, 4, x_303);
lean_ctor_set(x_308, 5, x_307);
lean_ctor_set_uint8(x_308, sizeof(void*)*6, x_21);
lean_ctor_set_uint8(x_308, sizeof(void*)*6 + 1, x_261);
lean_inc(x_308);
x_309 = l_Lean_Compiler_LCNF_Decl_saveMono___redArg(x_308, x_19, x_299);
lean_dec(x_19);
x_310 = lean_ctor_get(x_309, 1);
lean_inc(x_310);
lean_dec(x_309);
x_311 = lean_st_ref_get(x_277, x_310);
lean_dec(x_277);
x_312 = lean_ctor_get(x_311, 1);
lean_inc(x_312);
lean_dec(x_311);
x_313 = l_Lean_Compiler_LCNF_eraseParams___redArg(x_30, x_23, x_312);
lean_dec(x_23);
lean_dec(x_30);
x_314 = lean_ctor_get(x_313, 1);
lean_inc(x_314);
if (lean_is_exclusive(x_313)) {
 lean_ctor_release(x_313, 0);
 lean_ctor_release(x_313, 1);
 x_315 = x_313;
} else {
 lean_dec_ref(x_313);
 x_315 = lean_box(0);
}
x_316 = lean_mk_empty_array_with_capacity(x_268);
x_317 = lean_array_push(x_316, x_263);
x_318 = lean_array_push(x_317, x_308);
if (lean_is_scalar(x_315)) {
 x_319 = lean_alloc_ctor(0, 2, 0);
} else {
 x_319 = x_315;
}
lean_ctor_set(x_319, 0, x_318);
lean_ctor_set(x_319, 1, x_314);
return x_319;
}
else
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; 
lean_dec(x_292);
lean_dec(x_280);
lean_dec(x_277);
lean_dec(x_263);
lean_dec(x_30);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_19);
lean_dec(x_1);
x_320 = lean_ctor_get(x_297, 0);
lean_inc(x_320);
x_321 = lean_ctor_get(x_297, 1);
lean_inc(x_321);
if (lean_is_exclusive(x_297)) {
 lean_ctor_release(x_297, 0);
 lean_ctor_release(x_297, 1);
 x_322 = x_297;
} else {
 lean_dec_ref(x_297);
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
else
{
lean_object* x_324; lean_object* x_325; lean_object* x_326; lean_object* x_327; 
lean_dec(x_251);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_324 = lean_ctor_get(x_256, 0);
lean_inc(x_324);
x_325 = lean_ctor_get(x_256, 1);
lean_inc(x_325);
if (lean_is_exclusive(x_256)) {
 lean_ctor_release(x_256, 0);
 lean_ctor_release(x_256, 1);
 x_326 = x_256;
} else {
 lean_dec_ref(x_256);
 x_326 = lean_box(0);
}
if (lean_is_scalar(x_326)) {
 x_327 = lean_alloc_ctor(1, 2, 0);
} else {
 x_327 = x_326;
}
lean_ctor_set(x_327, 0, x_324);
lean_ctor_set(x_327, 1, x_325);
return x_327;
}
}
else
{
lean_object* x_328; lean_object* x_329; lean_object* x_330; lean_object* x_331; 
lean_dec(x_251);
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_1);
x_328 = lean_ctor_get(x_253, 0);
lean_inc(x_328);
x_329 = lean_ctor_get(x_253, 1);
lean_inc(x_329);
if (lean_is_exclusive(x_253)) {
 lean_ctor_release(x_253, 0);
 lean_ctor_release(x_253, 1);
 x_330 = x_253;
} else {
 lean_dec_ref(x_253);
 x_330 = lean_box(0);
}
if (lean_is_scalar(x_330)) {
 x_331 = lean_alloc_ctor(1, 2, 0);
} else {
 x_331 = x_330;
}
lean_ctor_set(x_331, 0, x_328);
lean_ctor_set(x_331, 1, x_329);
return x_331;
}
}
else
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; 
lean_dec(x_30);
lean_dec(x_28);
lean_dec(x_24);
lean_dec(x_23);
lean_dec(x_20);
lean_dec(x_19);
lean_dec(x_18);
lean_dec(x_17);
lean_dec(x_16);
lean_dec(x_15);
lean_dec(x_14);
lean_dec(x_8);
lean_dec(x_1);
x_332 = lean_ctor_get(x_31, 0);
lean_inc(x_332);
x_333 = lean_ctor_get(x_31, 1);
lean_inc(x_333);
if (lean_is_exclusive(x_31)) {
 lean_ctor_release(x_31, 0);
 lean_ctor_release(x_31, 1);
 x_334 = x_31;
} else {
 lean_dec_ref(x_31);
 x_334 = lean_box(0);
}
if (lean_is_scalar(x_334)) {
 x_335 = lean_alloc_ctor(1, 2, 0);
} else {
 x_335 = x_334;
}
lean_ctor_set(x_335, 0, x_332);
lean_ctor_set(x_335, 1, x_333);
return x_335;
}
}
}
block_358:
{
lean_object* x_351; lean_object* x_352; lean_object* x_353; uint8_t x_354; 
x_351 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_ReduceArity_reduce___boxed), 7, 0);
lean_inc(x_341);
lean_inc(x_339);
lean_inc(x_349);
x_352 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_352, 0, x_349);
lean_ctor_set(x_352, 1, x_339);
lean_ctor_set(x_352, 2, x_341);
x_353 = lean_mk_empty_array_with_capacity(x_340);
x_354 = lean_nat_dec_lt(x_340, x_337);
if (x_354 == 0)
{
lean_dec(x_337);
lean_dec(x_10);
x_15 = x_338;
x_16 = x_339;
x_17 = x_340;
x_18 = x_341;
x_19 = x_342;
x_20 = x_350;
x_21 = x_343;
x_22 = x_352;
x_23 = x_347;
x_24 = x_349;
x_25 = x_351;
x_26 = x_344;
x_27 = x_345;
x_28 = x_346;
x_29 = x_348;
x_30 = x_353;
goto block_336;
}
else
{
uint8_t x_355; 
x_355 = lean_nat_dec_le(x_337, x_337);
if (x_355 == 0)
{
lean_dec(x_337);
lean_dec(x_10);
x_15 = x_338;
x_16 = x_339;
x_17 = x_340;
x_18 = x_341;
x_19 = x_342;
x_20 = x_350;
x_21 = x_343;
x_22 = x_352;
x_23 = x_347;
x_24 = x_349;
x_25 = x_351;
x_26 = x_344;
x_27 = x_345;
x_28 = x_346;
x_29 = x_348;
x_30 = x_353;
goto block_336;
}
else
{
size_t x_356; lean_object* x_357; 
x_356 = lean_usize_of_nat(x_337);
lean_dec(x_337);
x_357 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(x_10, x_14, x_348, x_356, x_353);
lean_dec(x_10);
x_15 = x_338;
x_16 = x_339;
x_17 = x_340;
x_18 = x_341;
x_19 = x_342;
x_20 = x_350;
x_21 = x_343;
x_22 = x_352;
x_23 = x_347;
x_24 = x_349;
x_25 = x_351;
x_26 = x_344;
x_27 = x_345;
x_28 = x_346;
x_29 = x_348;
x_30 = x_357;
goto block_336;
}
}
}
block_378:
{
size_t x_365; lean_object* x_366; size_t x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; uint8_t x_374; 
x_365 = lean_array_size(x_14);
x_366 = lean_unsigned_to_nat(0u);
x_367 = lean_usize_of_nat(x_366);
lean_inc(x_14);
x_368 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(x_10, x_359, x_365, x_367, x_14);
x_369 = lean_ctor_get(x_1, 0);
lean_inc(x_369);
x_370 = lean_mk_string_unchecked("_redArg", 7, 7);
x_371 = l_Lean_Name_mkStr1(x_370);
lean_inc(x_369);
x_372 = l_Lean_Name_append(x_369, x_371);
x_373 = lean_mk_empty_array_with_capacity(x_366);
x_374 = lean_nat_dec_lt(x_366, x_337);
if (x_374 == 0)
{
x_338 = x_362;
x_339 = x_372;
x_340 = x_366;
x_341 = x_368;
x_342 = x_363;
x_343 = x_359;
x_344 = x_364;
x_345 = x_365;
x_346 = x_360;
x_347 = x_361;
x_348 = x_367;
x_349 = x_369;
x_350 = x_373;
goto block_358;
}
else
{
uint8_t x_375; 
x_375 = lean_nat_dec_le(x_337, x_337);
if (x_375 == 0)
{
x_338 = x_362;
x_339 = x_372;
x_340 = x_366;
x_341 = x_368;
x_342 = x_363;
x_343 = x_359;
x_344 = x_364;
x_345 = x_365;
x_346 = x_360;
x_347 = x_361;
x_348 = x_367;
x_349 = x_369;
x_350 = x_373;
goto block_358;
}
else
{
size_t x_376; lean_object* x_377; 
x_376 = lean_usize_of_nat(x_337);
x_377 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(x_10, x_359, x_14, x_367, x_376, x_373);
x_338 = x_362;
x_339 = x_372;
x_340 = x_366;
x_341 = x_368;
x_342 = x_363;
x_343 = x_359;
x_344 = x_364;
x_345 = x_365;
x_346 = x_360;
x_347 = x_361;
x_348 = x_367;
x_349 = x_369;
x_350 = x_377;
goto block_358;
}
}
}
block_430:
{
if (x_379 == 0)
{
lean_object* x_380; lean_object* x_381; lean_object* x_382; lean_object* x_383; lean_object* x_384; uint8_t x_385; 
lean_dec(x_12);
x_380 = lean_mk_string_unchecked("Compiler", 8, 8);
x_381 = lean_mk_string_unchecked("reduceArity", 11, 11);
x_382 = l_Lean_Name_mkStr2(x_380, x_381);
lean_inc(x_382);
x_383 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___redArg(x_382, x_4, x_11);
x_384 = lean_ctor_get(x_383, 0);
lean_inc(x_384);
x_385 = lean_unbox(x_384);
lean_dec(x_384);
if (x_385 == 0)
{
lean_object* x_386; 
lean_dec(x_382);
x_386 = lean_ctor_get(x_383, 1);
lean_inc(x_386);
lean_dec(x_383);
x_359 = x_379;
x_360 = x_2;
x_361 = x_3;
x_362 = x_4;
x_363 = x_5;
x_364 = x_386;
goto block_378;
}
else
{
uint8_t x_387; 
x_387 = !lean_is_exclusive(x_383);
if (x_387 == 0)
{
lean_object* x_388; lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; lean_object* x_396; lean_object* x_397; lean_object* x_398; lean_object* x_399; lean_object* x_400; lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; 
x_388 = lean_ctor_get(x_383, 1);
x_389 = lean_ctor_get(x_383, 0);
lean_dec(x_389);
x_390 = lean_mk_string_unchecked("", 0, 0);
x_391 = l_Lean_stringToMessageData(x_390);
lean_dec(x_390);
x_392 = lean_ctor_get(x_1, 0);
lean_inc(x_392);
x_393 = l_Lean_MessageData_ofName(x_392);
lean_inc(x_391);
lean_ctor_set_tag(x_383, 7);
lean_ctor_set(x_383, 1, x_393);
lean_ctor_set(x_383, 0, x_391);
x_394 = lean_mk_string_unchecked(", used params: ", 15, 15);
x_395 = l_Lean_stringToMessageData(x_394);
lean_dec(x_394);
x_396 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_396, 0, x_383);
lean_ctor_set(x_396, 1, x_395);
x_397 = l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7(x_10);
x_398 = lean_box(0);
x_399 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(x_397, x_398);
x_400 = lean_box(0);
x_401 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10(x_399, x_400);
x_402 = l_Lean_MessageData_ofList(x_401);
x_403 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_403, 0, x_396);
lean_ctor_set(x_403, 1, x_402);
x_404 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_404, 0, x_403);
lean_ctor_set(x_404, 1, x_391);
x_405 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg(x_382, x_404, x_3, x_4, x_5, x_388);
x_406 = lean_ctor_get(x_405, 1);
lean_inc(x_406);
lean_dec(x_405);
x_359 = x_379;
x_360 = x_2;
x_361 = x_3;
x_362 = x_4;
x_363 = x_5;
x_364 = x_406;
goto block_378;
}
else
{
lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; lean_object* x_414; lean_object* x_415; lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; 
x_407 = lean_ctor_get(x_383, 1);
lean_inc(x_407);
lean_dec(x_383);
x_408 = lean_mk_string_unchecked("", 0, 0);
x_409 = l_Lean_stringToMessageData(x_408);
lean_dec(x_408);
x_410 = lean_ctor_get(x_1, 0);
lean_inc(x_410);
x_411 = l_Lean_MessageData_ofName(x_410);
lean_inc(x_409);
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_409);
lean_ctor_set(x_412, 1, x_411);
x_413 = lean_mk_string_unchecked(", used params: ", 15, 15);
x_414 = l_Lean_stringToMessageData(x_413);
lean_dec(x_413);
x_415 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_415, 0, x_412);
lean_ctor_set(x_415, 1, x_414);
x_416 = l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7(x_10);
x_417 = lean_box(0);
x_418 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__9(x_416, x_417);
x_419 = lean_box(0);
x_420 = l_List_mapTR_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__10(x_418, x_419);
x_421 = l_Lean_MessageData_ofList(x_420);
x_422 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_422, 0, x_415);
lean_ctor_set(x_422, 1, x_421);
x_423 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_423, 0, x_422);
lean_ctor_set(x_423, 1, x_409);
x_424 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg(x_382, x_423, x_3, x_4, x_5, x_407);
x_425 = lean_ctor_get(x_424, 1);
lean_inc(x_425);
lean_dec(x_424);
x_359 = x_379;
x_360 = x_2;
x_361 = x_3;
x_362 = x_4;
x_363 = x_5;
x_364 = x_425;
goto block_378;
}
}
}
else
{
lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_dec(x_337);
lean_dec(x_14);
lean_dec(x_10);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_426 = lean_unsigned_to_nat(1u);
x_427 = lean_mk_empty_array_with_capacity(x_426);
x_428 = lean_array_push(x_427, x_1);
if (lean_is_scalar(x_12)) {
 x_429 = lean_alloc_ctor(0, 2, 0);
} else {
 x_429 = x_12;
}
lean_ctor_set(x_429, 0, x_428);
lean_ctor_set(x_429, 1, x_11);
return x_429;
}
}
}
else
{
uint8_t x_434; 
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_434 = !lean_is_exclusive(x_9);
if (x_434 == 0)
{
return x_9;
}
else
{
lean_object* x_435; lean_object* x_436; lean_object* x_437; 
x_435 = lean_ctor_get(x_9, 0);
x_436 = lean_ctor_get(x_9, 1);
lean_inc(x_436);
lean_inc(x_435);
lean_dec(x_9);
x_437 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_437, 0, x_435);
lean_ctor_set(x_437, 1, x_436);
return x_437;
}
}
}
else
{
lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; 
lean_dec(x_7);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
x_438 = lean_unsigned_to_nat(1u);
x_439 = lean_mk_empty_array_with_capacity(x_438);
x_440 = lean_array_push(x_439, x_1);
x_441 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_441, 0, x_440);
lean_ctor_set(x_441, 1, x_6);
return x_441;
}
}
}
LEAN_EXPORT lean_object* l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; size_t x_7; size_t x_8; lean_object* x_9; 
x_6 = lean_unbox(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = l_Array_mapMUnsafe_map___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__0(x_1, x_6, x_7, x_8, x_5);
lean_dec(x_1);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_7 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_8 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___redArg(x_1, x_6, x_7, x_4, x_5);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
size_t x_11; size_t x_12; lean_object* x_13; 
x_11 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_12 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_13 = l_Array_forIn_x27Unsafe_loop___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__2(x_1, x_11, x_12, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_9);
lean_dec(x_8);
lean_dec(x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_1);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
size_t x_6; size_t x_7; lean_object* x_8; 
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_8 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__3(x_1, x_2, x_6, x_7, x_5);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4_spec__4(x_1, x_7, x_3, x_8, x_9, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; size_t x_8; size_t x_9; lean_object* x_10; 
x_7 = lean_unbox(x_2);
lean_dec(x_2);
x_8 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_9 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_10 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__4(x_1, x_7, x_3, x_8, x_9, x_6);
lean_dec(x_3);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___redArg(x_1, x_2, x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_isTracingEnabledFor___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__6(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7_spec__7___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_RBNode_revFold___at___Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7_spec__7(x_1, x_2);
lean_dec(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_RBTree_toList___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__7(x_1);
lean_dec(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___Lean_Compiler_LCNF_Decl_reduceArity_spec__11(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
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
x_19 = l_Lean_Compiler_LCNF_Decl_reduceArity(x_18, x_5, x_6, x_7, x_8, x_9);
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
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_mk_empty_array_with_capacity(x_1);
x_9 = lean_array_get_size(x_2);
x_10 = lean_nat_dec_lt(x_1, x_9);
if (x_10 == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_11 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_11, 0, x_8);
lean_ctor_set(x_11, 1, x_7);
return x_11;
}
else
{
uint8_t x_12; 
x_12 = lean_nat_dec_le(x_9, x_9);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_9);
lean_dec(x_6);
lean_dec(x_5);
lean_dec(x_4);
lean_dec(x_3);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_7);
return x_13;
}
else
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_usize_of_nat(x_1);
x_15 = lean_usize_of_nat(x_9);
lean_dec(x_9);
x_16 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(x_2, x_14, x_15, x_8, x_3, x_4, x_5, x_6, x_7);
return x_16;
}
}
}
}
static lean_object* _init_l_Lean_Compiler_LCNF_reduceArity() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; uint8_t x_8; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_alloc_closure((void*)(l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed), 7, 1);
lean_closure_set(x_2, 0, x_1);
x_3 = lean_box(1);
x_4 = lean_mk_string_unchecked("reduceArity", 11, 11);
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
LEAN_EXPORT lean_object* l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
size_t x_10; size_t x_11; lean_object* x_12; 
x_10 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_11 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_12 = l_Array_foldlMUnsafe_fold___at___Lean_Compiler_LCNF_reduceArity_spec__0(x_1, x_10, x_11, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_reduceArity___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Compiler_LCNF_reduceArity___lam__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_2);
lean_dec(x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2415_(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; uint8_t x_25; lean_object* x_26; 
x_2 = lean_mk_string_unchecked("Compiler", 8, 8);
x_3 = lean_mk_string_unchecked("reduceArity", 11, 11);
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
x_19 = lean_mk_string_unchecked("ReduceArity", 11, 11);
x_20 = l_Lean_Name_str___override(x_18, x_19);
x_21 = lean_mk_string_unchecked("_hyg", 4, 4);
x_22 = l_Lean_Name_str___override(x_20, x_21);
x_23 = lean_unsigned_to_nat(2415u);
x_24 = l_Lean_Name_num___override(x_22, x_23);
x_25 = lean_unbox(x_5);
x_26 = l_Lean_registerTraceClass(x_4, x_25, x_24, x_1);
return x_26;
}
}
lean_object* initialize_Lean_Compiler_LCNF_CompilerM(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_PhaseExt(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_InferType(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Compiler_LCNF_Internalize(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Compiler_LCNF_ReduceArity(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_LCNF_CompilerM(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_PhaseExt(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_InferType(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Compiler_LCNF_Internalize(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Compiler_LCNF_reduceArity = _init_l_Lean_Compiler_LCNF_reduceArity();
lean_mark_persistent(l_Lean_Compiler_LCNF_reduceArity);
if (builtin) {res = l_Lean_Compiler_LCNF_initFn____x40_Lean_Compiler_LCNF_ReduceArity___hyg_2415_(lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
